// Lean compiler output
// Module: Lean.Meta.Tactic.Congr
// Imports: public import Lean.Meta.CongrTheorems public import Lean.Meta.Tactic.Assert public import Lean.Meta.Tactic.Refl public import Lean.Meta.Tactic.Assumption
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
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_eqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_MVarId_heqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_hrefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "h_congr_thm"};
static const lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 191, 7, 90, 105, 148, 138, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_congr_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_congr_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_congr_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_congr_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_congr_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_MVarId_congr_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_congr_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_congr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_Lean_MVarId_congr_x3f___closed__0 = (const lean_object*)&l_Lean_MVarId_congr_x3f___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_congr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_congr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l_Lean_MVarId_congr_x3f___closed__1 = (const lean_object*)&l_Lean_MVarId_congr_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_MVarId_hcongr_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_hcongr_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_MVarId_hcongr_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_hcongr_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Internal error: Expected at least two goals after applying `"};
static const lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1;
static const lean_string_object l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`, but unexpectedly found fewer"};
static const lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3;
static const lean_ctor_object l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_congrImplies_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "implies_congr"};
static const lean_object* l_Lean_MVarId_congrImplies_x3f___closed__0 = (const lean_object*)&l_Lean_MVarId_congrImplies_x3f___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_congrImplies_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_congrImplies_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 71, 54, 187, 9, 73, 178, 153)}};
static const lean_object* l_Lean_MVarId_congrImplies_x3f___closed__1 = (const lean_object*)&l_Lean_MVarId_congrImplies_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_congrCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Failed to apply congruence"};
static const lean_object* l_Lean_MVarId_congrCore___closed__0 = (const lean_object*)&l_Lean_MVarId_congrCore___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_congrCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_congrCore___closed__0_value)}};
static const lean_object* l_Lean_MVarId_congrCore___closed__1 = (const lean_object*)&l_Lean_MVarId_congrCore___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_congrCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_congrCore___closed__2;
static lean_once_cell_t l_Lean_MVarId_congrCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_congrCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_congrCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_MVarId_congrN___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_congrN___closed__0 = (const lean_object*)&l_Lean_MVarId_congrN___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_congrPre(lean_object* v_mvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_MVarId_heqOfEq(v_mvarId_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_77_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_77_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_77_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_77_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___y_13_; uint8_t v___y_14_; uint8_t v___x_41_; lean_object* v___x_42_; 
v___x_41_ = 1;
lean_inc(v_a_8_);
v___x_42_ = l_Lean_MVarId_refl(v_a_8_, v___x_41_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_50_; 
lean_del_object(v___x_10_);
lean_dec(v_a_8_);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; 
v_unused_51_ = lean_ctor_get(v___x_42_, 0);
lean_dec(v_unused_51_);
v___x_44_ = v___x_42_;
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
else
{
lean_dec(v___x_42_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_46_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
else
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_76_; 
v_a_52_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_76_ == 0)
{
v___x_54_ = v___x_42_;
v_isShared_55_ = v_isSharedCheck_76_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_42_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_76_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
uint8_t v___y_57_; uint8_t v___x_74_; 
v___x_74_ = l_Lean_Exception_isInterrupt(v_a_52_);
if (v___x_74_ == 0)
{
uint8_t v___x_75_; 
lean_inc(v_a_52_);
v___x_75_ = l_Lean_Exception_isRuntime(v_a_52_);
v___y_57_ = v___x_75_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___x_74_;
goto v___jp_56_;
}
v___jp_56_:
{
if (v___y_57_ == 0)
{
lean_object* v___x_58_; 
lean_del_object(v___x_54_);
lean_dec(v_a_52_);
lean_inc(v_a_8_);
v___x_58_ = l_Lean_MVarId_hrefl(v_a_8_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_66_; 
lean_del_object(v___x_10_);
lean_dec(v_a_8_);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v___x_58_, 0);
lean_dec(v_unused_67_);
v___x_60_ = v___x_58_;
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
else
{
lean_dec(v___x_58_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_62_);
v___x_64_ = v___x_60_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
else
{
lean_object* v_a_68_; uint8_t v___x_69_; 
v_a_68_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_58_, 1);
v___x_69_ = l_Lean_Exception_isInterrupt(v_a_68_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; 
lean_inc(v_a_68_);
v___x_70_ = l_Lean_Exception_isRuntime(v_a_68_);
v___y_13_ = v_a_68_;
v___y_14_ = v___x_70_;
goto v___jp_12_;
}
else
{
v___y_13_ = v_a_68_;
v___y_14_ = v___x_69_;
goto v___jp_12_;
}
}
}
else
{
lean_object* v___x_72_; 
lean_del_object(v___x_10_);
lean_dec(v_a_8_);
if (v_isShared_55_ == 0)
{
v___x_72_ = v___x_54_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_52_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
v___jp_12_:
{
if (v___y_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec_ref(v___y_13_);
lean_del_object(v___x_10_);
lean_inc(v_a_8_);
v___x_15_ = l_Lean_MVarId_assumptionCore(v_a_8_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_29_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_29_ == 0)
{
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_29_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_29_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
uint8_t v___x_20_; 
v___x_20_ = lean_unbox(v_a_16_);
lean_dec(v_a_16_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_a_8_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_21_);
v___x_23_ = v___x_18_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
else
{
lean_object* v___x_25_; lean_object* v___x_27_; 
lean_dec(v_a_8_);
v___x_25_ = lean_box(0);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_25_);
v___x_27_ = v___x_18_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
lean_dec(v_a_8_);
v_a_30_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_15_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_15_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
else
{
lean_object* v___x_39_; 
lean_dec(v_a_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set_tag(v___x_10_, 1);
lean_ctor_set(v___x_10_, 0, v___y_13_);
v___x_39_ = v___x_10_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___y_13_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_a_78_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_7_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_7_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_congrPre_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lean_MVarId_congrPre(v_mvarId_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrPre___boxed(lean_object* v_mvarId_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_MVarId_congrPre(v_mvarId_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_93_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(lean_object* v_fst_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v_fst_94_);
v___x_102_ = l_List_reverse___redArg(v_x_96_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
else
{
lean_object* v_head_104_; lean_object* v_tail_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_123_; 
v_head_104_ = lean_ctor_get(v_x_95_, 0);
v_tail_105_ = lean_ctor_get(v_x_95_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_95_);
if (v_isSharedCheck_123_ == 0)
{
v___x_107_ = v_x_95_;
v_isShared_108_ = v_isSharedCheck_123_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_tail_105_);
lean_inc(v_head_104_);
lean_dec(v_x_95_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_123_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; 
lean_inc(v_fst_94_);
v___x_109_ = l_Lean_MVarId_tryClear(v_head_104_, v_fst_94_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v___x_109_, 1);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v_x_96_);
lean_ctor_set(v___x_107_, 0, v_a_110_);
v___x_112_ = v___x_107_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_110_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_x_96_);
v___x_112_ = v_reuseFailAlloc_114_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
v_x_95_ = v_tail_105_;
v_x_96_ = v___x_112_;
goto _start;
}
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_del_object(v___x_107_);
lean_dec(v_tail_105_);
lean_dec(v_x_96_);
lean_dec(v_fst_94_);
v_a_115_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_109_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_109_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_94_ = stack[0].m_obj;
lean_object* v_x_95_ = stack[1].m_obj;
lean_object* v_x_96_ = stack[2].m_obj;
lean_object* v___y_97_ = stack[3].m_obj;
lean_object* v___y_98_ = stack[4].m_obj;
lean_object* v___y_99_ = stack[5].m_obj;
lean_object* v___y_100_ = stack[6].m_obj;
lean_object* v_res_124_;
v_res_124_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_94_, v_x_95_, v_x_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
stack->m_obj
 = v_res_124_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0___boxed(lean_object* v_fst_125_, lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_125_, v_x_126_, v_x_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_133_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(lean_object* v_mvarId_141_, lean_object* v_congrThm_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1));
v___x_149_ = l_Lean_Core_mkFreshUserName(v___x_148_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v_type_151_; lean_object* v_proof_152_; lean_object* v___x_153_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_a_150_);
lean_dec_ref_known(v___x_149_, 1);
v_type_151_ = lean_ctor_get(v_congrThm_142_, 0);
lean_inc_ref(v_type_151_);
v_proof_152_ = lean_ctor_get(v_congrThm_142_, 1);
lean_inc_ref(v_proof_152_);
lean_dec_ref(v_congrThm_142_);
v___x_153_ = l_Lean_MVarId_assert(v_mvarId_141_, v_a_150_, v_type_151_, v_proof_152_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; uint8_t v___x_155_; lean_object* v___x_156_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = 1;
v___x_156_ = l_Lean_Meta_intro1Core(v_a_154_, v___x_155_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v_fst_158_; lean_object* v_snd_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v_fst_158_ = lean_ctor_get(v_a_157_, 0);
lean_inc_n(v_fst_158_, 2);
v_snd_159_ = lean_ctor_get(v_a_157_, 1);
lean_inc(v_snd_159_);
lean_dec(v_a_157_);
v___x_160_ = l_Lean_mkFVar(v_fst_158_);
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2));
v___x_162_ = lean_box(0);
v___x_163_ = l_Lean_MVarId_apply(v_snd_159_, v___x_160_, v___x_161_, v___x_162_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
v___x_165_ = lean_box(0);
v___x_166_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_158_, v_a_164_, v___x_165_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
return v___x_166_;
}
else
{
lean_dec(v_fst_158_);
return v___x_163_;
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_156_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_156_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_a_175_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_153_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_153_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v_congrThm_142_);
lean_dec(v_mvarId_141_);
v_a_183_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_149_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_149_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_141_ = stack[0].m_obj;
lean_object* v_congrThm_142_ = stack[1].m_obj;
lean_object* v_a_143_ = stack[2].m_obj;
lean_object* v_a_144_ = stack[3].m_obj;
lean_object* v_a_145_ = stack[4].m_obj;
lean_object* v_a_146_ = stack[5].m_obj;
lean_object* v_res_191_;
v_res_191_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(v_mvarId_141_, v_congrThm_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___boxed(lean_object* v_mvarId_192_, lean_object* v_congrThm_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(v_mvarId_192_, v_congrThm_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_199_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(lean_object* v_mvarId_200_, lean_object* v_x_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_200_, v_x_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_207_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_207_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_200_ = stack[0].m_obj;
lean_object* v_x_201_ = stack[1].m_obj;
lean_object* v___y_202_ = stack[2].m_obj;
lean_object* v___y_203_ = stack[3].m_obj;
lean_object* v___y_204_ = stack[4].m_obj;
lean_object* v___y_205_ = stack[5].m_obj;
lean_object* v_res_224_;
v_res_224_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_mvarId_200_, v_x_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_225_, lean_object* v_x_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_mvarId_225_, v_x_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_232_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(lean_object* v_00_u03b1_233_, lean_object* v_mvarId_234_, lean_object* v_x_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_mvarId_234_, v_x_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
return v___x_241_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_234_ = stack[1].m_obj;
lean_object* v_x_235_ = stack[2].m_obj;
lean_object* v___y_236_ = stack[3].m_obj;
lean_object* v___y_237_ = stack[4].m_obj;
lean_object* v___y_238_ = stack[5].m_obj;
lean_object* v___y_239_ = stack[6].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(lean_box(0), v_mvarId_234_, v_x_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___boxed(lean_object* v_00_u03b1_243_, lean_object* v_mvarId_244_, lean_object* v_x_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(v_00_u03b1_243_, v_mvarId_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_251_;
}
}
lean_object* l_Lean_MVarId_congr_x3f___lam__0(lean_object* v_mvarId_255_, lean_object* v___x_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
lean_inc(v_mvarId_255_);
v___x_262_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_255_, v___x_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; 
lean_dec_ref_known(v___x_262_, 1);
lean_inc(v_mvarId_255_);
v___x_263_ = l_Lean_MVarId_getType_x27(v_mvarId_255_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_330_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_330_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_330_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_330_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lean_MVarId_congr_x3f___lam__0___closed__1));
v___x_269_ = lean_unsigned_to_nat(3u);
v___x_270_ = l_Lean_Expr_isAppOfArity(v_a_264_, v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec(v_a_264_);
lean_dec(v_mvarId_255_);
v___x_271_ = lean_box(0);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_271_);
v___x_273_ = v___x_266_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_275_ = l_Lean_Expr_appFn_x21(v_a_264_);
lean_dec(v_a_264_);
v___x_276_ = l_Lean_Expr_appArg_x21(v___x_275_);
lean_dec_ref(v___x_275_);
v___x_277_ = l_Lean_Expr_cleanupAnnotations(v___x_276_);
v___x_278_ = l_Lean_Expr_isApp(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec_ref(v___x_277_);
lean_dec(v_mvarId_255_);
v___x_279_ = lean_box(0);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_279_);
v___x_281_ = v___x_266_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_del_object(v___x_266_);
v___x_283_ = l_Lean_Expr_getAppFn(v___x_277_);
v___x_284_ = 0;
v___x_285_ = l_Lean_Expr_getAppNumArgs(v___x_277_);
lean_dec_ref(v___x_277_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = l_Lean_Meta_mkCongrSimp_x3f(v___x_283_, v___x_284_, v___x_286_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_321_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_321_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_321_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_321_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
if (lean_obj_tag(v_a_288_) == 1)
{
lean_object* v_val_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_316_; 
lean_del_object(v___x_290_);
v_val_292_ = lean_ctor_get(v_a_288_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v_a_288_);
if (v_isSharedCheck_316_ == 0)
{
v___x_294_ = v_a_288_;
v_isShared_295_ = v_isSharedCheck_316_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_val_292_);
lean_dec(v_a_288_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_316_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(v_mvarId_255_, v_val_292_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_307_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_307_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v_a_297_);
v___x_302_ = v___x_294_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_del_object(v___x_294_);
v_a_308_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_296_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_296_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v___x_317_; lean_object* v___x_319_; 
lean_dec(v_a_288_);
lean_dec(v_mvarId_255_);
v___x_317_ = lean_box(0);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_317_);
v___x_319_ = v___x_290_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_mvarId_255_);
v_a_322_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_287_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_287_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_mvarId_255_);
v_a_331_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_263_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_263_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_mvarId_255_);
v_a_339_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_262_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_262_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_congr_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_255_ = stack[0].m_obj;
lean_object* v___x_256_ = stack[1].m_obj;
lean_object* v___y_257_ = stack[2].m_obj;
lean_object* v___y_258_ = stack[3].m_obj;
lean_object* v___y_259_ = stack[4].m_obj;
lean_object* v___y_260_ = stack[5].m_obj;
lean_object* v_res_347_;
v_res_347_ = l_Lean_MVarId_congr_x3f___lam__0(v_mvarId_255_, v___x_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___lam__0___boxed(lean_object* v_mvarId_348_, lean_object* v___x_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_MVarId_congr_x3f___lam__0(v_mvarId_348_, v___x_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_355_;
}
}
lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(lean_object* v_x_x3f_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_saveState___redArg(v___y_358_, v___y_360_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_407_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_407_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_407_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_407_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___y_368_; uint8_t v___y_369_; lean_object* v_a_391_; lean_object* v___x_394_; 
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
v___x_394_ = lean_apply_5(v_x_x3f_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, lean_box(0));
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
if (lean_obj_tag(v_a_395_) == 0)
{
lean_object* v___x_396_; 
lean_dec_ref_known(v___x_394_, 1);
lean_inc(v_a_363_);
v___x_396_ = l_Lean_Meta_SavedState_restore___redArg(v_a_363_, v___y_358_, v___y_360_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_del_object(v___x_365_);
lean_dec(v_a_363_);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_396_, 0);
lean_dec(v_unused_404_);
v___x_398_ = v___x_396_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_dec(v___x_396_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v_a_395_);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_395_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v_a_405_; 
v_a_405_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_396_, 1);
v_a_391_ = v_a_405_;
goto v___jp_390_;
}
}
else
{
lean_dec_ref_known(v_a_395_, 1);
lean_del_object(v___x_365_);
lean_dec(v_a_363_);
return v___x_394_;
}
}
else
{
lean_object* v_a_406_; 
v_a_406_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_394_, 1);
v_a_391_ = v_a_406_;
goto v___jp_390_;
}
v___jp_367_:
{
if (v___y_369_ == 0)
{
lean_object* v___x_370_; 
lean_del_object(v___x_365_);
v___x_370_ = l_Lean_Meta_SavedState_restore___redArg(v_a_363_, v___y_358_, v___y_360_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_378_);
v___x_372_ = v___x_370_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_370_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 1);
lean_ctor_set(v___x_372_, 0, v___y_368_);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___y_368_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec_ref(v___y_368_);
v_a_379_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_370_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_370_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v___x_388_; 
lean_dec(v_a_363_);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 1);
lean_ctor_set(v___x_365_, 0, v___y_368_);
v___x_388_ = v___x_365_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___y_368_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
v___jp_390_:
{
uint8_t v___x_392_; 
v___x_392_ = l_Lean_Exception_isInterrupt(v_a_391_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
lean_inc_ref(v_a_391_);
v___x_393_ = l_Lean_Exception_isRuntime(v_a_391_);
v___y_368_ = v_a_391_;
v___y_369_ = v___x_393_;
goto v___jp_367_;
}
else
{
v___y_368_ = v_a_391_;
v___y_369_ = v___x_392_;
goto v___jp_367_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_x_x3f_356_);
v_a_408_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_362_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_362_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_x3f_356_ = stack[0].m_obj;
lean_object* v___y_357_ = stack[1].m_obj;
lean_object* v___y_358_ = stack[2].m_obj;
lean_object* v___y_359_ = stack[3].m_obj;
lean_object* v___y_360_ = stack[4].m_obj;
lean_object* v_res_416_;
v_res_416_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_x3f_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(lean_object* v_x_x3f_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_430_) == 0)
{
return v___x_430_;
}
else
{
lean_object* v_a_431_; uint8_t v___y_433_; uint8_t v___x_443_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v___x_443_ = l_Lean_Exception_isInterrupt(v_a_431_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; 
lean_inc(v_a_431_);
v___x_444_ = l_Lean_Exception_isRuntime(v_a_431_);
v___y_433_ = v___x_444_;
goto v___jp_432_;
}
else
{
v___y_433_ = v___x_443_;
goto v___jp_432_;
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_430_, 0);
lean_dec(v_unused_442_);
v___x_435_ = v___x_430_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_dec(v___x_430_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_box(0);
if (v_isShared_436_ == 0)
{
lean_ctor_set_tag(v___x_435_, 0);
lean_ctor_set(v___x_435_, 0, v___x_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
return v___x_430_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_x3f_424_ = stack[0].m_obj;
lean_object* v___y_425_ = stack[1].m_obj;
lean_object* v___y_426_ = stack[2].m_obj;
lean_object* v___y_427_ = stack[3].m_obj;
lean_object* v___y_428_ = stack[4].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(v_x_x3f_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(v_x_x3f_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_452_;
}
}
lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(lean_object* v_00_u03b1_453_, lean_object* v_x_x3f_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(v_x_x3f_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
return v___x_460_;
}
}
LEAN_EXPORT void l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_x3f_454_ = stack[1].m_obj;
lean_object* v___y_455_ = stack[2].m_obj;
lean_object* v___y_456_ = stack[3].m_obj;
lean_object* v___y_457_ = stack[4].m_obj;
lean_object* v___y_458_ = stack[5].m_obj;
lean_object* v_res_461_;
v_res_461_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(lean_box(0), v_x_x3f_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___boxed(lean_object* v_00_u03b1_462_, lean_object* v_x_x3f_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(v_00_u03b1_462_, v_x_x3f_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_469_;
}
}
lean_object* l_Lean_MVarId_congr_x3f(lean_object* v_mvarId_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_479_ = ((lean_object*)(l_Lean_MVarId_congr_x3f___closed__1));
lean_inc(v_mvarId_473_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_MVarId_congr_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_480_, 0, v_mvarId_473_);
lean_closure_set(v___f_480_, 1, v___x_479_);
v___x_481_ = lean_alloc_closure((void*)(l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___boxed), 7, 2);
lean_closure_set(v___x_481_, 0, lean_box(0));
lean_closure_set(v___x_481_, 1, v___f_480_);
v___x_482_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_mvarId_473_, v___x_481_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_482_;
}
}
LEAN_EXPORT void l_Lean_MVarId_congr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_473_ = stack[0].m_obj;
lean_object* v_a_474_ = stack[1].m_obj;
lean_object* v_a_475_ = stack[2].m_obj;
lean_object* v_a_476_ = stack[3].m_obj;
lean_object* v_a_477_ = stack[4].m_obj;
lean_object* v_res_483_;
v_res_483_ = l_Lean_MVarId_congr_x3f(v_mvarId_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___boxed(lean_object* v_mvarId_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_MVarId_congr_x3f(v_mvarId_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
return v_res_490_;
}
}
lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(lean_object* v_00_u03b1_491_, lean_object* v_x_x3f_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_498_;
}
}
LEAN_EXPORT void l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_x3f_492_ = stack[1].m_obj;
lean_object* v___y_493_ = stack[2].m_obj;
lean_object* v___y_494_ = stack[3].m_obj;
lean_object* v___y_495_ = stack[4].m_obj;
lean_object* v___y_496_ = stack[5].m_obj;
lean_object* v_res_499_;
v_res_499_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(lean_box(0), v_x_x3f_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_500_, lean_object* v_x_x3f_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(v_00_u03b1_500_, v_x_x3f_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_507_;
}
}
lean_object* l_Lean_MVarId_hcongr_x3f___lam__0(lean_object* v_a_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; 
lean_inc(v_a_511_);
v___x_517_ = l_Lean_MVarId_getType_x27(v_a_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_568_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_568_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_568_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_568_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = ((lean_object*)(l_Lean_MVarId_hcongr_x3f___lam__0___closed__1));
v___x_523_ = lean_unsigned_to_nat(4u);
v___x_524_ = l_Lean_Expr_isAppOfArity(v_a_518_, v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec(v_a_518_);
lean_dec(v_a_511_);
v___x_525_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_525_);
v___x_527_ = v___x_520_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_529_ = l_Lean_Expr_appFn_x21(v_a_518_);
lean_dec(v_a_518_);
v___x_530_ = l_Lean_Expr_appFn_x21(v___x_529_);
lean_dec_ref(v___x_529_);
v___x_531_ = l_Lean_Expr_appArg_x21(v___x_530_);
lean_dec_ref(v___x_530_);
v___x_532_ = l_Lean_Expr_cleanupAnnotations(v___x_531_);
v___x_533_ = l_Lean_Expr_isApp(v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec_ref(v___x_532_);
lean_dec(v_a_511_);
v___x_534_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_534_);
v___x_536_ = v___x_520_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_del_object(v___x_520_);
v___x_538_ = l_Lean_Expr_getAppFn(v___x_532_);
v___x_539_ = l_Lean_Expr_getAppNumArgs(v___x_532_);
lean_dec_ref(v___x_532_);
v___x_540_ = l_Lean_Meta_mkHCongrWithArity(v___x_538_, v___x_539_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(v_a_511_, v_a_541_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v_a_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_a_552_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_542_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_542_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_a_511_);
v_a_560_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_540_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_540_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_a_511_);
v_a_569_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_517_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_517_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_hcongr_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_511_ = stack[0].m_obj;
lean_object* v___y_512_ = stack[1].m_obj;
lean_object* v___y_513_ = stack[2].m_obj;
lean_object* v___y_514_ = stack[3].m_obj;
lean_object* v___y_515_ = stack[4].m_obj;
lean_object* v_res_577_;
v_res_577_ = l_Lean_MVarId_hcongr_x3f___lam__0(v_a_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__0___boxed(lean_object* v_a_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_MVarId_hcongr_x3f___lam__0(v_a_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_584_;
}
}
lean_object* l_Lean_MVarId_hcongr_x3f___lam__1(lean_object* v_mvarId_585_, lean_object* v___x_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
lean_inc(v_mvarId_585_);
v___x_592_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_585_, v___x_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_593_; 
lean_dec_ref_known(v___x_592_, 1);
v___x_593_ = l_Lean_MVarId_eqOfHEq(v_mvarId_585_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___f_595_; lean_object* v___x_596_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc_n(v_a_594_, 2);
lean_dec_ref_known(v___x_593_, 1);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_MVarId_hcongr_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_595_, 0, v_a_594_);
v___x_596_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_a_594_, v___f_595_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
return v___x_596_;
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_a_597_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_593_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec(v_mvarId_585_);
v_a_605_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_592_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_592_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_hcongr_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_585_ = stack[0].m_obj;
lean_object* v___x_586_ = stack[1].m_obj;
lean_object* v___y_587_ = stack[2].m_obj;
lean_object* v___y_588_ = stack[3].m_obj;
lean_object* v___y_589_ = stack[4].m_obj;
lean_object* v___y_590_ = stack[5].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lean_MVarId_hcongr_x3f___lam__1(v_mvarId_585_, v___x_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__1___boxed(lean_object* v_mvarId_614_, lean_object* v___x_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_MVarId_hcongr_x3f___lam__1(v_mvarId_614_, v___x_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
lean_object* l_Lean_MVarId_hcongr_x3f(lean_object* v_mvarId_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; lean_object* v___f_629_; lean_object* v___x_630_; 
v___x_628_ = ((lean_object*)(l_Lean_MVarId_congr_x3f___closed__1));
v___f_629_ = lean_alloc_closure((void*)(l_Lean_MVarId_hcongr_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_629_, 0, v_mvarId_622_);
lean_closure_set(v___f_629_, 1, v___x_628_);
v___x_630_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(v___f_629_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
return v___x_630_;
}
}
LEAN_EXPORT void l_Lean_MVarId_hcongr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_622_ = stack[0].m_obj;
lean_object* v_a_623_ = stack[1].m_obj;
lean_object* v_a_624_ = stack[2].m_obj;
lean_object* v_a_625_ = stack[3].m_obj;
lean_object* v_a_626_ = stack[4].m_obj;
lean_object* v_res_631_;
v_res_631_ = l_Lean_MVarId_hcongr_x3f(v_mvarId_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
stack->m_obj
 = v_res_631_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___boxed(lean_object* v_mvarId_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_MVarId_hcongr_x3f(v_mvarId_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
return v_res_638_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(lean_object* v_x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_saveState___redArg(v___y_641_, v___y_643_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
v___x_647_ = lean_apply_5(v_x_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, lean_box(0));
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_646_);
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_656_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_652_, 0, v_a_648_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_686_; 
v_a_657_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_686_ == 0)
{
v___x_659_ = v___x_647_;
v_isShared_660_ = v_isSharedCheck_686_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_647_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_686_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
uint8_t v___y_662_; uint8_t v___x_684_; 
v___x_684_ = l_Lean_Exception_isInterrupt(v_a_657_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; 
lean_inc(v_a_657_);
v___x_685_ = l_Lean_Exception_isRuntime(v_a_657_);
v___y_662_ = v___x_685_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___x_684_;
goto v___jp_661_;
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_object* v___x_663_; 
lean_del_object(v___x_659_);
lean_dec(v_a_657_);
v___x_663_ = l_Lean_Meta_SavedState_restore___redArg(v_a_646_, v___y_641_, v___y_643_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v___x_663_, 0);
lean_dec(v_unused_672_);
v___x_665_ = v___x_663_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_dec(v___x_663_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
v_a_673_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_663_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_663_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v___x_682_; 
lean_dec(v_a_646_);
if (v_isShared_660_ == 0)
{
v___x_682_ = v___x_659_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_657_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_x_639_);
v_a_687_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_645_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_645_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_639_ = stack[0].m_obj;
lean_object* v___y_640_ = stack[1].m_obj;
lean_object* v___y_641_ = stack[2].m_obj;
lean_object* v___y_642_ = stack[3].m_obj;
lean_object* v___y_643_ = stack[4].m_obj;
lean_object* v_res_695_;
v_res_695_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v_x_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
stack->m_obj
 = v_res_695_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg___boxed(lean_object* v_x_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v_x_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_702_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(lean_object* v_00_u03b1_703_, lean_object* v_x_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v_x_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_710_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_704_ = stack[1].m_obj;
lean_object* v___y_705_ = stack[2].m_obj;
lean_object* v___y_706_ = stack[3].m_obj;
lean_object* v___y_707_ = stack[4].m_obj;
lean_object* v___y_708_ = stack[5].m_obj;
lean_object* v_res_711_;
v_res_711_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(lean_box(0), v_x_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___boxed(lean_object* v_00_u03b1_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(v_00_u03b1_712_, v_x_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_719_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(lean_object* v_msgData_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; lean_object* v_env_727_; uint8_t v___x_728_; lean_object* v_env_729_; lean_object* v___x_730_; lean_object* v_toCold_731_; lean_object* v_mctx_732_; lean_object* v_lctx_733_; lean_object* v_options_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_726_ = lean_st_ref_get(v___y_724_);
v_env_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_env_727_);
lean_dec(v___x_726_);
v___x_728_ = 0;
v_env_729_ = l_Lean_Environment_setRecordingDeps(v_env_727_, v___x_728_);
v___x_730_ = lean_st_ref_get(v___y_722_);
v_toCold_731_ = lean_ctor_get(v___y_723_, 0);
v_mctx_732_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_mctx_732_);
lean_dec(v___x_730_);
v_lctx_733_ = lean_ctor_get(v___y_721_, 2);
v_options_734_ = lean_ctor_get(v_toCold_731_, 2);
lean_inc_ref(v_options_734_);
lean_inc_ref(v_lctx_733_);
v___x_735_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_735_, 0, v_env_729_);
lean_ctor_set(v___x_735_, 1, v_mctx_732_);
lean_ctor_set(v___x_735_, 2, v_lctx_733_);
lean_ctor_set(v___x_735_, 3, v_options_734_);
v___x_736_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v_msgData_720_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_720_ = stack[0].m_obj;
lean_object* v___y_721_ = stack[1].m_obj;
lean_object* v___y_722_ = stack[2].m_obj;
lean_object* v___y_723_ = stack[3].m_obj;
lean_object* v___y_724_ = stack[4].m_obj;
lean_object* v_res_738_;
v_res_738_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msgData_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msgData_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_745_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(lean_object* v_msg_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_ref_752_; lean_object* v___x_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_ref_752_ = lean_ctor_get(v___y_749_, 2);
v___x_753_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msg_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_inc(v_ref_752_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_ref_752_);
lean_ctor_set(v___x_758_, 1, v_a_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 1);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_746_ = stack[0].m_obj;
lean_object* v___y_747_ = stack[1].m_obj;
lean_object* v___y_748_ = stack[2].m_obj;
lean_object* v___y_749_ = stack[3].m_obj;
lean_object* v___y_750_ = stack[4].m_obj;
lean_object* v_res_763_;
v_res_763_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(v_msg_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
stack->m_obj
 = v_res_763_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg___boxed(lean_object* v_msg_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(v_msg_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_770_;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0(lean_object* v___x_781_, lean_object* v_mvarId_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
lean_inc(v___x_781_);
v___x_788_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_781_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; uint8_t v___x_790_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = 0;
v___x_802_ = ((lean_object*)(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4));
v___x_803_ = lean_box(0);
v___x_804_ = l_Lean_MVarId_apply(v_mvarId_782_, v_a_789_, v___x_802_, v___x_803_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_832_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_832_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_832_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_832_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
if (lean_obj_tag(v_a_805_) == 1)
{
lean_object* v_tail_809_; 
v_tail_809_ = lean_ctor_get(v_a_805_, 1);
lean_inc(v_tail_809_);
if (lean_obj_tag(v_tail_809_) == 1)
{
lean_object* v_head_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_830_; 
lean_dec(v___x_781_);
v_head_810_ = lean_ctor_get(v_a_805_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v_a_805_, 1);
lean_dec(v_unused_831_);
v___x_812_ = v_a_805_;
v_isShared_813_ = v_isSharedCheck_830_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_head_810_);
lean_dec(v_a_805_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_830_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_head_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_828_; 
v_head_814_ = lean_ctor_get(v_tail_809_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v_tail_809_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_tail_809_, 1);
lean_dec(v_unused_829_);
v___x_816_ = v_tail_809_;
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_head_814_);
lean_dec(v_tail_809_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_box(0);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_head_814_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_818_);
v___x_820_ = v_reuseFailAlloc_827_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_822_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v___x_820_);
v___x_822_ = v___x_812_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_head_810_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_822_);
v___x_824_ = v___x_807_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
else
{
lean_dec(v_tail_809_);
lean_dec_ref_known(v_a_805_, 2);
lean_del_object(v___x_807_);
v___y_792_ = v___y_783_;
v___y_793_ = v___y_784_;
v___y_794_ = v___y_785_;
v___y_795_ = v___y_786_;
goto v___jp_791_;
}
}
else
{
lean_del_object(v___x_807_);
lean_dec(v_a_805_);
v___y_792_ = v___y_783_;
v___y_793_ = v___y_784_;
v___y_794_ = v___y_785_;
v___y_795_ = v___y_786_;
goto v___jp_791_;
}
}
}
else
{
lean_dec(v___x_781_);
return v___x_804_;
}
v___jp_791_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_796_ = lean_obj_once(&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1, &l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1_once, _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1);
v___x_797_ = l_Lean_MessageData_ofConstName(v___x_781_, v___x_790_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_obj_once(&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3, &l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3_once, _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(v___x_800_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
return v___x_801_;
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_mvarId_782_);
lean_dec(v___x_781_);
v_a_833_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_788_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_788_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_congrImplies_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_781_ = stack[0].m_obj;
lean_object* v_mvarId_782_ = stack[1].m_obj;
lean_object* v___y_783_ = stack[2].m_obj;
lean_object* v___y_784_ = stack[3].m_obj;
lean_object* v___y_785_ = stack[4].m_obj;
lean_object* v___y_786_ = stack[5].m_obj;
lean_object* v_res_841_;
v_res_841_ = l_Lean_MVarId_congrImplies_x3f___lam__0(v___x_781_, v_mvarId_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
stack->m_obj
 = v_res_841_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___boxed(lean_object* v___x_842_, lean_object* v_mvarId_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_MVarId_congrImplies_x3f___lam__0(v___x_842_, v_mvarId_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
lean_object* l_Lean_MVarId_congrImplies_x3f(lean_object* v_mvarId_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_859_; lean_object* v___f_860_; lean_object* v___x_861_; 
v___x_859_ = ((lean_object*)(l_Lean_MVarId_congrImplies_x3f___closed__1));
v___f_860_ = lean_alloc_closure((void*)(l_Lean_MVarId_congrImplies_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_860_, 0, v___x_859_);
lean_closure_set(v___f_860_, 1, v_mvarId_853_);
v___x_861_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v___f_860_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
return v___x_861_;
}
}
LEAN_EXPORT void l_Lean_MVarId_congrImplies_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_853_ = stack[0].m_obj;
lean_object* v_a_854_ = stack[1].m_obj;
lean_object* v_a_855_ = stack[2].m_obj;
lean_object* v_a_856_ = stack[3].m_obj;
lean_object* v_a_857_ = stack[4].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_Lean_MVarId_congrImplies_x3f(v_mvarId_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___boxed(lean_object* v_mvarId_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_MVarId_congrImplies_x3f(v_mvarId_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_869_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(lean_object* v_00_u03b1_870_, lean_object* v_msg_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(v_msg_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_877_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_871_ = stack[1].m_obj;
lean_object* v___y_872_ = stack[2].m_obj;
lean_object* v___y_873_ = stack[3].m_obj;
lean_object* v___y_874_ = stack[4].m_obj;
lean_object* v___y_875_ = stack[5].m_obj;
lean_object* v_res_878_;
v_res_878_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(lean_box(0), v_msg_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
stack->m_obj
 = v_res_878_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___boxed(lean_object* v_00_u03b1_879_, lean_object* v_msg_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(v_00_u03b1_879_, v_msg_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_MVarId_congrCore___closed__2(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_MVarId_congrCore___closed__1));
v___x_891_ = l_Lean_MessageData_ofFormat(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_MVarId_congrCore___closed__3(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_obj_once(&l_Lean_MVarId_congrCore___closed__2, &l_Lean_MVarId_congrCore___closed__2_once, _init_l_Lean_MVarId_congrCore___closed__2);
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
lean_object* l_Lean_MVarId_congrCore(lean_object* v_mvarId_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; 
lean_inc(v_mvarId_894_);
v___x_900_ = l_Lean_MVarId_congr_x3f(v_mvarId_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_948_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_948_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_948_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_948_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
if (lean_obj_tag(v_a_901_) == 1)
{
lean_object* v_val_905_; lean_object* v___x_907_; 
lean_dec(v_mvarId_894_);
v_val_905_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v_a_901_, 1);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v_val_905_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_val_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
else
{
lean_object* v___x_909_; 
lean_del_object(v___x_903_);
lean_dec(v_a_901_);
lean_inc(v_mvarId_894_);
v___x_909_ = l_Lean_MVarId_hcongr_x3f(v_mvarId_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_939_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_939_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_939_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_939_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
if (lean_obj_tag(v_a_910_) == 1)
{
lean_object* v_val_914_; lean_object* v___x_916_; 
lean_dec(v_mvarId_894_);
v_val_914_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v_val_914_);
lean_dec_ref_known(v_a_910_, 1);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_val_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_val_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
else
{
lean_object* v___x_918_; 
lean_del_object(v___x_912_);
lean_dec(v_a_910_);
lean_inc(v_mvarId_894_);
v___x_918_ = l_Lean_MVarId_congrImplies_x3f(v_mvarId_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_930_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_930_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_930_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_930_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
if (lean_obj_tag(v_a_919_) == 1)
{
lean_object* v_val_923_; lean_object* v___x_925_; 
lean_dec(v_mvarId_894_);
v_val_923_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_val_923_);
lean_dec_ref_known(v_a_919_, 1);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_val_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_val_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_del_object(v___x_921_);
lean_dec(v_a_919_);
v___x_927_ = ((lean_object*)(l_Lean_MVarId_congr_x3f___closed__1));
v___x_928_ = lean_obj_once(&l_Lean_MVarId_congrCore___closed__3, &l_Lean_MVarId_congrCore___closed__3_once, _init_l_Lean_MVarId_congrCore___closed__3);
v___x_929_ = l_Lean_Meta_throwTacticEx___redArg(v___x_927_, v_mvarId_894_, v___x_928_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
return v___x_929_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_mvarId_894_);
v_a_931_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_918_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_918_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_mvarId_894_);
v_a_940_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_909_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_909_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_mvarId_894_);
v_a_949_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_900_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_900_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_congrCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_894_ = stack[0].m_obj;
lean_object* v_a_895_ = stack[1].m_obj;
lean_object* v_a_896_ = stack[2].m_obj;
lean_object* v_a_897_ = stack[3].m_obj;
lean_object* v_a_898_ = stack[4].m_obj;
lean_object* v_res_957_;
v_res_957_ = l_Lean_MVarId_congrCore(v_mvarId_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrCore___boxed(lean_object* v_mvarId_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_MVarId_congrCore(v_mvarId_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_964_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(uint8_t v_closePost_965_, lean_object* v_mvarId_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Meta_Context_config(v_a_968_);
if (v_closePost_965_ == 0)
{
lean_dec_ref(v___x_979_);
goto v___jp_973_;
}
else
{
uint8_t v_transparency_980_; uint8_t v___x_981_; uint8_t v___x_982_; 
v_transparency_980_ = lean_ctor_get_uint8(v___x_979_, 9);
lean_dec_ref(v___x_979_);
v___x_981_ = 2;
v___x_982_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_980_, v___x_981_);
if (v___x_982_ == 0)
{
uint8_t v___x_983_; uint8_t v___x_984_; 
v___x_983_ = 4;
v___x_984_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_980_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_MVarId_congrPre(v_mvarId_966_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1002_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1002_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1002_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
if (lean_obj_tag(v_a_986_) == 1)
{
lean_object* v_val_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v_val_990_ = lean_ctor_get(v_a_986_, 0);
lean_inc(v_val_990_);
lean_dec_ref_known(v_a_986_, 1);
v___x_991_ = lean_st_ref_take(v_a_967_);
v___x_992_ = lean_box(0);
v___x_993_ = lean_array_push(v___x_991_, v_val_990_);
v___x_994_ = lean_st_ref_put(v_a_967_, v___x_993_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_992_);
v___x_996_ = v___x_988_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_992_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
lean_dec(v_a_986_);
v___x_998_ = lean_box(0);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_998_);
v___x_1000_ = v___x_988_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_985_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_985_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
goto v___jp_973_;
}
}
else
{
goto v___jp_973_;
}
}
v___jp_973_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_974_ = lean_st_ref_take(v_a_967_);
v___x_975_ = lean_box(0);
v___x_976_ = lean_array_push(v___x_974_, v_mvarId_966_);
v___x_977_ = lean_st_ref_put(v_a_967_, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_975_);
return v___x_978_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post_0interp(lean_interpreter_value* stack)
{
uint8_t v_closePost_965_ = stack[0].m_num;
lean_object* v_mvarId_966_ = stack[1].m_obj;
lean_object* v_a_967_ = stack[2].m_obj;
lean_object* v_a_968_ = stack[3].m_obj;
lean_object* v_a_969_ = stack[4].m_obj;
lean_object* v_a_970_ = stack[5].m_obj;
lean_object* v_a_971_ = stack[6].m_obj;
lean_object* v_res_1011_;
v_res_1011_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(v_closePost_965_, v_mvarId_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post___boxed(lean_object* v_closePost_1012_, lean_object* v_mvarId_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_closePost_boxed_1020_; lean_object* v_res_1021_; 
v_closePost_boxed_1020_ = lean_unbox(v_closePost_1012_);
v_res_1021_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(v_closePost_boxed_1020_, v_mvarId_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
return v_res_1021_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(uint8_t v_closePre_1022_, uint8_t v_closePost_1023_, lean_object* v_n_1024_, lean_object* v_mvarId_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_val_1033_; lean_object* v___y_1054_; 
if (v_closePre_1022_ == 0)
{
v_val_1033_ = v_mvarId_1025_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1073_; uint8_t v_transparency_1074_; uint8_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1073_ = l_Lean_Meta_Context_config(v_a_1027_);
v_transparency_1074_ = lean_ctor_get_uint8(v___x_1073_, 9);
lean_dec_ref(v___x_1073_);
v___x_1075_ = 2;
v___x_1076_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v_keyedConfig_1077_; uint8_t v_trackZetaDelta_1078_; lean_object* v_zetaDeltaSet_1079_; lean_object* v_lctx_1080_; lean_object* v_localInstances_1081_; lean_object* v_defEqCtx_x3f_1082_; lean_object* v_synthPendingDepth_1083_; lean_object* v_customCanUnfoldPredicate_x3f_1084_; uint8_t v_univApprox_1085_; uint8_t v_inTypeClassResolution_1086_; uint8_t v_cacheInferType_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_keyedConfig_1077_ = lean_ctor_get(v_a_1027_, 0);
v_trackZetaDelta_1078_ = lean_ctor_get_uint8(v_a_1027_, sizeof(void*)*7);
v_zetaDeltaSet_1079_ = lean_ctor_get(v_a_1027_, 1);
v_lctx_1080_ = lean_ctor_get(v_a_1027_, 2);
v_localInstances_1081_ = lean_ctor_get(v_a_1027_, 3);
v_defEqCtx_x3f_1082_ = lean_ctor_get(v_a_1027_, 4);
v_synthPendingDepth_1083_ = lean_ctor_get(v_a_1027_, 5);
v_customCanUnfoldPredicate_x3f_1084_ = lean_ctor_get(v_a_1027_, 6);
v_univApprox_1085_ = lean_ctor_get_uint8(v_a_1027_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1086_ = lean_ctor_get_uint8(v_a_1027_, sizeof(void*)*7 + 2);
v_cacheInferType_1087_ = lean_ctor_get_uint8(v_a_1027_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1077_);
v___x_1088_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1075_, v_keyedConfig_1077_);
lean_inc(v_customCanUnfoldPredicate_x3f_1084_);
lean_inc(v_synthPendingDepth_1083_);
lean_inc(v_defEqCtx_x3f_1082_);
lean_inc_ref(v_localInstances_1081_);
lean_inc_ref(v_lctx_1080_);
lean_inc(v_zetaDeltaSet_1079_);
v___x_1089_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_zetaDeltaSet_1079_);
lean_ctor_set(v___x_1089_, 2, v_lctx_1080_);
lean_ctor_set(v___x_1089_, 3, v_localInstances_1081_);
lean_ctor_set(v___x_1089_, 4, v_defEqCtx_x3f_1082_);
lean_ctor_set(v___x_1089_, 5, v_synthPendingDepth_1083_);
lean_ctor_set(v___x_1089_, 6, v_customCanUnfoldPredicate_x3f_1084_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*7, v_trackZetaDelta_1078_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*7 + 1, v_univApprox_1085_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1086_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*7 + 3, v_cacheInferType_1087_);
v___x_1090_ = l_Lean_MVarId_congrPre(v_mvarId_1025_, v___x_1089_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec_ref_known(v___x_1089_, 7);
v___y_1054_ = v___x_1090_;
goto v___jp_1053_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_MVarId_congrPre(v_mvarId_1025_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
v___y_1054_ = v___x_1091_;
goto v___jp_1053_;
}
}
v___jp_1032_:
{
lean_object* v_zero_1034_; uint8_t v_isZero_1035_; 
v_zero_1034_ = lean_unsigned_to_nat(0u);
v_isZero_1035_ = lean_nat_dec_eq(v_n_1024_, v_zero_1034_);
if (v_isZero_1035_ == 1)
{
lean_object* v___x_1036_; 
v___x_1036_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(v_closePost_1023_, v_val_1033_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1036_;
}
else
{
lean_object* v_one_1037_; lean_object* v_n_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_one_1037_ = lean_unsigned_to_nat(1u);
v_n_1038_ = lean_nat_sub(v_n_1024_, v_one_1037_);
lean_inc(v_val_1033_);
v___x_1039_ = lean_alloc_closure((void*)(l_Lean_MVarId_congrCore___boxed), 6, 1);
lean_closure_set(v___x_1039_, 0, v_val_1033_);
v___x_1040_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v___x_1039_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
if (lean_obj_tag(v_a_1041_) == 1)
{
lean_object* v_val_1042_; lean_object* v___x_1043_; 
lean_dec(v_val_1033_);
v_val_1042_ = lean_ctor_get(v_a_1041_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v_a_1041_, 1);
v___x_1043_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(v_closePre_1022_, v_closePost_1023_, v_n_1038_, v_val_1042_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_n_1038_);
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; 
lean_dec(v_a_1041_);
lean_dec(v_n_1038_);
v___x_1044_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(v_closePost_1023_, v_val_1033_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1044_;
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_n_1038_);
lean_dec(v_val_1033_);
v_a_1045_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1040_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1040_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
v___jp_1053_:
{
if (lean_obj_tag(v___y_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
v_a_1055_ = lean_ctor_get(v___y_1054_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___y_1054_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1057_ = v___y_1054_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___y_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
if (lean_obj_tag(v_a_1055_) == 1)
{
lean_object* v_val_1059_; 
lean_del_object(v___x_1057_);
v_val_1059_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v_a_1055_, 1);
v_val_1033_ = v_val_1059_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec(v_a_1055_);
v___x_1060_ = lean_box(0);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v___y_1054_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___y_1054_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___y_1054_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___y_1054_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_closePre_1022_ = stack[0].m_num;
uint8_t v_closePost_1023_ = stack[1].m_num;
lean_object* v_n_1024_ = stack[2].m_obj;
lean_object* v_mvarId_1025_ = stack[3].m_obj;
lean_object* v_a_1026_ = stack[4].m_obj;
lean_object* v_a_1027_ = stack[5].m_obj;
lean_object* v_a_1028_ = stack[6].m_obj;
lean_object* v_a_1029_ = stack[7].m_obj;
lean_object* v_a_1030_ = stack[8].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(v_closePre_1022_, v_closePost_1023_, v_n_1024_, v_mvarId_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
stack->m_obj
 = v_res_1092_;
}
lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(uint8_t v_closePre_1093_, uint8_t v_closePost_1094_, lean_object* v_n_1095_, lean_object* v_as_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
if (lean_obj_tag(v_as_1096_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v_head_1105_; lean_object* v_tail_1106_; lean_object* v___x_1107_; 
v_head_1105_ = lean_ctor_get(v_as_1096_, 0);
lean_inc(v_head_1105_);
v_tail_1106_ = lean_ctor_get(v_as_1096_, 1);
lean_inc(v_tail_1106_);
lean_dec_ref_known(v_as_1096_, 2);
v___x_1107_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(v_closePre_1093_, v_closePost_1094_, v_n_1095_, v_head_1105_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_dec_ref_known(v___x_1107_, 1);
v_as_1096_ = v_tail_1106_;
goto _start;
}
else
{
lean_dec(v_tail_1106_);
return v___x_1107_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_closePre_1093_ = stack[0].m_num;
uint8_t v_closePost_1094_ = stack[1].m_num;
lean_object* v_n_1095_ = stack[2].m_obj;
lean_object* v_as_1096_ = stack[3].m_obj;
lean_object* v___y_1097_ = stack[4].m_obj;
lean_object* v___y_1098_ = stack[5].m_obj;
lean_object* v___y_1099_ = stack[6].m_obj;
lean_object* v___y_1100_ = stack[7].m_obj;
lean_object* v___y_1101_ = stack[8].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(v_closePre_1093_, v_closePost_1094_, v_n_1095_, v_as_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0___boxed(lean_object* v_closePre_1110_, lean_object* v_closePost_1111_, lean_object* v_n_1112_, lean_object* v_as_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_closePre_boxed_1120_; uint8_t v_closePost_boxed_1121_; lean_object* v_res_1122_; 
v_closePre_boxed_1120_ = lean_unbox(v_closePre_1110_);
v_closePost_boxed_1121_ = lean_unbox(v_closePost_1111_);
v_res_1122_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(v_closePre_boxed_1120_, v_closePost_boxed_1121_, v_n_1112_, v_as_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec(v_n_1112_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___boxed(lean_object* v_closePre_1123_, lean_object* v_closePost_1124_, lean_object* v_n_1125_, lean_object* v_mvarId_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
uint8_t v_closePre_boxed_1133_; uint8_t v_closePost_boxed_1134_; lean_object* v_res_1135_; 
v_closePre_boxed_1133_ = lean_unbox(v_closePre_1123_);
v_closePost_boxed_1134_ = lean_unbox(v_closePost_1124_);
v_res_1135_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(v_closePre_boxed_1133_, v_closePost_boxed_1134_, v_n_1125_, v_mvarId_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_n_1125_);
return v_res_1135_;
}
}
lean_object* l_Lean_MVarId_congrN(lean_object* v_mvarId_1138_, lean_object* v_depth_1139_, uint8_t v_closePre_1140_, uint8_t v_closePost_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = ((lean_object*)(l_Lean_MVarId_congrN___closed__0));
v___x_1148_ = lean_st_mk_ref(v___x_1147_);
v___x_1149_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(v_closePre_1140_, v_closePost_1141_, v_depth_1139_, v_mvarId_1138_, v___x_1148_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1158_; 
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v___x_1149_, 0);
lean_dec(v_unused_1159_);
v___x_1151_ = v___x_1149_;
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
else
{
lean_dec(v___x_1149_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1153_ = lean_st_ref_get(v___x_1148_);
lean_dec(v___x_1148_);
v___x_1154_ = lean_array_to_list(v___x_1153_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v___x_1148_);
v_a_1160_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1149_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1149_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_congrN_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1138_ = stack[0].m_obj;
lean_object* v_depth_1139_ = stack[1].m_obj;
uint8_t v_closePre_1140_ = stack[2].m_num;
uint8_t v_closePost_1141_ = stack[3].m_num;
lean_object* v_a_1142_ = stack[4].m_obj;
lean_object* v_a_1143_ = stack[5].m_obj;
lean_object* v_a_1144_ = stack[6].m_obj;
lean_object* v_a_1145_ = stack[7].m_obj;
lean_object* v_res_1168_;
v_res_1168_ = l_Lean_MVarId_congrN(v_mvarId_1138_, v_depth_1139_, v_closePre_1140_, v_closePost_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
stack->m_obj
 = v_res_1168_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN___boxed(lean_object* v_mvarId_1169_, lean_object* v_depth_1170_, lean_object* v_closePre_1171_, lean_object* v_closePost_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
uint8_t v_closePre_boxed_1178_; uint8_t v_closePost_boxed_1179_; lean_object* v_res_1180_; 
v_closePre_boxed_1178_ = lean_unbox(v_closePre_1171_);
v_closePost_boxed_1179_ = lean_unbox(v_closePost_1172_);
v_res_1180_ = l_Lean_MVarId_congrN(v_mvarId_1169_, v_depth_1170_, v_closePre_boxed_1178_, v_closePost_boxed_1179_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_depth_1170_);
return v_res_1180_;
}
}
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Congr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Congr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Congr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Congr(builtin);
}
#ifdef __cplusplus
}
#endif
