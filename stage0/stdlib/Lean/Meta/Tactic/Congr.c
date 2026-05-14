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
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_MVarId_heqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_hrefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static const lean_ctor_object l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0_value;
static const lean_string_object l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Internal error: Expected at least two goals after applying `"};
static const lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2;
static const lean_string_object l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`, but unexpectedly found fewer"};
static const lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_MVarId_congrN___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_congrN___closed__0 = (const lean_object*)&l_Lean_MVarId_congrN___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrPre(lean_object* v_mvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
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
lean_dec_ref(v___x_58_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_congrPre___boxed(lean_object* v_mvarId_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_MVarId_congrPre(v_mvarId_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(lean_object* v_fst_93_, lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_fst_93_);
v___x_101_ = l_List_reverse___redArg(v_x_95_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v_head_103_; lean_object* v_tail_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_122_; 
v_head_103_ = lean_ctor_get(v_x_94_, 0);
v_tail_104_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_122_ == 0)
{
v___x_106_ = v_x_94_;
v_isShared_107_ = v_isSharedCheck_122_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_tail_104_);
lean_inc(v_head_103_);
lean_dec(v_x_94_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_122_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; 
lean_inc(v_fst_93_);
v___x_108_ = l_Lean_MVarId_tryClear(v_head_103_, v_fst_93_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref(v___x_108_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v_x_95_);
lean_ctor_set(v___x_106_, 0, v_a_109_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_109_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_x_95_);
v___x_111_ = v_reuseFailAlloc_113_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
v_x_94_ = v_tail_104_;
v_x_95_ = v___x_111_;
goto _start;
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
lean_del_object(v___x_106_);
lean_dec(v_tail_104_);
lean_dec(v_x_95_);
lean_dec(v_fst_93_);
v_a_114_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_108_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_108_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0___boxed(lean_object* v_fst_123_, lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_123_, v_x_124_, v_x_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(lean_object* v_mvarId_139_, lean_object* v_congrThm_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1));
v___x_147_ = l_Lean_Core_mkFreshUserName(v___x_146_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v_type_149_; lean_object* v_proof_150_; lean_object* v___x_151_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref(v___x_147_);
v_type_149_ = lean_ctor_get(v_congrThm_140_, 0);
lean_inc_ref(v_type_149_);
v_proof_150_ = lean_ctor_get(v_congrThm_140_, 1);
lean_inc_ref(v_proof_150_);
lean_dec_ref(v_congrThm_140_);
v___x_151_ = l_Lean_MVarId_assert(v_mvarId_139_, v_a_148_, v_type_149_, v_proof_150_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; uint8_t v___x_153_; lean_object* v___x_154_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref(v___x_151_);
v___x_153_ = 1;
v___x_154_ = l_Lean_Meta_intro1Core(v_a_152_, v___x_153_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
v_fst_156_ = lean_ctor_get(v_a_155_, 0);
lean_inc_n(v_fst_156_, 2);
v_snd_157_ = lean_ctor_get(v_a_155_, 1);
lean_inc(v_snd_157_);
lean_dec(v_a_155_);
v___x_158_ = l_Lean_mkFVar(v_fst_156_);
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2));
v___x_160_ = lean_box(0);
v___x_161_ = l_Lean_MVarId_apply(v_snd_157_, v___x_158_, v___x_159_, v___x_160_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref(v___x_161_);
v___x_163_ = lean_box(0);
v___x_164_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_156_, v_a_162_, v___x_163_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
return v___x_164_;
}
else
{
lean_dec(v_fst_156_);
return v___x_161_;
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_154_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_154_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_151_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_151_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec_ref(v_congrThm_140_);
lean_dec(v_mvarId_139_);
v_a_181_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_147_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_147_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___boxed(lean_object* v_mvarId_189_, lean_object* v_congrThm_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(v_mvarId_189_, v_congrThm_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(lean_object* v_mvarId_197_, lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_197_, v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
v_a_213_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_204_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_204_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_221_, lean_object* v_x_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_mvarId_221_, v_x_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(lean_object* v_00_u03b1_229_, lean_object* v_mvarId_230_, lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_mvarId_230_, v_x_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___boxed(lean_object* v_00_u03b1_238_, lean_object* v_mvarId_239_, lean_object* v_x_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(v_00_u03b1_238_, v_mvarId_239_, v_x_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___lam__0(lean_object* v_mvarId_250_, lean_object* v___x_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; 
lean_inc(v_mvarId_250_);
v___x_257_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_250_, v___x_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v___x_257_);
lean_inc(v_mvarId_250_);
v___x_258_ = l_Lean_MVarId_getType_x27(v_mvarId_250_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_325_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_325_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_325_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_325_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_263_ = ((lean_object*)(l_Lean_MVarId_congr_x3f___lam__0___closed__1));
v___x_264_ = lean_unsigned_to_nat(3u);
v___x_265_ = l_Lean_Expr_isAppOfArity(v_a_259_, v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_268_; 
lean_dec(v_a_259_);
lean_dec(v_mvarId_250_);
v___x_266_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_266_);
v___x_268_ = v___x_261_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_270_ = l_Lean_Expr_appFn_x21(v_a_259_);
lean_dec(v_a_259_);
v___x_271_ = l_Lean_Expr_appArg_x21(v___x_270_);
lean_dec_ref(v___x_270_);
v___x_272_ = l_Lean_Expr_cleanupAnnotations(v___x_271_);
v___x_273_ = l_Lean_Expr_isApp(v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec_ref(v___x_272_);
lean_dec(v_mvarId_250_);
v___x_274_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_274_);
v___x_276_ = v___x_261_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
lean_del_object(v___x_261_);
v___x_278_ = l_Lean_Expr_getAppFn(v___x_272_);
v___x_279_ = 0;
v___x_280_ = l_Lean_Expr_getAppNumArgs(v___x_272_);
lean_dec_ref(v___x_272_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___x_282_ = l_Lean_Meta_mkCongrSimp_x3f(v___x_278_, v___x_279_, v___x_281_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_316_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_316_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_316_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_316_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
if (lean_obj_tag(v_a_283_) == 1)
{
lean_object* v_val_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_311_; 
lean_del_object(v___x_285_);
v_val_287_ = lean_ctor_get(v_a_283_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_283_);
if (v_isSharedCheck_311_ == 0)
{
v___x_289_ = v_a_283_;
v_isShared_290_ = v_isSharedCheck_311_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_val_287_);
lean_dec(v_a_283_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_311_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; 
v___x_291_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(v_mvarId_250_, v_val_287_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_302_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_302_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_302_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_302_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_a_292_);
v___x_297_ = v___x_289_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_301_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_297_);
v___x_299_ = v___x_294_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_del_object(v___x_289_);
v_a_303_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_291_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_291_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_314_; 
lean_dec(v_a_283_);
lean_dec(v_mvarId_250_);
v___x_312_ = lean_box(0);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_312_);
v___x_314_ = v___x_285_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
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
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_mvarId_250_);
v_a_317_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_282_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_282_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_mvarId_250_);
v_a_326_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_258_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_258_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_mvarId_250_);
v_a_334_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_257_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_257_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___lam__0___boxed(lean_object* v_mvarId_342_, lean_object* v___x_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_MVarId_congr_x3f___lam__0(v_mvarId_342_, v___x_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(lean_object* v_x_x3f_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Meta_saveState___redArg(v___y_352_, v___y_354_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_401_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_401_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_401_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_401_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___y_362_; uint8_t v___y_363_; lean_object* v_a_385_; lean_object* v___x_388_; 
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_351_);
v___x_388_ = lean_apply_5(v_x_x3f_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, lean_box(0));
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
if (lean_obj_tag(v_a_389_) == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v___x_388_);
v___x_390_ = l_Lean_Meta_SavedState_restore___redArg(v_a_357_, v___y_352_, v___y_354_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_del_object(v___x_359_);
lean_dec(v_a_357_);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_398_);
v___x_392_ = v___x_390_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_dec(v___x_390_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v_a_389_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_389_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_399_; 
v_a_399_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_399_);
lean_dec_ref(v___x_390_);
v_a_385_ = v_a_399_;
goto v___jp_384_;
}
}
else
{
lean_dec_ref(v_a_389_);
lean_del_object(v___x_359_);
lean_dec(v_a_357_);
return v___x_388_;
}
}
else
{
lean_object* v_a_400_; 
v_a_400_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_400_);
lean_dec_ref(v___x_388_);
v_a_385_ = v_a_400_;
goto v___jp_384_;
}
v___jp_361_:
{
if (v___y_363_ == 0)
{
lean_object* v___x_364_; 
lean_del_object(v___x_359_);
v___x_364_ = l_Lean_Meta_SavedState_restore___redArg(v_a_357_, v___y_352_, v___y_354_);
lean_dec(v_a_357_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_372_);
v___x_366_ = v___x_364_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_dec(v___x_364_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 1);
lean_ctor_set(v___x_366_, 0, v___y_362_);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___y_362_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v___y_362_);
v_a_373_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_364_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_364_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v___x_382_; 
lean_dec(v_a_357_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
lean_ctor_set(v___x_359_, 0, v___y_362_);
v___x_382_ = v___x_359_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___y_362_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
v___jp_384_:
{
uint8_t v___x_386_; 
v___x_386_ = l_Lean_Exception_isInterrupt(v_a_385_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; 
lean_inc_ref(v_a_385_);
v___x_387_ = l_Lean_Exception_isRuntime(v_a_385_);
v___y_362_ = v_a_385_;
v___y_363_ = v___x_387_;
goto v___jp_361_;
}
else
{
v___y_362_ = v_a_385_;
v___y_363_ = v___x_386_;
goto v___jp_361_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v_x_x3f_350_);
v_a_402_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_356_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_356_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_x3f_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(lean_object* v_x_x3f_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_423_) == 0)
{
return v___x_423_;
}
else
{
lean_object* v_a_424_; uint8_t v___y_426_; uint8_t v___x_436_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
v___x_436_ = l_Lean_Exception_isInterrupt(v_a_424_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_Exception_isRuntime(v_a_424_);
v___y_426_ = v___x_437_;
goto v___jp_425_;
}
else
{
lean_dec(v_a_424_);
v___y_426_ = v___x_436_;
goto v___jp_425_;
}
v___jp_425_:
{
if (v___y_426_ == 0)
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v___x_423_, 0);
lean_dec(v_unused_435_);
v___x_428_ = v___x_423_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_dec(v___x_423_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = lean_box(0);
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 0);
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(v_x_x3f_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(lean_object* v_00_u03b1_445_, lean_object* v_x_x3f_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(v_x_x3f_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___boxed(lean_object* v_00_u03b1_453_, lean_object* v_x_x3f_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(v_00_u03b1_453_, v_x_x3f_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f(lean_object* v_mvarId_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_470_; lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_470_ = ((lean_object*)(l_Lean_MVarId_congr_x3f___closed__1));
lean_inc(v_mvarId_464_);
v___f_471_ = lean_alloc_closure((void*)(l_Lean_MVarId_congr_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_471_, 0, v_mvarId_464_);
lean_closure_set(v___f_471_, 1, v___x_470_);
v___x_472_ = lean_alloc_closure((void*)(l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___boxed), 7, 2);
lean_closure_set(v___x_472_, 0, lean_box(0));
lean_closure_set(v___x_472_, 1, v___f_471_);
v___x_473_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_mvarId_464_, v___x_472_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___boxed(lean_object* v_mvarId_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_MVarId_congr_x3f(v_mvarId_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(lean_object* v_00_u03b1_481_, lean_object* v_x_x3f_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_489_, lean_object* v_x_x3f_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(v_00_u03b1_489_, v_x_x3f_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__0(lean_object* v_a_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
lean_inc(v_a_500_);
v___x_506_ = l_Lean_MVarId_getType_x27(v_a_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_557_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_557_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_557_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_557_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_511_ = ((lean_object*)(l_Lean_MVarId_hcongr_x3f___lam__0___closed__1));
v___x_512_ = lean_unsigned_to_nat(4u);
v___x_513_ = l_Lean_Expr_isAppOfArity(v_a_507_, v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_516_; 
lean_dec(v_a_507_);
lean_dec(v_a_500_);
v___x_514_ = lean_box(0);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_514_);
v___x_516_ = v___x_509_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_518_ = l_Lean_Expr_appFn_x21(v_a_507_);
lean_dec(v_a_507_);
v___x_519_ = l_Lean_Expr_appFn_x21(v___x_518_);
lean_dec_ref(v___x_518_);
v___x_520_ = l_Lean_Expr_appArg_x21(v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = l_Lean_Expr_cleanupAnnotations(v___x_520_);
v___x_522_ = l_Lean_Expr_isApp(v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec_ref(v___x_521_);
lean_dec(v_a_500_);
v___x_523_ = lean_box(0);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_523_);
v___x_525_ = v___x_509_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_del_object(v___x_509_);
v___x_527_ = l_Lean_Expr_getAppFn(v___x_521_);
v___x_528_ = l_Lean_Expr_getAppNumArgs(v___x_521_);
lean_dec_ref(v___x_521_);
v___x_529_ = l_Lean_Meta_mkHCongrWithArity(v___x_527_, v___x_528_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref(v___x_529_);
v___x_531_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(v_a_500_, v_a_530_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_540_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_540_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v_a_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_531_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_531_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_500_);
v_a_549_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_529_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_529_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_a_500_);
v_a_558_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_506_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_506_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__0___boxed(lean_object* v_a_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_MVarId_hcongr_x3f___lam__0(v_a_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__1(lean_object* v_mvarId_573_, lean_object* v___x_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
lean_inc(v_mvarId_573_);
v___x_580_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_573_, v___x_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v___x_580_);
v___x_581_ = l_Lean_MVarId_eqOfHEq(v_mvarId_573_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___f_583_; lean_object* v___x_584_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_n(v_a_582_, 2);
lean_dec_ref(v___x_581_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_MVarId_hcongr_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_583_, 0, v_a_582_);
v___x_584_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_a_582_, v___f_583_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_584_;
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_a_585_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_581_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v_mvarId_573_);
v_a_593_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_580_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_580_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__1___boxed(lean_object* v_mvarId_601_, lean_object* v___x_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_MVarId_hcongr_x3f___lam__1(v_mvarId_601_, v___x_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f(lean_object* v_mvarId_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___x_617_; 
v___x_615_ = ((lean_object*)(l_Lean_MVarId_congr_x3f___closed__1));
v___f_616_ = lean_alloc_closure((void*)(l_Lean_MVarId_hcongr_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_616_, 0, v_mvarId_609_);
lean_closure_set(v___f_616_, 1, v___x_615_);
v___x_617_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(v___f_616_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___boxed(lean_object* v_mvarId_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_MVarId_hcongr_x3f(v_mvarId_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(lean_object* v_x_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_saveState___redArg(v___y_627_, v___y_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
v___x_633_ = lean_apply_5(v_x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, lean_box(0));
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_a_632_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_642_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_a_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_672_; 
v_a_643_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_672_ == 0)
{
v___x_645_ = v___x_633_;
v_isShared_646_ = v_isSharedCheck_672_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_633_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_672_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
uint8_t v___y_648_; uint8_t v___x_670_; 
v___x_670_ = l_Lean_Exception_isInterrupt(v_a_643_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
lean_inc(v_a_643_);
v___x_671_ = l_Lean_Exception_isRuntime(v_a_643_);
v___y_648_ = v___x_671_;
goto v___jp_647_;
}
else
{
v___y_648_ = v___x_670_;
goto v___jp_647_;
}
v___jp_647_:
{
if (v___y_648_ == 0)
{
lean_object* v___x_649_; 
lean_del_object(v___x_645_);
lean_dec(v_a_643_);
v___x_649_ = l_Lean_Meta_SavedState_restore___redArg(v_a_632_, v___y_627_, v___y_629_);
lean_dec(v_a_632_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_649_, 0);
lean_dec(v_unused_658_);
v___x_651_ = v___x_649_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_dec(v___x_649_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_box(0);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_649_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_649_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_object* v___x_668_; 
lean_dec(v_a_632_);
if (v_isShared_646_ == 0)
{
v___x_668_ = v___x_645_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_643_);
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
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_x_625_);
v_a_673_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_631_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_631_);
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
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg___boxed(lean_object* v_x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v_x_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(lean_object* v_00_u03b1_688_, lean_object* v_x_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v_x_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___boxed(lean_object* v_00_u03b1_696_, lean_object* v_x_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(v_00_u03b1_696_, v_x_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(lean_object* v_msgData_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v_env_711_; lean_object* v___x_712_; lean_object* v_mctx_713_; lean_object* v_lctx_714_; lean_object* v_options_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_710_ = lean_st_ref_get(v___y_708_);
v_env_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_env_711_);
lean_dec(v___x_710_);
v___x_712_ = lean_st_ref_get(v___y_706_);
v_mctx_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc_ref(v_mctx_713_);
lean_dec(v___x_712_);
v_lctx_714_ = lean_ctor_get(v___y_705_, 2);
v_options_715_ = lean_ctor_get(v___y_707_, 2);
lean_inc_ref(v_options_715_);
lean_inc_ref(v_lctx_714_);
v___x_716_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_716_, 0, v_env_711_);
lean_ctor_set(v___x_716_, 1, v_mctx_713_);
lean_ctor_set(v___x_716_, 2, v_lctx_714_);
lean_ctor_set(v___x_716_, 3, v_options_715_);
v___x_717_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_msgData_704_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msgData_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_ref_732_; lean_object* v___x_733_; lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_742_; 
v_ref_732_ = lean_ctor_get(v___y_729_, 5);
v___x_733_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_742_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_inc(v_ref_732_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_ref_732_);
lean_ctor_set(v___x_738_, 1, v_a_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 1);
lean_ctor_set(v___x_736_, 0, v___x_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg___boxed(lean_object* v_msg_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(v_msg_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_749_;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0(lean_object* v___x_760_, lean_object* v_mvarId_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
lean_inc(v___x_760_);
v___x_767_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_760_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref(v___x_767_);
v___x_769_ = 0;
v___x_770_ = ((lean_object*)(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0));
v___x_771_ = lean_box(0);
v___x_772_ = l_Lean_MVarId_apply(v_mvarId_761_, v_a_768_, v___x_770_, v___x_771_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_811_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_811_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_811_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_811_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; 
if (lean_obj_tag(v_a_773_) == 1)
{
lean_object* v_tail_788_; 
v_tail_788_ = lean_ctor_get(v_a_773_, 1);
lean_inc(v_tail_788_);
if (lean_obj_tag(v_tail_788_) == 1)
{
lean_object* v_head_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_809_; 
lean_dec(v___x_760_);
v_head_789_ = lean_ctor_get(v_a_773_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_a_773_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_a_773_, 1);
lean_dec(v_unused_810_);
v___x_791_ = v_a_773_;
v_isShared_792_ = v_isSharedCheck_809_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_head_789_);
lean_dec(v_a_773_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_809_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_head_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_807_; 
v_head_793_ = lean_ctor_get(v_tail_788_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v_tail_788_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_tail_788_, 1);
lean_dec(v_unused_808_);
v___x_795_ = v_tail_788_;
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_head_793_);
lean_dec(v_tail_788_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_box(0);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_head_793_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_806_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_799_);
v___x_801_ = v___x_791_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_head_789_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_799_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_801_);
v___x_803_ = v___x_775_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_a_773_);
lean_dec(v_tail_788_);
lean_del_object(v___x_775_);
v___y_778_ = v___y_762_;
v___y_779_ = v___y_763_;
v___y_780_ = v___y_764_;
v___y_781_ = v___y_765_;
goto v___jp_777_;
}
}
else
{
lean_del_object(v___x_775_);
lean_dec(v_a_773_);
v___y_778_ = v___y_762_;
v___y_779_ = v___y_763_;
v___y_780_ = v___y_764_;
v___y_781_ = v___y_765_;
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_782_ = lean_obj_once(&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2, &l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2_once, _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2);
v___x_783_ = l_Lean_MessageData_ofConstName(v___x_760_, v___x_769_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_obj_once(&l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4, &l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4_once, _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(v___x_786_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
return v___x_787_;
}
}
}
else
{
lean_dec(v___x_760_);
return v___x_772_;
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_mvarId_761_);
lean_dec(v___x_760_);
v_a_812_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_767_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_767_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___boxed(lean_object* v___x_820_, lean_object* v_mvarId_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_MVarId_congrImplies_x3f___lam__0(v___x_820_, v_mvarId_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f(lean_object* v_mvarId_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___f_838_; lean_object* v___x_839_; 
v___x_837_ = ((lean_object*)(l_Lean_MVarId_congrImplies_x3f___closed__1));
v___f_838_ = lean_alloc_closure((void*)(l_Lean_MVarId_congrImplies_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_838_, 0, v___x_837_);
lean_closure_set(v___f_838_, 1, v_mvarId_831_);
v___x_839_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v___f_838_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___boxed(lean_object* v_mvarId_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_MVarId_congrImplies_x3f(v_mvarId_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(lean_object* v_00_u03b1_847_, lean_object* v_msg_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(v_msg_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___boxed(lean_object* v_00_u03b1_855_, lean_object* v_msg_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(v_00_u03b1_855_, v_msg_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_862_;
}
}
static lean_object* _init_l_Lean_MVarId_congrCore___closed__2(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_MVarId_congrCore___closed__1));
v___x_867_ = l_Lean_MessageData_ofFormat(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_MVarId_congrCore___closed__3(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_obj_once(&l_Lean_MVarId_congrCore___closed__2, &l_Lean_MVarId_congrCore___closed__2_once, _init_l_Lean_MVarId_congrCore___closed__2);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrCore(lean_object* v_mvarId_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
lean_inc(v_mvarId_870_);
v___x_876_ = l_Lean_MVarId_congr_x3f(v_mvarId_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_924_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_924_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_924_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_924_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_883_; 
lean_dec(v_mvarId_870_);
v_val_881_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_val_881_);
lean_dec_ref(v_a_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_val_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_val_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
lean_object* v___x_885_; 
lean_del_object(v___x_879_);
lean_dec(v_a_877_);
lean_inc(v_mvarId_870_);
v___x_885_ = l_Lean_MVarId_hcongr_x3f(v_mvarId_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_915_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_915_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_915_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_915_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
if (lean_obj_tag(v_a_886_) == 1)
{
lean_object* v_val_890_; lean_object* v___x_892_; 
lean_dec(v_mvarId_870_);
v_val_890_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_val_890_);
lean_dec_ref(v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_val_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_val_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v___x_894_; 
lean_del_object(v___x_888_);
lean_dec(v_a_886_);
lean_inc(v_mvarId_870_);
v___x_894_ = l_Lean_MVarId_congrImplies_x3f(v_mvarId_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_906_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_906_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_906_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_906_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
if (lean_obj_tag(v_a_895_) == 1)
{
lean_object* v_val_899_; lean_object* v___x_901_; 
lean_dec(v_mvarId_870_);
v_val_899_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_val_899_);
lean_dec_ref(v_a_895_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_val_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_val_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_del_object(v___x_897_);
lean_dec(v_a_895_);
v___x_903_ = ((lean_object*)(l_Lean_MVarId_congr_x3f___closed__1));
v___x_904_ = lean_obj_once(&l_Lean_MVarId_congrCore___closed__3, &l_Lean_MVarId_congrCore___closed__3_once, _init_l_Lean_MVarId_congrCore___closed__3);
v___x_905_ = l_Lean_Meta_throwTacticEx___redArg(v___x_903_, v_mvarId_870_, v___x_904_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_905_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_mvarId_870_);
v_a_907_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_894_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_894_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_mvarId_870_);
v_a_916_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_885_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_885_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_mvarId_870_);
v_a_925_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_876_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_876_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrCore___boxed(lean_object* v_mvarId_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_MVarId_congrCore(v_mvarId_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(uint8_t v_closePost_940_, lean_object* v_mvarId_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Meta_Context_config(v_a_943_);
if (v_closePost_940_ == 0)
{
lean_dec_ref(v___x_954_);
goto v___jp_948_;
}
else
{
uint8_t v_transparency_955_; uint8_t v___x_956_; uint8_t v___x_957_; 
v_transparency_955_ = lean_ctor_get_uint8(v___x_954_, 9);
lean_dec_ref(v___x_954_);
v___x_956_ = 2;
v___x_957_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_955_, v___x_956_);
if (v___x_957_ == 0)
{
uint8_t v___x_958_; uint8_t v___x_959_; 
v___x_958_ = 4;
v___x_959_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_955_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_MVarId_congrPre(v_mvarId_941_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_977_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_977_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_977_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_977_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
if (lean_obj_tag(v_a_961_) == 1)
{
lean_object* v_val_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v_val_965_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_val_965_);
lean_dec_ref(v_a_961_);
v___x_966_ = lean_st_ref_take(v_a_942_);
v___x_967_ = lean_array_push(v___x_966_, v_val_965_);
v___x_968_ = lean_st_ref_set(v_a_942_, v___x_967_);
v___x_969_ = lean_box(0);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_969_);
v___x_971_ = v___x_963_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec(v_a_961_);
v___x_973_ = lean_box(0);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_973_);
v___x_975_ = v___x_963_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_a_978_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_960_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_960_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
goto v___jp_948_;
}
}
else
{
goto v___jp_948_;
}
}
v___jp_948_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_949_ = lean_st_ref_take(v_a_942_);
v___x_950_ = lean_array_push(v___x_949_, v_mvarId_941_);
v___x_951_ = lean_st_ref_set(v_a_942_, v___x_950_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post___boxed(lean_object* v_closePost_986_, lean_object* v_mvarId_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
uint8_t v_closePost_boxed_994_; lean_object* v_res_995_; 
v_closePost_boxed_994_ = lean_unbox(v_closePost_986_);
v_res_995_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(v_closePost_boxed_994_, v_mvarId_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
return v_res_995_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0(void){
_start:
{
uint8_t v___x_996_; uint64_t v___x_997_; 
v___x_996_ = 2;
v___x_997_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(uint8_t v_closePre_998_, uint8_t v_closePost_999_, lean_object* v_n_1000_, lean_object* v_mvarId_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_val_1009_; lean_object* v_a_1030_; 
if (v_closePre_998_ == 0)
{
v_val_1009_ = v_mvarId_1001_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1034_; uint8_t v_foApprox_1035_; uint8_t v_ctxApprox_1036_; uint8_t v_quasiPatternApprox_1037_; uint8_t v_constApprox_1038_; uint8_t v_isDefEqStuckEx_1039_; uint8_t v_unificationHints_1040_; uint8_t v_proofIrrelevance_1041_; uint8_t v_assignSyntheticOpaque_1042_; uint8_t v_offsetCnstrs_1043_; uint8_t v_etaStruct_1044_; uint8_t v_univApprox_1045_; uint8_t v_iota_1046_; uint8_t v_beta_1047_; uint8_t v_proj_1048_; uint8_t v_zeta_1049_; uint8_t v_zetaDelta_1050_; uint8_t v_zetaUnused_1051_; uint8_t v_zetaHave_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1089_; 
v___x_1034_ = l_Lean_Meta_Context_config(v_a_1003_);
v_foApprox_1035_ = lean_ctor_get_uint8(v___x_1034_, 0);
v_ctxApprox_1036_ = lean_ctor_get_uint8(v___x_1034_, 1);
v_quasiPatternApprox_1037_ = lean_ctor_get_uint8(v___x_1034_, 2);
v_constApprox_1038_ = lean_ctor_get_uint8(v___x_1034_, 3);
v_isDefEqStuckEx_1039_ = lean_ctor_get_uint8(v___x_1034_, 4);
v_unificationHints_1040_ = lean_ctor_get_uint8(v___x_1034_, 5);
v_proofIrrelevance_1041_ = lean_ctor_get_uint8(v___x_1034_, 6);
v_assignSyntheticOpaque_1042_ = lean_ctor_get_uint8(v___x_1034_, 7);
v_offsetCnstrs_1043_ = lean_ctor_get_uint8(v___x_1034_, 8);
v_etaStruct_1044_ = lean_ctor_get_uint8(v___x_1034_, 10);
v_univApprox_1045_ = lean_ctor_get_uint8(v___x_1034_, 11);
v_iota_1046_ = lean_ctor_get_uint8(v___x_1034_, 12);
v_beta_1047_ = lean_ctor_get_uint8(v___x_1034_, 13);
v_proj_1048_ = lean_ctor_get_uint8(v___x_1034_, 14);
v_zeta_1049_ = lean_ctor_get_uint8(v___x_1034_, 15);
v_zetaDelta_1050_ = lean_ctor_get_uint8(v___x_1034_, 16);
v_zetaUnused_1051_ = lean_ctor_get_uint8(v___x_1034_, 17);
v_zetaHave_1052_ = lean_ctor_get_uint8(v___x_1034_, 18);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1054_ = v___x_1034_;
v_isShared_1055_ = v_isSharedCheck_1089_;
goto v_resetjp_1053_;
}
else
{
lean_dec(v___x_1034_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1089_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
uint8_t v_trackZetaDelta_1056_; lean_object* v_zetaDeltaSet_1057_; lean_object* v_lctx_1058_; lean_object* v_localInstances_1059_; lean_object* v_defEqCtx_x3f_1060_; lean_object* v_synthPendingDepth_1061_; lean_object* v_canUnfold_x3f_1062_; uint8_t v_univApprox_1063_; uint8_t v_inTypeClassResolution_1064_; uint8_t v_cacheInferType_1065_; uint8_t v___x_1066_; lean_object* v_config_1068_; 
v_trackZetaDelta_1056_ = lean_ctor_get_uint8(v_a_1003_, sizeof(void*)*7);
v_zetaDeltaSet_1057_ = lean_ctor_get(v_a_1003_, 1);
v_lctx_1058_ = lean_ctor_get(v_a_1003_, 2);
v_localInstances_1059_ = lean_ctor_get(v_a_1003_, 3);
v_defEqCtx_x3f_1060_ = lean_ctor_get(v_a_1003_, 4);
v_synthPendingDepth_1061_ = lean_ctor_get(v_a_1003_, 5);
v_canUnfold_x3f_1062_ = lean_ctor_get(v_a_1003_, 6);
v_univApprox_1063_ = lean_ctor_get_uint8(v_a_1003_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1064_ = lean_ctor_get_uint8(v_a_1003_, sizeof(void*)*7 + 2);
v_cacheInferType_1065_ = lean_ctor_get_uint8(v_a_1003_, sizeof(void*)*7 + 3);
v___x_1066_ = 2;
if (v_isShared_1055_ == 0)
{
v_config_1068_ = v___x_1054_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 0, v_foApprox_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 1, v_ctxApprox_1036_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 2, v_quasiPatternApprox_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 3, v_constApprox_1038_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 4, v_isDefEqStuckEx_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 5, v_unificationHints_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 6, v_proofIrrelevance_1041_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 7, v_assignSyntheticOpaque_1042_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 8, v_offsetCnstrs_1043_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 10, v_etaStruct_1044_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 11, v_univApprox_1045_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 12, v_iota_1046_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 13, v_beta_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 14, v_proj_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 15, v_zeta_1049_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 16, v_zetaDelta_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 17, v_zetaUnused_1051_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, 18, v_zetaHave_1052_);
v_config_1068_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
uint64_t v___x_1069_; uint64_t v___x_1070_; uint64_t v___x_1071_; uint64_t v___x_1072_; uint64_t v___x_1073_; uint64_t v_key_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_ctor_set_uint8(v_config_1068_, 9, v___x_1066_);
v___x_1069_ = l_Lean_Meta_Context_configKey(v_a_1003_);
v___x_1070_ = 2ULL;
v___x_1071_ = lean_uint64_shift_right(v___x_1069_, v___x_1070_);
v___x_1072_ = lean_uint64_shift_left(v___x_1071_, v___x_1070_);
v___x_1073_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0, &l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0);
v_key_1074_ = lean_uint64_lor(v___x_1072_, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1075_, 0, v_config_1068_);
lean_ctor_set_uint64(v___x_1075_, sizeof(void*)*1, v_key_1074_);
lean_inc(v_canUnfold_x3f_1062_);
lean_inc(v_synthPendingDepth_1061_);
lean_inc(v_defEqCtx_x3f_1060_);
lean_inc_ref(v_localInstances_1059_);
lean_inc_ref(v_lctx_1058_);
lean_inc(v_zetaDeltaSet_1057_);
v___x_1076_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v_zetaDeltaSet_1057_);
lean_ctor_set(v___x_1076_, 2, v_lctx_1058_);
lean_ctor_set(v___x_1076_, 3, v_localInstances_1059_);
lean_ctor_set(v___x_1076_, 4, v_defEqCtx_x3f_1060_);
lean_ctor_set(v___x_1076_, 5, v_synthPendingDepth_1061_);
lean_ctor_set(v___x_1076_, 6, v_canUnfold_x3f_1062_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*7, v_trackZetaDelta_1056_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*7 + 1, v_univApprox_1063_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1064_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*7 + 3, v_cacheInferType_1065_);
v___x_1077_ = l_Lean_MVarId_congrPre(v_mvarId_1001_, v___x_1076_, v_a_1004_, v_a_1005_, v_a_1006_);
lean_dec_ref(v___x_1076_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref(v___x_1077_);
v_a_1030_ = v_a_1078_;
goto v___jp_1029_;
}
else
{
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1079_);
lean_dec_ref(v___x_1077_);
v_a_1030_ = v_a_1079_;
goto v___jp_1029_;
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1077_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
}
v___jp_1008_:
{
lean_object* v_zero_1010_; uint8_t v_isZero_1011_; 
v_zero_1010_ = lean_unsigned_to_nat(0u);
v_isZero_1011_ = lean_nat_dec_eq(v_n_1000_, v_zero_1010_);
if (v_isZero_1011_ == 1)
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(v_closePost_999_, v_val_1009_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_inc(v_val_1009_);
v___x_1013_ = lean_alloc_closure((void*)(l_Lean_MVarId_congrCore___boxed), 6, 1);
lean_closure_set(v___x_1013_, 0, v_val_1009_);
v___x_1014_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(v___x_1013_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1014_);
if (lean_obj_tag(v_a_1015_) == 1)
{
lean_object* v_val_1016_; lean_object* v_one_1017_; lean_object* v_n_1018_; lean_object* v___x_1019_; 
lean_dec(v_val_1009_);
v_val_1016_ = lean_ctor_get(v_a_1015_, 0);
lean_inc(v_val_1016_);
lean_dec_ref(v_a_1015_);
v_one_1017_ = lean_unsigned_to_nat(1u);
v_n_1018_ = lean_nat_sub(v_n_1000_, v_one_1017_);
v___x_1019_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(v_closePre_998_, v_closePost_999_, v_n_1018_, v_val_1016_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
lean_dec(v_n_1018_);
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; 
lean_dec(v_a_1015_);
v___x_1020_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(v_closePost_999_, v_val_1009_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1020_;
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_val_1009_);
v_a_1021_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1014_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1014_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
v___jp_1029_:
{
if (lean_obj_tag(v_a_1030_) == 1)
{
lean_object* v_val_1031_; 
v_val_1031_ = lean_ctor_get(v_a_1030_, 0);
lean_inc(v_val_1031_);
lean_dec_ref(v_a_1030_);
v_val_1009_ = v_val_1031_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v_a_1030_);
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(uint8_t v_closePre_1090_, uint8_t v_closePost_1091_, lean_object* v_n_1092_, lean_object* v_as_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
if (lean_obj_tag(v_as_1093_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v_head_1102_; lean_object* v_tail_1103_; lean_object* v___x_1104_; 
v_head_1102_ = lean_ctor_get(v_as_1093_, 0);
lean_inc(v_head_1102_);
v_tail_1103_ = lean_ctor_get(v_as_1093_, 1);
lean_inc(v_tail_1103_);
lean_dec_ref(v_as_1093_);
v___x_1104_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(v_closePre_1090_, v_closePost_1091_, v_n_1092_, v_head_1102_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec_ref(v___x_1104_);
v_as_1093_ = v_tail_1103_;
goto _start;
}
else
{
lean_dec(v_tail_1103_);
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0___boxed(lean_object* v_closePre_1106_, lean_object* v_closePost_1107_, lean_object* v_n_1108_, lean_object* v_as_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v_closePre_boxed_1116_; uint8_t v_closePost_boxed_1117_; lean_object* v_res_1118_; 
v_closePre_boxed_1116_ = lean_unbox(v_closePre_1106_);
v_closePost_boxed_1117_ = lean_unbox(v_closePost_1107_);
v_res_1118_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(v_closePre_boxed_1116_, v_closePost_boxed_1117_, v_n_1108_, v_as_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec(v_n_1108_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___boxed(lean_object* v_closePre_1119_, lean_object* v_closePost_1120_, lean_object* v_n_1121_, lean_object* v_mvarId_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
uint8_t v_closePre_boxed_1129_; uint8_t v_closePost_boxed_1130_; lean_object* v_res_1131_; 
v_closePre_boxed_1129_ = lean_unbox(v_closePre_1119_);
v_closePost_boxed_1130_ = lean_unbox(v_closePost_1120_);
v_res_1131_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(v_closePre_boxed_1129_, v_closePost_boxed_1130_, v_n_1121_, v_mvarId_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec(v_n_1121_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN(lean_object* v_mvarId_1134_, lean_object* v_depth_1135_, uint8_t v_closePre_1136_, uint8_t v_closePost_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = ((lean_object*)(l_Lean_MVarId_congrN___closed__0));
v___x_1144_ = lean_st_mk_ref(v___x_1143_);
v___x_1145_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(v_closePre_1136_, v_closePost_1137_, v_depth_1135_, v_mvarId_1134_, v___x_1144_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1154_; 
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v___x_1145_, 0);
lean_dec(v_unused_1155_);
v___x_1147_ = v___x_1145_;
v_isShared_1148_ = v_isSharedCheck_1154_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v___x_1145_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1154_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1149_ = lean_st_ref_get(v___x_1144_);
lean_dec(v___x_1144_);
v___x_1150_ = lean_array_to_list(v___x_1149_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v___x_1144_);
v_a_1156_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1145_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1145_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN___boxed(lean_object* v_mvarId_1164_, lean_object* v_depth_1165_, lean_object* v_closePre_1166_, lean_object* v_closePost_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
uint8_t v_closePre_boxed_1173_; uint8_t v_closePost_boxed_1174_; lean_object* v_res_1175_; 
v_closePre_boxed_1173_ = lean_unbox(v_closePre_1166_);
v_closePost_boxed_1174_ = lean_unbox(v_closePost_1167_);
v_res_1175_ = l_Lean_MVarId_congrN(v_mvarId_1164_, v_depth_1165_, v_closePre_boxed_1173_, v_closePost_boxed_1174_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_depth_1165_);
return v_res_1175_;
}
}
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Congr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
