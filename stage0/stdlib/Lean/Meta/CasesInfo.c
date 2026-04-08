// Lean compiler output
// Module: Lean.Meta.CasesInfo
// Imports: public import Lean.Meta.Basic import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
uint8_t l_Lean_isCasesOnLike(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_default_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_default_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_instInhabitedCasesAltInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_instInhabitedCasesAltInfo_default___closed__0 = (const lean_object*)&l_instInhabitedCasesAltInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_instInhabitedCasesAltInfo_default = (const lean_object*)&l_instInhabitedCasesAltInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_instInhabitedCasesAltInfo = (const lean_object*)&l_instInhabitedCasesAltInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_CasesInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_CasesInfo_numAlts___boxed(lean_object*);
static const lean_closure_object l_panic___at___00getCasesInfo_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00getCasesInfo_x3f_spec__1___closed__0 = (const lean_object*)&l_panic___at___00getCasesInfo_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00getCasesInfo_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00getCasesInfo_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00getCasesInfo_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00getCasesInfo_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.CasesInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "getCasesInfo\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: mr.isApp\n          "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "assertion violation: motiveArg == xs[discrPos]!\n            "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7___redArg(lean_object*, lean_object*);
static const lean_string_object l_getCasesInfo_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "assertion violation: r.isApp\n      "};
static const lean_object* l_getCasesInfo_x3f___lam__0___closed__0 = (const lean_object*)&l_getCasesInfo_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_getCasesInfo_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___lam__0___closed__1;
static const lean_string_object l_getCasesInfo_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "assertion violation: r.appArg!.isFVar  -- major argument\n      "};
static const lean_object* l_getCasesInfo_x3f___lam__0___closed__2 = (const lean_object*)&l_getCasesInfo_x3f___lam__0___closed__2_value;
static lean_once_cell_t l_getCasesInfo_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___lam__0___closed__3;
static const lean_string_object l_getCasesInfo_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "assertion violation: r.getAppFn.isFVar -- motive\n      "};
static const lean_object* l_getCasesInfo_x3f___lam__0___closed__4 = (const lean_object*)&l_getCasesInfo_x3f___lam__0___closed__4_value;
static lean_once_cell_t l_getCasesInfo_x3f___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___lam__0___closed__5;
static const lean_array_object l_getCasesInfo_x3f___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_getCasesInfo_x3f___lam__0___closed__6 = (const lean_object*)&l_getCasesInfo_x3f___lam__0___closed__6_value;
static lean_once_cell_t l_getCasesInfo_x3f___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___lam__0___closed__7;
static lean_once_cell_t l_getCasesInfo_x3f___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___lam__0___closed__8;
LEAN_EXPORT lean_object* l_getCasesInfo_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_getCasesInfo_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_getCasesInfo_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___closed__0;
static lean_once_cell_t l_getCasesInfo_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___closed__1;
static lean_once_cell_t l_getCasesInfo_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___closed__2;
static const lean_array_object l_getCasesInfo_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_getCasesInfo_x3f___closed__3 = (const lean_object*)&l_getCasesInfo_x3f___closed__3_value;
static lean_once_cell_t l_getCasesInfo_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___closed__4;
static lean_once_cell_t l_getCasesInfo_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___closed__5;
static lean_once_cell_t l_getCasesInfo_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___closed__6;
static lean_once_cell_t l_getCasesInfo_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_getCasesInfo_x3f___closed__7;
LEAN_EXPORT lean_object* l_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_getCasesInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_CasesAltInfo_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_ctorName_8_; lean_object* v_numFields_9_; lean_object* v___x_10_; 
v_ctorName_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_ctorName_8_);
v_numFields_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_numFields_9_);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_ctorName_8_, v_numFields_9_);
return v___x_10_;
}
else
{
lean_object* v_numHyps_11_; lean_object* v___x_12_; 
v_numHyps_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_numHyps_11_);
lean_dec_ref(v_t_6_);
v___x_12_ = lean_apply_1(v_k_7_, v_numHyps_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_CasesAltInfo_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_CasesAltInfo_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_CasesAltInfo_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_CasesAltInfo_ctor_elim___redArg(lean_object* v_t_25_, lean_object* v_ctor_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_CasesAltInfo_ctorElim___redArg(v_t_25_, v_ctor_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_CasesAltInfo_ctor_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_ctor_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_CasesAltInfo_ctorElim___redArg(v_t_29_, v_ctor_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_CasesAltInfo_default_elim___redArg(lean_object* v_t_33_, lean_object* v_default_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_CasesAltInfo_ctorElim___redArg(v_t_33_, v_default_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_CasesAltInfo_default_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_default_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_CasesAltInfo_ctorElim___redArg(v_t_37_, v_default_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_CasesInfo_numAlts(lean_object* v_c_46_){
_start:
{
lean_object* v_altNumParams_47_; lean_object* v___x_48_; 
v_altNumParams_47_ = lean_ctor_get(v_c_46_, 5);
v___x_48_ = lean_array_get_size(v_altNumParams_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_CasesInfo_numAlts___boxed(lean_object* v_c_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_CasesInfo_numAlts(v_c_49_);
lean_dec_ref(v_c_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00getCasesInfo_x3f_spec__1(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_6295__overap_59_; lean_object* v___x_60_; 
v___f_58_ = ((lean_object*)(l_panic___at___00getCasesInfo_x3f_spec__1___closed__0));
v___x_6295__overap_59_ = lean_panic_fn_borrowed(v___f_58_, v_msg_52_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
v___x_60_ = lean_apply_5(v___x_6295__overap_59_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, lean_box(0));
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00getCasesInfo_x3f_spec__1___boxed(lean_object* v_msg_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_panic___at___00getCasesInfo_x3f_spec__1(v_msg_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00getCasesInfo_x3f_spec__3(lean_object* v_msg_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_6317__overap_75_; lean_object* v___x_76_; 
v___f_74_ = ((lean_object*)(l_panic___at___00getCasesInfo_x3f_spec__1___closed__0));
v___x_6317__overap_75_ = lean_panic_fn_borrowed(v___f_74_, v_msg_68_);
lean_inc(v___y_72_);
lean_inc_ref(v___y_71_);
lean_inc(v___y_70_);
lean_inc_ref(v___y_69_);
v___x_76_ = lean_apply_5(v___x_6317__overap_75_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, lean_box(0));
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00getCasesInfo_x3f_spec__3___boxed(lean_object* v_msg_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_panic___at___00getCasesInfo_x3f_spec__3(v_msg_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0(lean_object* v_k_84_, lean_object* v_b_85_, lean_object* v_c_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; 
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
v___x_92_ = lean_apply_7(v_k_84_, v_b_85_, v_c_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0___boxed(lean_object* v_k_93_, lean_object* v_b_94_, lean_object* v_c_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0(v_k_93_, v_b_94_, v_c_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(lean_object* v_type_102_, lean_object* v_k_103_, uint8_t v_cleanupAnnotations_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___f_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___f_110_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_110_, 0, v_k_103_);
v___x_111_ = 0;
v___x_112_ = lean_box(0);
v___x_113_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_111_, v___x_112_, v_type_102_, v___f_110_, v_cleanupAnnotations_104_, v___x_111_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
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
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_122_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_113_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_113_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___boxed(lean_object* v_type_130_, lean_object* v_k_131_, lean_object* v_cleanupAnnotations_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_138_; lean_object* v_res_139_; 
v_cleanupAnnotations_boxed_138_ = lean_unbox(v_cleanupAnnotations_132_);
v_res_139_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(v_type_130_, v_k_131_, v_cleanupAnnotations_boxed_138_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6(lean_object* v_00_u03b1_140_, lean_object* v_type_141_, lean_object* v_k_142_, uint8_t v_cleanupAnnotations_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(v_type_141_, v_k_142_, v_cleanupAnnotations_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___boxed(lean_object* v_00_u03b1_150_, lean_object* v_type_151_, lean_object* v_k_152_, lean_object* v_cleanupAnnotations_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_159_; lean_object* v_res_160_; 
v_cleanupAnnotations_boxed_159_ = lean_unbox(v_cleanupAnnotations_153_);
v_res_160_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6(v_00_u03b1_150_, v_type_151_, v_k_152_, v_cleanupAnnotations_boxed_159_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10(lean_object* v_msgData_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v_env_168_; lean_object* v___x_169_; lean_object* v_mctx_170_; lean_object* v_lctx_171_; lean_object* v_options_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_167_ = lean_st_ref_get(v___y_165_);
v_env_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc_ref(v_env_168_);
lean_dec(v___x_167_);
v___x_169_ = lean_st_ref_get(v___y_163_);
v_mctx_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_mctx_170_);
lean_dec(v___x_169_);
v_lctx_171_ = lean_ctor_get(v___y_162_, 2);
v_options_172_ = lean_ctor_get(v___y_164_, 2);
lean_inc_ref(v_options_172_);
lean_inc_ref(v_lctx_171_);
v___x_173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_173_, 0, v_env_168_);
lean_ctor_set(v___x_173_, 1, v_mctx_170_);
lean_ctor_set(v___x_173_, 2, v_lctx_171_);
lean_ctor_set(v___x_173_, 3, v_options_172_);
v___x_174_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_msgData_161_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10___boxed(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10(v_msgData_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_ref_189_; lean_object* v___x_190_; lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_199_; 
v_ref_189_ = lean_ctor_get(v___y_186_, 5);
v___x_190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10(v_msg_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_199_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
lean_inc(v_ref_189_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v_ref_189_);
lean_ctor_set(v___x_195_, 1, v_a_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 1);
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg___boxed(lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(v_msg_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_instMonadEIO(lean_box(0));
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_toApplicative_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_281_; 
v___x_218_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0);
v___x_219_ = l_StateRefT_x27_instMonad___redArg(v___x_218_);
v_toApplicative_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_219_, 1);
lean_dec(v_unused_282_);
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_281_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_toApplicative_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_281_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_toFunctor_224_; lean_object* v_toSeq_225_; lean_object* v_toSeqLeft_226_; lean_object* v_toSeqRight_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_279_; 
v_toFunctor_224_ = lean_ctor_get(v_toApplicative_220_, 0);
v_toSeq_225_ = lean_ctor_get(v_toApplicative_220_, 2);
v_toSeqLeft_226_ = lean_ctor_get(v_toApplicative_220_, 3);
v_toSeqRight_227_ = lean_ctor_get(v_toApplicative_220_, 4);
v_isSharedCheck_279_ = !lean_is_exclusive(v_toApplicative_220_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v_toApplicative_220_, 1);
lean_dec(v_unused_280_);
v___x_229_ = v_toApplicative_220_;
v_isShared_230_ = v_isSharedCheck_279_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_toSeqRight_227_);
lean_inc(v_toSeqLeft_226_);
lean_inc(v_toSeq_225_);
lean_inc(v_toFunctor_224_);
lean_dec(v_toApplicative_220_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_279_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_240_; 
v___f_231_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__1));
v___f_232_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__2));
lean_inc_ref(v_toFunctor_224_);
v___f_233_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_233_, 0, v_toFunctor_224_);
v___f_234_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_234_, 0, v_toFunctor_224_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___f_233_);
lean_ctor_set(v___x_235_, 1, v___f_234_);
v___f_236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_236_, 0, v_toSeqRight_227_);
v___f_237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_237_, 0, v_toSeqLeft_226_);
v___f_238_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_238_, 0, v_toSeq_225_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v___f_236_);
lean_ctor_set(v___x_229_, 3, v___f_237_);
lean_ctor_set(v___x_229_, 2, v___f_238_);
lean_ctor_set(v___x_229_, 1, v___f_231_);
lean_ctor_set(v___x_229_, 0, v___x_235_);
v___x_240_ = v___x_229_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___f_231_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v___f_238_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v___f_237_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v___f_236_);
v___x_240_ = v_reuseFailAlloc_278_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___f_232_);
lean_ctor_set(v___x_222_, 0, v___x_240_);
v___x_242_ = v___x_222_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___f_232_);
v___x_242_ = v_reuseFailAlloc_277_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v_toApplicative_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_275_; 
v___x_243_ = l_StateRefT_x27_instMonad___redArg(v___x_242_);
v_toApplicative_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v___x_243_, 1);
lean_dec(v_unused_276_);
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_275_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_toApplicative_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_275_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_toFunctor_248_; lean_object* v_toSeq_249_; lean_object* v_toSeqLeft_250_; lean_object* v_toSeqRight_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_273_; 
v_toFunctor_248_ = lean_ctor_get(v_toApplicative_244_, 0);
v_toSeq_249_ = lean_ctor_get(v_toApplicative_244_, 2);
v_toSeqLeft_250_ = lean_ctor_get(v_toApplicative_244_, 3);
v_toSeqRight_251_ = lean_ctor_get(v_toApplicative_244_, 4);
v_isSharedCheck_273_ = !lean_is_exclusive(v_toApplicative_244_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_toApplicative_244_, 1);
lean_dec(v_unused_274_);
v___x_253_ = v_toApplicative_244_;
v_isShared_254_ = v_isSharedCheck_273_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_toSeqRight_251_);
lean_inc(v_toSeqLeft_250_);
lean_inc(v_toSeq_249_);
lean_inc(v_toFunctor_248_);
lean_dec(v_toApplicative_244_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_273_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___x_264_; 
v___f_255_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__3));
v___f_256_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__4));
lean_inc_ref(v_toFunctor_248_);
v___f_257_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_257_, 0, v_toFunctor_248_);
v___f_258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_258_, 0, v_toFunctor_248_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___f_257_);
lean_ctor_set(v___x_259_, 1, v___f_258_);
v___f_260_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_260_, 0, v_toSeqRight_251_);
v___f_261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_261_, 0, v_toSeqLeft_250_);
v___f_262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_262_, 0, v_toSeq_249_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 4, v___f_260_);
lean_ctor_set(v___x_253_, 3, v___f_261_);
lean_ctor_set(v___x_253_, 2, v___f_262_);
lean_ctor_set(v___x_253_, 1, v___f_255_);
lean_ctor_set(v___x_253_, 0, v___x_259_);
v___x_264_ = v___x_253_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___f_255_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v___f_262_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v___f_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v___f_260_);
v___x_264_ = v_reuseFailAlloc_272_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___f_256_);
lean_ctor_set(v___x_246_, 0, v___x_264_);
v___x_266_ = v___x_246_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___f_256_);
v___x_266_ = v_reuseFailAlloc_271_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_8315__overap_269_; lean_object* v___x_270_; 
v___x_267_ = lean_box(0);
v___x_268_ = l_instInhabitedOfMonad___redArg(v___x_266_, v___x_267_);
v___x_8315__overap_269_ = lean_panic_fn_borrowed(v___x_268_, v_msg_212_);
lean_dec(v___x_268_);
lean_inc(v___y_216_);
lean_inc_ref(v___y_215_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
v___x_270_ = lean_apply_5(v___x_8315__overap_269_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, lean_box(0));
return v___x_270_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___boxed(lean_object* v_msg_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7(v_msg_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__0));
v___x_292_ = l_Lean_stringToMessageData(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__2));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6));
v___x_300_ = lean_unsigned_to_nat(11u);
v___x_301_ = lean_unsigned_to_nat(122u);
v___x_302_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__5));
v___x_303_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__4));
v___x_304_ = l_mkPanicMessageWithDecl(v___x_303_, v___x_302_, v___x_301_, v___x_300_, v___x_299_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4(lean_object* v_constName_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_319_; lean_object* v_env_320_; uint8_t v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_st_ref_get(v___y_309_);
v_env_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_env_320_);
lean_dec(v___x_319_);
v___x_321_ = 0;
lean_inc(v_constName_305_);
v___x_322_ = l_Lean_Environment_findAsync_x3f(v_env_320_, v_constName_305_, v___x_321_);
if (lean_obj_tag(v___x_322_) == 1)
{
lean_object* v_val_323_; uint8_t v_kind_324_; 
v_val_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_val_323_);
lean_dec_ref(v___x_322_);
v_kind_324_ = lean_ctor_get_uint8(v_val_323_, sizeof(void*)*3);
if (v_kind_324_ == 6)
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_323_);
if (lean_obj_tag(v___x_325_) == 6)
{
lean_object* v_val_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_constName_305_);
v_val_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_val_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 0);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_val_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v___x_325_);
v___x_334_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7);
v___x_335_ = l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7(v___x_334_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_344_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_344_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
if (lean_obj_tag(v_a_336_) == 0)
{
lean_del_object(v___x_338_);
goto v___jp_311_;
}
else
{
lean_object* v_val_340_; lean_object* v___x_342_; 
lean_dec(v_constName_305_);
v_val_340_ = lean_ctor_get(v_a_336_, 0);
lean_inc(v_val_340_);
lean_dec_ref(v_a_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v_val_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_val_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_constName_305_);
v_a_345_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_335_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_335_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
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
}
else
{
lean_dec(v_val_323_);
goto v___jp_311_;
}
}
else
{
lean_dec(v___x_322_);
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_312_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1);
v___x_313_ = 0;
v___x_314_ = l_Lean_MessageData_ofConstName(v_constName_305_, v___x_313_);
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_312_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(v___x_317_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___boxed(lean_object* v_constName_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4(v_constName_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_359_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__2));
v___x_364_ = lean_unsigned_to_nat(10u);
v___x_365_ = lean_unsigned_to_nat(71u);
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_368_ = l_mkPanicMessageWithDecl(v___x_367_, v___x_366_, v___x_365_, v___x_364_, v___x_363_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_369_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6));
v___x_370_ = lean_unsigned_to_nat(65u);
v___x_371_ = lean_unsigned_to_nat(80u);
v___x_372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_374_ = l_mkPanicMessageWithDecl(v___x_373_, v___x_372_, v___x_371_, v___x_370_, v___x_369_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__5));
v___x_377_ = lean_unsigned_to_nat(12u);
v___x_378_ = lean_unsigned_to_nat(76u);
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_381_ = l_mkPanicMessageWithDecl(v___x_380_, v___x_379_, v___x_378_, v___x_377_, v___x_376_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0(lean_object* v___x_382_, lean_object* v_ys_383_, lean_object* v_mr_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = l_Lean_Expr_isApp(v_mr_384_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3);
v___x_392_ = l_panic___at___00getCasesInfo_x3f_spec__3(v___x_391_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = l_Lean_Expr_appArg_x21(v_mr_384_);
v___x_394_ = l_Lean_Expr_isFVar(v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = l_Lean_Expr_getAppFn(v___x_393_);
lean_dec_ref(v___x_393_);
v___x_396_ = l_Lean_Expr_constName_x3f(v___x_395_);
lean_dec_ref(v___x_395_);
if (lean_obj_tag(v___x_396_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_398_; 
v_val_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc_n(v_val_397_, 2);
lean_dec_ref(v___x_396_);
v___x_398_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4(v_val_397_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_408_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_408_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_numFields_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v_numFields_403_ = lean_ctor_get(v_a_399_, 4);
lean_inc(v_numFields_403_);
lean_dec(v_a_399_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_val_397_);
lean_ctor_set(v___x_404_, 1, v_numFields_403_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_val_397_);
v_a_409_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_398_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_398_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec(v___x_396_);
v___x_417_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4);
v___x_418_ = l_panic___at___00getCasesInfo_x3f_spec__3(v___x_417_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_418_;
}
}
else
{
uint8_t v___x_419_; 
v___x_419_ = lean_expr_eqv(v___x_393_, v___x_382_);
lean_dec_ref(v___x_393_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6);
v___x_421_ = l_panic___at___00getCasesInfo_x3f_spec__3(v___x_420_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_array_get_size(v_ys_383_);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___boxed(lean_object* v___x_425_, lean_object* v_ys_426_, lean_object* v_mr_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0(v___x_425_, v_ys_426_, v_mr_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v_mr_427_);
lean_dec_ref(v_ys_426_);
lean_dec_ref(v___x_425_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8(lean_object* v_val_434_, lean_object* v_a_435_, lean_object* v___x_436_, size_t v_sz_437_, size_t v_i_438_, lean_object* v_bs_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
lean_dec_ref(v___x_436_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v_bs_439_);
return v___x_446_;
}
else
{
lean_object* v___f_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_v_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; 
lean_inc_ref(v___x_436_);
v___f_447_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___boxed), 8, 1);
lean_closure_set(v___f_447_, 0, v___x_436_);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = l_Lean_instInhabitedExpr;
v_v_450_ = lean_array_uget_borrowed(v_bs_439_, v_i_438_);
v___x_451_ = lean_nat_sub(v_v_450_, v_val_434_);
v___x_452_ = lean_nat_sub(v___x_451_, v___x_448_);
lean_dec(v___x_451_);
v___x_453_ = lean_array_get_borrowed(v___x_449_, v_a_435_, v___x_452_);
lean_dec(v___x_452_);
v___x_454_ = 0;
lean_inc(v___x_453_);
v___x_455_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(v___x_453_, v___f_447_, v___x_454_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; lean_object* v_bs_x27_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref(v___x_455_);
v___x_457_ = lean_unsigned_to_nat(0u);
v_bs_x27_458_ = lean_array_uset(v_bs_439_, v_i_438_, v___x_457_);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_add(v_i_438_, v___x_459_);
v___x_461_ = lean_array_uset(v_bs_x27_458_, v_i_438_, v_a_456_);
v_i_438_ = v___x_460_;
v_bs_439_ = v___x_461_;
goto _start;
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_bs_439_);
lean_dec_ref(v___x_436_);
v_a_463_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_455_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_455_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___boxed(lean_object* v_val_471_, lean_object* v_a_472_, lean_object* v___x_473_, lean_object* v_sz_474_, lean_object* v_i_475_, lean_object* v_bs_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_474_);
lean_dec(v_sz_474_);
v_i_boxed_483_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8(v_val_471_, v_a_472_, v___x_473_, v_sz_boxed_482_, v_i_boxed_483_, v_bs_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v_a_472_);
lean_dec(v_val_471_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7(lean_object* v_xs_485_, lean_object* v_v_486_, lean_object* v_i_487_){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_array_get_size(v_xs_485_);
v___x_489_ = lean_nat_dec_lt(v_i_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec(v_i_487_);
v___x_490_ = lean_box(0);
return v___x_490_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_array_fget_borrowed(v_xs_485_, v_i_487_);
v___x_492_ = lean_expr_eqv(v___x_491_, v_v_486_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_i_487_, v___x_493_);
lean_dec(v_i_487_);
v_i_487_ = v___x_494_;
goto _start;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v_i_487_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7___boxed(lean_object* v_xs_497_, lean_object* v_v_498_, lean_object* v_i_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7(v_xs_497_, v_v_498_, v_i_499_);
lean_dec_ref(v_v_498_);
lean_dec_ref(v_xs_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3(lean_object* v_xs_501_, lean_object* v_v_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7(v_xs_501_, v_v_502_, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3___boxed(lean_object* v_xs_505_, lean_object* v_v_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3(v_xs_505_, v_v_506_);
lean_dec_ref(v_v_506_);
lean_dec_ref(v_xs_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2(lean_object* v_xs_508_, lean_object* v_v_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3(v_xs_508_, v_v_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v___x_511_; 
v___x_511_ = lean_box(0);
return v___x_511_;
}
else
{
lean_object* v_val_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_val_512_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_510_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_val_512_);
lean_dec(v___x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_val_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2___boxed(lean_object* v_xs_520_, lean_object* v_v_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2(v_xs_520_, v_v_521_);
lean_dec_ref(v_v_521_);
lean_dec_ref(v_xs_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5(size_t v_sz_523_, size_t v_i_524_, lean_object* v_bs_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_lt(v_i_524_, v_sz_523_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v_bs_525_);
return v___x_532_;
}
else
{
lean_object* v_v_533_; lean_object* v___x_534_; 
v_v_533_ = lean_array_uget_borrowed(v_bs_525_, v_i_524_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
lean_inc(v___y_527_);
lean_inc_ref(v___y_526_);
lean_inc(v_v_533_);
v___x_534_ = lean_infer_type(v_v_533_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; lean_object* v_bs_x27_537_; size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref(v___x_534_);
v___x_536_ = lean_unsigned_to_nat(0u);
v_bs_x27_537_ = lean_array_uset(v_bs_525_, v_i_524_, v___x_536_);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_i_524_, v___x_538_);
v___x_540_ = lean_array_uset(v_bs_x27_537_, v_i_524_, v_a_535_);
v_i_524_ = v___x_539_;
v_bs_525_ = v___x_540_;
goto _start;
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v_bs_525_);
v_a_542_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_534_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_534_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5___boxed(lean_object* v_sz_550_, lean_object* v_i_551_, lean_object* v_bs_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_550_);
lean_dec(v_sz_550_);
v_i_boxed_559_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5(v_sz_boxed_558_, v_i_boxed_559_, v_bs_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7___redArg(lean_object* v_a_561_, lean_object* v_b_562_){
_start:
{
lean_object* v_next_563_; 
v_next_563_ = lean_ctor_get(v_a_561_, 0);
lean_inc(v_next_563_);
if (lean_obj_tag(v_next_563_) == 0)
{
lean_dec_ref(v_a_561_);
return v_b_562_;
}
else
{
lean_object* v_upperBound_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_584_; 
v_upperBound_564_ = lean_ctor_get(v_a_561_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_561_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_a_561_, 0);
lean_dec(v_unused_585_);
v___x_566_ = v_a_561_;
v_isShared_567_ = v_isSharedCheck_584_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_upperBound_564_);
lean_dec(v_a_561_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_584_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_val_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_583_; 
v_val_568_ = lean_ctor_get(v_next_563_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_next_563_);
if (v_isSharedCheck_583_ == 0)
{
v___x_570_ = v_next_563_;
v_isShared_571_ = v_isSharedCheck_583_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_val_568_);
lean_dec(v_next_563_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_583_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint8_t v___x_572_; 
v___x_572_ = lean_nat_dec_lt(v_val_568_, v_upperBound_564_);
if (v___x_572_ == 0)
{
lean_del_object(v___x_570_);
lean_dec(v_val_568_);
lean_del_object(v___x_566_);
lean_dec(v_upperBound_564_);
return v_b_562_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_add(v_val_568_, v___x_573_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_574_);
v___x_576_ = v___x_570_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_582_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_576_);
v___x_578_ = v___x_566_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_upperBound_564_);
v___x_578_ = v_reuseFailAlloc_581_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; 
v___x_579_ = lean_array_push(v_b_562_, v_val_568_);
v_a_561_ = v___x_578_;
v_b_562_ = v___x_579_;
goto _start;
}
}
}
}
}
}
}
}
static lean_object* _init_l_getCasesInfo_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_587_ = ((lean_object*)(l_getCasesInfo_x3f___lam__0___closed__0));
v___x_588_ = lean_unsigned_to_nat(6u);
v___x_589_ = lean_unsigned_to_nat(60u);
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_592_ = l_mkPanicMessageWithDecl(v___x_591_, v___x_590_, v___x_589_, v___x_588_, v___x_587_);
return v___x_592_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = ((lean_object*)(l_getCasesInfo_x3f___lam__0___closed__2));
v___x_595_ = lean_unsigned_to_nat(6u);
v___x_596_ = lean_unsigned_to_nat(61u);
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_599_ = l_mkPanicMessageWithDecl(v___x_598_, v___x_597_, v___x_596_, v___x_595_, v___x_594_);
return v___x_599_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = ((lean_object*)(l_getCasesInfo_x3f___lam__0___closed__4));
v___x_602_ = lean_unsigned_to_nat(6u);
v___x_603_ = lean_unsigned_to_nat(62u);
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_606_ = l_mkPanicMessageWithDecl(v___x_605_, v___x_604_, v___x_603_, v___x_602_, v___x_601_);
return v___x_606_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___lam__0___closed__7(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_609_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6));
v___x_610_ = lean_unsigned_to_nat(76u);
v___x_611_ = lean_unsigned_to_nat(64u);
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_614_ = l_mkPanicMessageWithDecl(v___x_613_, v___x_612_, v___x_611_, v___x_610_, v___x_609_);
return v___x_614_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___lam__0___closed__8(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_615_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6));
v___x_616_ = lean_unsigned_to_nat(49u);
v___x_617_ = lean_unsigned_to_nat(63u);
v___x_618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_620_ = l_mkPanicMessageWithDecl(v___x_619_, v___x_618_, v___x_617_, v___x_616_, v___x_615_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_getCasesInfo_x3f___lam__0(lean_object* v_declName_621_, lean_object* v_xs_622_, lean_object* v_r_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = l_Lean_Expr_isApp(v_r_623_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v_declName_621_);
v___x_630_ = lean_obj_once(&l_getCasesInfo_x3f___lam__0___closed__1, &l_getCasesInfo_x3f___lam__0___closed__1_once, _init_l_getCasesInfo_x3f___lam__0___closed__1);
v___x_631_ = l_panic___at___00getCasesInfo_x3f_spec__1(v___x_630_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = l_Lean_Expr_appArg_x21(v_r_623_);
v___x_633_ = l_Lean_Expr_isFVar(v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v___x_632_);
lean_dec(v_declName_621_);
v___x_634_ = lean_obj_once(&l_getCasesInfo_x3f___lam__0___closed__3, &l_getCasesInfo_x3f___lam__0___closed__3_once, _init_l_getCasesInfo_x3f___lam__0___closed__3);
v___x_635_ = l_panic___at___00getCasesInfo_x3f_spec__1(v___x_634_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = l_Lean_Expr_getAppFn(v_r_623_);
v___x_637_ = l_Lean_Expr_isFVar(v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_632_);
lean_dec(v_declName_621_);
v___x_638_ = lean_obj_once(&l_getCasesInfo_x3f___lam__0___closed__5, &l_getCasesInfo_x3f___lam__0___closed__5_once, _init_l_getCasesInfo_x3f___lam__0___closed__5);
v___x_639_ = l_panic___at___00getCasesInfo_x3f_spec__1(v___x_638_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2(v_xs_622_, v___x_632_);
lean_dec_ref(v___x_632_);
if (lean_obj_tag(v___x_640_) == 1)
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_722_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_722_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_722_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_722_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_instInhabitedExpr;
v___x_646_ = lean_array_get_borrowed(v___x_645_, v_xs_622_, v_val_641_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
lean_inc(v___y_625_);
lean_inc_ref(v___y_624_);
lean_inc(v___x_646_);
v___x_647_ = lean_infer_type(v___x_646_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
v___x_649_ = l_Lean_Expr_getAppFn(v_a_648_);
lean_dec(v_a_648_);
v___x_650_ = l_Lean_Expr_constName_x3f(v___x_649_);
lean_dec_ref(v___x_649_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_711_; 
v_val_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_711_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_711_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_711_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; size_t v_sz_659_; size_t v___x_660_; lean_object* v___x_661_; 
v___x_655_ = lean_array_get_size(v_xs_622_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_val_641_, v___x_656_);
v___x_658_ = l_Array_extract___redArg(v_xs_622_, v___x_657_, v___x_655_);
v_sz_659_ = lean_array_size(v___x_658_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5(v_sz_659_, v___x_660_, v___x_658_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___y_664_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref(v___x_661_);
v___x_695_ = lean_array_get_size(v_a_662_);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_nat_dec_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
if (v___x_637_ == 0)
{
lean_dec_ref(v___x_636_);
v___y_664_ = v___x_656_;
goto v___jp_663_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_698_ = lean_array_get_borrowed(v___x_645_, v_a_662_, v___x_696_);
v___x_699_ = l_Lean_Expr_getForallBody(v___x_698_);
v___x_700_ = l_Lean_Expr_getAppFn(v___x_699_);
lean_dec_ref(v___x_699_);
v___x_701_ = lean_expr_eqv(v___x_700_, v___x_636_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_unsigned_to_nat(2u);
v___y_664_ = v___x_702_;
goto v___jp_663_;
}
else
{
v___y_664_ = v___x_656_;
goto v___jp_663_;
}
}
}
else
{
lean_dec_ref(v___x_636_);
v___y_664_ = v___x_656_;
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_665_ = lean_nat_add(v_val_641_, v___y_664_);
lean_inc(v___x_665_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___x_655_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_665_);
v___x_668_ = v___x_653_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_665_);
v___x_668_ = v_reuseFailAlloc_694_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; size_t v_sz_672_; lean_object* v___x_673_; 
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_655_);
v___x_670_ = ((lean_object*)(l_getCasesInfo_x3f___lam__0___closed__6));
v___x_671_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7___redArg(v___x_669_, v___x_670_);
v_sz_672_ = lean_array_size(v___x_671_);
lean_inc(v___x_646_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8(v_val_641_, v_a_662_, v___x_646_, v_sz_672_, v___x_660_, v___x_671_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v_a_662_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_685_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_685_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_685_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_685_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_678_, 0, v_declName_621_);
lean_ctor_set(v___x_678_, 1, v_val_651_);
lean_ctor_set(v___x_678_, 2, v___x_655_);
lean_ctor_set(v___x_678_, 3, v_val_641_);
lean_ctor_set(v___x_678_, 4, v___x_666_);
lean_ctor_set(v___x_678_, 5, v_a_674_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_678_);
v___x_680_ = v___x_643_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_680_);
v___x_682_ = v___x_676_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
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
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v___x_666_);
lean_dec(v_val_651_);
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec(v_declName_621_);
v_a_686_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_673_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_673_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_del_object(v___x_653_);
lean_dec(v_val_651_);
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec_ref(v___x_636_);
lean_dec(v_declName_621_);
v_a_703_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_661_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_661_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v___x_650_);
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec_ref(v___x_636_);
lean_dec(v_declName_621_);
v___x_712_ = lean_obj_once(&l_getCasesInfo_x3f___lam__0___closed__7, &l_getCasesInfo_x3f___lam__0___closed__7_once, _init_l_getCasesInfo_x3f___lam__0___closed__7);
v___x_713_ = l_panic___at___00getCasesInfo_x3f_spec__1(v___x_712_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_713_;
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec_ref(v___x_636_);
lean_dec(v_declName_621_);
v_a_714_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_647_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_647_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec(v___x_640_);
lean_dec_ref(v___x_636_);
lean_dec(v_declName_621_);
v___x_723_ = lean_obj_once(&l_getCasesInfo_x3f___lam__0___closed__8, &l_getCasesInfo_x3f___lam__0___closed__8_once, _init_l_getCasesInfo_x3f___lam__0___closed__8);
v___x_724_ = l_panic___at___00getCasesInfo_x3f_spec__1(v___x_723_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCasesInfo_x3f___lam__0___boxed(lean_object* v_declName_725_, lean_object* v_xs_726_, lean_object* v_r_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_getCasesInfo_x3f___lam__0(v_declName_725_, v_xs_726_, v_r_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec_ref(v_r_727_);
lean_dec_ref(v_xs_726_);
return v_res_733_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_734_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
lean_ctor_set(v___x_739_, 2, v___x_738_);
lean_ctor_set(v___x_739_, 3, v___x_738_);
lean_ctor_set(v___x_739_, 4, v___x_737_);
lean_ctor_set(v___x_739_, 5, v___x_737_);
lean_ctor_set(v___x_739_, 6, v___x_737_);
lean_ctor_set(v___x_739_, 7, v___x_737_);
lean_ctor_set(v___x_739_, 8, v___x_737_);
lean_ctor_set(v___x_739_, 9, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_unsigned_to_nat(32u);
v___x_741_ = lean_mk_empty_array_with_capacity(v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4(void){
_start:
{
size_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_743_ = ((size_t)5ULL);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_unsigned_to_nat(32u);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_745_);
v___x_747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3);
v___x_748_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v___x_746_);
lean_ctor_set(v___x_748_, 2, v___x_744_);
lean_ctor_set(v___x_748_, 3, v___x_744_);
lean_ctor_set_usize(v___x_748_, 4, v___x_743_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_box(1);
v___x_750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4);
v___x_751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1);
v___x_752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
lean_ctor_set(v___x_752_, 2, v___x_749_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__14));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__16));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__18));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(lean_object* v_msg_774_, lean_object* v_declHint_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v_env_779_; uint8_t v___x_780_; 
v___x_778_ = lean_st_ref_get(v___y_776_);
v_env_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc_ref(v_env_779_);
lean_dec(v___x_778_);
v___x_780_ = l_Lean_Name_isAnonymous(v_declHint_775_);
if (v___x_780_ == 0)
{
uint8_t v_isExporting_781_; 
v_isExporting_781_ = lean_ctor_get_uint8(v_env_779_, sizeof(void*)*8);
if (v_isExporting_781_ == 0)
{
lean_object* v___x_782_; 
lean_dec_ref(v_env_779_);
lean_dec(v_declHint_775_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v_msg_774_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; uint8_t v___x_784_; 
lean_inc_ref(v_env_779_);
v___x_783_ = l_Lean_Environment_setExporting(v_env_779_, v___x_780_);
lean_inc(v_declHint_775_);
lean_inc_ref(v___x_783_);
v___x_784_ = l_Lean_Environment_contains(v___x_783_, v_declHint_775_, v_isExporting_781_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec_ref(v___x_783_);
lean_dec_ref(v_env_779_);
lean_dec(v_declHint_775_);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v_msg_774_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v_c_791_; lean_object* v___x_792_; 
v___x_786_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2);
v___x_787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5);
v___x_788_ = l_Lean_Options_empty;
v___x_789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_789_, 0, v___x_783_);
lean_ctor_set(v___x_789_, 1, v___x_786_);
lean_ctor_set(v___x_789_, 2, v___x_787_);
lean_ctor_set(v___x_789_, 3, v___x_788_);
lean_inc(v_declHint_775_);
v___x_790_ = l_Lean_MessageData_ofConstName(v_declHint_775_, v___x_780_);
v_c_791_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_791_, 0, v___x_789_);
lean_ctor_set(v_c_791_, 1, v___x_790_);
v___x_792_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_779_, v_declHint_775_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_env_779_);
lean_dec(v_declHint_775_);
v___x_793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v_c_791_);
v___x_795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_MessageData_note(v___x_796_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v_msg_774_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_835_; 
v_val_800_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_835_ == 0)
{
v___x_802_ = v___x_792_;
v_isShared_803_ = v_isSharedCheck_835_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v___x_792_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_835_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_mod_807_; uint8_t v___x_808_; 
v___x_804_ = lean_box(0);
v___x_805_ = l_Lean_Environment_header(v_env_779_);
lean_dec_ref(v_env_779_);
v___x_806_ = l_Lean_EnvironmentHeader_moduleNames(v___x_805_);
v_mod_807_ = lean_array_get(v___x_804_, v___x_806_, v_val_800_);
lean_dec(v_val_800_);
lean_dec_ref(v___x_806_);
v___x_808_ = l_Lean_isPrivateName(v_declHint_775_);
lean_dec(v_declHint_775_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v_c_791_);
v___x_811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_MessageData_ofName(v_mod_807_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_MessageData_note(v___x_816_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v_msg_774_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 0);
lean_ctor_set(v___x_802_, 0, v___x_818_);
v___x_820_ = v___x_802_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v_c_791_);
v___x_824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_MessageData_ofName(v_mod_807_);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_MessageData_note(v___x_829_);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v_msg_774_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 0);
lean_ctor_set(v___x_802_, 0, v___x_831_);
v___x_833_ = v___x_802_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_836_; 
lean_dec_ref(v_env_779_);
lean_dec(v_declHint_775_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_msg_774_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___boxed(lean_object* v_msg_837_, lean_object* v_declHint_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_837_, v_declHint_838_, v___y_839_);
lean_dec(v___y_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(lean_object* v_msg_842_, lean_object* v_declHint_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_857_; 
v___x_847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_842_, v_declHint_843_, v___y_845_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_857_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_857_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_857_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_852_ = l_Lean_unknownIdentifierMessageTag;
v___x_853_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_a_848_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_853_);
v___x_855_ = v___x_850_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15___boxed(lean_object* v_msg_858_, lean_object* v_declHint_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(v_msg_858_, v_declHint_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(lean_object* v_msgData_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v_env_869_; lean_object* v_options_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_868_ = lean_st_ref_get(v___y_866_);
v_env_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc_ref(v_env_869_);
lean_dec(v___x_868_);
v_options_870_ = lean_ctor_get(v___y_865_, 2);
v___x_871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2);
v___x_872_ = lean_unsigned_to_nat(32u);
v___x_873_ = lean_mk_empty_array_with_capacity(v___x_872_);
lean_dec_ref(v___x_873_);
v___x_874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5);
lean_inc_ref(v_options_870_);
v___x_875_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_875_, 0, v_env_869_);
lean_ctor_set(v___x_875_, 1, v___x_871_);
lean_ctor_set(v___x_875_, 2, v___x_874_);
lean_ctor_set(v___x_875_, 3, v_options_870_);
v___x_876_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_msgData_864_);
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___boxed(lean_object* v_msgData_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(v_msgData_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_ref_887_; lean_object* v___x_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_897_; 
v_ref_887_ = lean_ctor_get(v___y_884_, 5);
v___x_888_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(v_msg_883_, v___y_884_, v___y_885_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_897_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
lean_inc(v_ref_887_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_ref_887_);
lean_ctor_set(v___x_893_, 1, v_a_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 1);
lean_ctor_set(v___x_891_, 0, v___x_893_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg___boxed(lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(lean_object* v_ref_903_, lean_object* v_msg_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_fileName_908_; lean_object* v_fileMap_909_; lean_object* v_options_910_; lean_object* v_currRecDepth_911_; lean_object* v_maxRecDepth_912_; lean_object* v_ref_913_; lean_object* v_currNamespace_914_; lean_object* v_openDecls_915_; lean_object* v_initHeartbeats_916_; lean_object* v_maxHeartbeats_917_; lean_object* v_quotContext_918_; lean_object* v_currMacroScope_919_; uint8_t v_diag_920_; lean_object* v_cancelTk_x3f_921_; uint8_t v_suppressElabErrors_922_; lean_object* v_inheritedTraceOptions_923_; lean_object* v_ref_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_fileName_908_ = lean_ctor_get(v___y_905_, 0);
v_fileMap_909_ = lean_ctor_get(v___y_905_, 1);
v_options_910_ = lean_ctor_get(v___y_905_, 2);
v_currRecDepth_911_ = lean_ctor_get(v___y_905_, 3);
v_maxRecDepth_912_ = lean_ctor_get(v___y_905_, 4);
v_ref_913_ = lean_ctor_get(v___y_905_, 5);
v_currNamespace_914_ = lean_ctor_get(v___y_905_, 6);
v_openDecls_915_ = lean_ctor_get(v___y_905_, 7);
v_initHeartbeats_916_ = lean_ctor_get(v___y_905_, 8);
v_maxHeartbeats_917_ = lean_ctor_get(v___y_905_, 9);
v_quotContext_918_ = lean_ctor_get(v___y_905_, 10);
v_currMacroScope_919_ = lean_ctor_get(v___y_905_, 11);
v_diag_920_ = lean_ctor_get_uint8(v___y_905_, sizeof(void*)*14);
v_cancelTk_x3f_921_ = lean_ctor_get(v___y_905_, 12);
v_suppressElabErrors_922_ = lean_ctor_get_uint8(v___y_905_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_923_ = lean_ctor_get(v___y_905_, 13);
v_ref_924_ = l_Lean_replaceRef(v_ref_903_, v_ref_913_);
lean_inc_ref(v_inheritedTraceOptions_923_);
lean_inc(v_cancelTk_x3f_921_);
lean_inc(v_currMacroScope_919_);
lean_inc(v_quotContext_918_);
lean_inc(v_maxHeartbeats_917_);
lean_inc(v_initHeartbeats_916_);
lean_inc(v_openDecls_915_);
lean_inc(v_currNamespace_914_);
lean_inc(v_maxRecDepth_912_);
lean_inc(v_currRecDepth_911_);
lean_inc_ref(v_options_910_);
lean_inc_ref(v_fileMap_909_);
lean_inc_ref(v_fileName_908_);
v___x_925_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_925_, 0, v_fileName_908_);
lean_ctor_set(v___x_925_, 1, v_fileMap_909_);
lean_ctor_set(v___x_925_, 2, v_options_910_);
lean_ctor_set(v___x_925_, 3, v_currRecDepth_911_);
lean_ctor_set(v___x_925_, 4, v_maxRecDepth_912_);
lean_ctor_set(v___x_925_, 5, v_ref_924_);
lean_ctor_set(v___x_925_, 6, v_currNamespace_914_);
lean_ctor_set(v___x_925_, 7, v_openDecls_915_);
lean_ctor_set(v___x_925_, 8, v_initHeartbeats_916_);
lean_ctor_set(v___x_925_, 9, v_maxHeartbeats_917_);
lean_ctor_set(v___x_925_, 10, v_quotContext_918_);
lean_ctor_set(v___x_925_, 11, v_currMacroScope_919_);
lean_ctor_set(v___x_925_, 12, v_cancelTk_x3f_921_);
lean_ctor_set(v___x_925_, 13, v_inheritedTraceOptions_923_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*14, v_diag_920_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*14 + 1, v_suppressElabErrors_922_);
v___x_926_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_904_, v___x_925_, v___y_906_);
lean_dec_ref(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg___boxed(lean_object* v_ref_927_, lean_object* v_msg_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_927_, v_msg_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v_ref_927_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_933_, lean_object* v_msg_934_, lean_object* v_declHint_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_941_; 
v___x_939_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(v_msg_934_, v_declHint_935_, v___y_936_, v___y_937_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref(v___x_939_);
v___x_941_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_933_, v_a_940_, v___y_936_, v___y_937_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_942_, lean_object* v_msg_943_, lean_object* v_declHint_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_942_, v_msg_943_, v_declHint_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v_ref_942_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_952_, lean_object* v_constName_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_957_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_958_ = 0;
lean_inc(v_constName_953_);
v___x_959_ = l_Lean_MessageData_ofConstName(v_constName_953_, v___x_958_);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_957_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_952_, v___x_962_, v_constName_953_, v___y_954_, v___y_955_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_964_, lean_object* v_constName_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_964_, v_constName_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v_ref_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(lean_object* v_constName_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_ref_974_; lean_object* v___x_975_; 
v_ref_974_ = lean_ctor_get(v___y_971_, 5);
v___x_975_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_974_, v_constName_970_, v___y_971_, v___y_972_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0(lean_object* v_constName_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; lean_object* v_env_986_; uint8_t v___x_987_; lean_object* v___x_988_; 
v___x_985_ = lean_st_ref_get(v___y_983_);
v_env_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc_ref(v_env_986_);
lean_dec(v___x_985_);
v___x_987_ = 0;
lean_inc(v_constName_981_);
v___x_988_ = l_Lean_Environment_findConstVal_x3f(v_env_986_, v_constName_981_, v___x_987_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_981_, v___y_982_, v___y_983_);
return v___x_989_;
}
else
{
lean_object* v_val_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_constName_981_);
v_val_990_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_988_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_val_990_);
lean_dec(v___x_988_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_val_990_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0___boxed(lean_object* v_constName_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0(v_constName_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
return v_res_1002_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___closed__0(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1003_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l_getCasesInfo_x3f___closed__0, &l_getCasesInfo_x3f___closed__0_once, _init_l_getCasesInfo_x3f___closed__0);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___closed__2(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1006_ = lean_box(1);
v___x_1007_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4);
v___x_1008_ = lean_obj_once(&l_getCasesInfo_x3f___closed__1, &l_getCasesInfo_x3f___closed__1_once, _init_l_getCasesInfo_x3f___closed__1);
v___x_1009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_1007_);
lean_ctor_set(v___x_1009_, 2, v___x_1006_);
return v___x_1009_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___closed__4(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_obj_once(&l_getCasesInfo_x3f___closed__1, &l_getCasesInfo_x3f___closed__1_once, _init_l_getCasesInfo_x3f___closed__1);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
lean_ctor_set(v___x_1014_, 3, v___x_1013_);
lean_ctor_set(v___x_1014_, 4, v___x_1012_);
lean_ctor_set(v___x_1014_, 5, v___x_1012_);
lean_ctor_set(v___x_1014_, 6, v___x_1012_);
lean_ctor_set(v___x_1014_, 7, v___x_1012_);
lean_ctor_set(v___x_1014_, 8, v___x_1012_);
lean_ctor_set(v___x_1014_, 9, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___closed__5(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_obj_once(&l_getCasesInfo_x3f___closed__1, &l_getCasesInfo_x3f___closed__1_once, _init_l_getCasesInfo_x3f___closed__1);
v___x_1016_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
lean_ctor_set(v___x_1016_, 3, v___x_1015_);
lean_ctor_set(v___x_1016_, 4, v___x_1015_);
lean_ctor_set(v___x_1016_, 5, v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___closed__6(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_obj_once(&l_getCasesInfo_x3f___closed__1, &l_getCasesInfo_x3f___closed__1_once, _init_l_getCasesInfo_x3f___closed__1);
v___x_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_ctor_set(v___x_1018_, 2, v___x_1017_);
lean_ctor_set(v___x_1018_, 3, v___x_1017_);
lean_ctor_set(v___x_1018_, 4, v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l_getCasesInfo_x3f___closed__7(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1019_ = lean_obj_once(&l_getCasesInfo_x3f___closed__6, &l_getCasesInfo_x3f___closed__6_once, _init_l_getCasesInfo_x3f___closed__6);
v___x_1020_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4);
v___x_1021_ = lean_box(1);
v___x_1022_ = lean_obj_once(&l_getCasesInfo_x3f___closed__5, &l_getCasesInfo_x3f___closed__5_once, _init_l_getCasesInfo_x3f___closed__5);
v___x_1023_ = lean_obj_once(&l_getCasesInfo_x3f___closed__4, &l_getCasesInfo_x3f___closed__4_once, _init_l_getCasesInfo_x3f___closed__4);
v___x_1024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_1022_);
lean_ctor_set(v___x_1024_, 2, v___x_1021_);
lean_ctor_set(v___x_1024_, 3, v___x_1020_);
lean_ctor_set(v___x_1024_, 4, v___x_1019_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_getCasesInfo_x3f(lean_object* v_declName_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v_env_1030_; uint8_t v___x_1031_; 
v___x_1029_ = lean_st_ref_get(v_a_1027_);
v_env_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_env_1030_);
lean_dec(v___x_1029_);
lean_inc(v_declName_1025_);
v___x_1031_ = l_Lean_isCasesOnLike(v_env_1030_, v_declName_1025_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v_declName_1025_);
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; 
lean_inc(v_declName_1025_);
v___x_1034_ = l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0(v_declName_1025_, v_a_1026_, v_a_1027_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; uint8_t v___x_1036_; uint8_t v___x_1037_; uint8_t v___x_1038_; uint8_t v___x_1039_; lean_object* v___x_1040_; uint64_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_type_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = 0;
v___x_1037_ = 1;
v___x_1038_ = 0;
v___x_1039_ = 2;
v___x_1040_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1040_, 0, v___x_1036_);
lean_ctor_set_uint8(v___x_1040_, 1, v___x_1036_);
lean_ctor_set_uint8(v___x_1040_, 2, v___x_1036_);
lean_ctor_set_uint8(v___x_1040_, 3, v___x_1036_);
lean_ctor_set_uint8(v___x_1040_, 4, v___x_1036_);
lean_ctor_set_uint8(v___x_1040_, 5, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 6, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 7, v___x_1036_);
lean_ctor_set_uint8(v___x_1040_, 8, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 9, v___x_1037_);
lean_ctor_set_uint8(v___x_1040_, 10, v___x_1038_);
lean_ctor_set_uint8(v___x_1040_, 11, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 12, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 13, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 14, v___x_1039_);
lean_ctor_set_uint8(v___x_1040_, 15, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 16, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 17, v___x_1031_);
lean_ctor_set_uint8(v___x_1040_, 18, v___x_1031_);
v___x_1041_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1040_);
v___x_1042_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set_uint64(v___x_1042_, sizeof(void*)*1, v___x_1041_);
v___x_1043_ = lean_box(1);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_obj_once(&l_getCasesInfo_x3f___closed__2, &l_getCasesInfo_x3f___closed__2_once, _init_l_getCasesInfo_x3f___closed__2);
v___x_1046_ = ((lean_object*)(l_getCasesInfo_x3f___closed__3));
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1048_, 0, v___x_1042_);
lean_ctor_set(v___x_1048_, 1, v___x_1043_);
lean_ctor_set(v___x_1048_, 2, v___x_1045_);
lean_ctor_set(v___x_1048_, 3, v___x_1046_);
lean_ctor_set(v___x_1048_, 4, v___x_1047_);
lean_ctor_set(v___x_1048_, 5, v___x_1044_);
lean_ctor_set(v___x_1048_, 6, v___x_1047_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*7, v___x_1036_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*7 + 1, v___x_1036_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*7 + 2, v___x_1036_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*7 + 3, v___x_1031_);
v___x_1049_ = lean_obj_once(&l_getCasesInfo_x3f___closed__7, &l_getCasesInfo_x3f___closed__7_once, _init_l_getCasesInfo_x3f___closed__7);
v___x_1050_ = lean_st_mk_ref(v___x_1049_);
v_type_1051_ = lean_ctor_get(v_a_1035_, 2);
lean_inc_ref(v_type_1051_);
lean_dec(v_a_1035_);
v___f_1052_ = lean_alloc_closure((void*)(l_getCasesInfo_x3f___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1052_, 0, v_declName_1025_);
v___x_1053_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(v_type_1051_, v___f_1052_, v___x_1036_, v___x_1048_, v___x_1050_, v_a_1026_, v_a_1027_);
lean_dec_ref(v___x_1048_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1062_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1062_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1062_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = lean_st_ref_get(v___x_1050_);
lean_dec(v___x_1050_);
lean_dec(v___x_1058_);
if (v_isShared_1057_ == 0)
{
v___x_1060_ = v___x_1056_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1054_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_dec(v___x_1050_);
return v___x_1053_;
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_declName_1025_);
v_a_1063_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1034_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1034_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCasesInfo_x3f___boxed(lean_object* v_declName_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_getCasesInfo_x3f(v_declName_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7(lean_object* v_inst_1076_, lean_object* v_R_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7___redArg(v_a_1078_, v_b_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b1_1081_, lean_object* v_constName_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_1082_, v___y_1083_, v___y_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1087_, lean_object* v_constName_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0(v_00_u03b1_1087_, v_constName_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6(lean_object* v_00_u03b1_1093_, lean_object* v_msg_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(v_msg_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1101_, lean_object* v_msg_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6(v_00_u03b1_1101_, v_msg_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_1109_, lean_object* v_ref_1110_, lean_object* v_constName_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_1110_, v_constName_1111_, v___y_1112_, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_ref_1117_, lean_object* v_constName_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4(v_00_u03b1_1116_, v_ref_1117_, v_constName_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v_ref_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_1123_, lean_object* v_ref_1124_, lean_object* v_msg_1125_, lean_object* v_declHint_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1124_, v_msg_1125_, v_declHint_1126_, v___y_1127_, v___y_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_ref_1132_, lean_object* v_msg_1133_, lean_object* v_declHint_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_1131_, v_ref_1132_, v_msg_1133_, v_declHint_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v_ref_1132_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17(lean_object* v_msg_1139_, lean_object* v_declHint_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_1139_, v_declHint_1140_, v___y_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___boxed(lean_object* v_msg_1145_, lean_object* v_declHint_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17(v_msg_1145_, v_declHint_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16(lean_object* v_00_u03b1_1151_, lean_object* v_ref_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_1152_, v_msg_1153_, v___y_1154_, v___y_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_ref_1159_, lean_object* v_msg_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16(v_00_u03b1_1158_, v_ref_1159_, v_msg_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v_ref_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19(lean_object* v_00_u03b1_1165_, lean_object* v_msg_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_1166_, v___y_1167_, v___y_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_msg_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19(v_00_u03b1_1171_, v_msg_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1176_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CasesInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CasesInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CasesInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CasesInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CasesInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CasesInfo(builtin);
}
#ifdef __cplusplus
}
#endif
