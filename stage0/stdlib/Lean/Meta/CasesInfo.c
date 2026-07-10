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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnLike(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_default_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_default_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedCasesAltInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedCasesAltInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedCasesAltInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedCasesAltInfo_default = (const lean_object*)&l_Lean_instInhabitedCasesAltInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedCasesAltInfo = (const lean_object*)&l_Lean_instInhabitedCasesAltInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_CasesInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesInfo_numAlts___boxed(lean_object*);
static const lean_closure_object l_panic___at___00Lean_getCasesInfo_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_getCasesInfo_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.CasesInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.getCasesInfo\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: mr.isApp\n          "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "assertion violation: motiveArg == xs[discrPos]!\n            "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__7___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_getCasesInfo_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "assertion violation: r.isApp\n      "};
static const lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_getCasesInfo_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__1;
static const lean_string_object l_Lean_getCasesInfo_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "assertion violation: r.appArg!.isFVar  -- major argument\n      "};
static const lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_getCasesInfo_x3f___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__3;
static const lean_string_object l_Lean_getCasesInfo_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "assertion violation: r.getAppFn.isFVar -- motive\n      "};
static const lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__4 = (const lean_object*)&l_Lean_getCasesInfo_x3f___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__5;
static const lean_array_object l_Lean_getCasesInfo_x3f___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__6 = (const lean_object*)&l_Lean_getCasesInfo_x3f___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__7;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__0;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__1;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__2;
static const lean_array_object l_Lean_getCasesInfo_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getCasesInfo_x3f___closed__3 = (const lean_object*)&l_Lean_getCasesInfo_x3f___closed__3_value;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__4;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__5;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__6;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_CasesAltInfo_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_ctorName_8_; lean_object* v_numFields_9_; lean_object* v___x_10_; 
v_ctorName_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_ctorName_8_);
v_numFields_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_numFields_9_);
lean_dec_ref_known(v_t_6_, 2);
v___x_10_ = lean_apply_2(v_k_7_, v_ctorName_8_, v_numFields_9_);
return v___x_10_;
}
else
{
lean_object* v_numHyps_11_; lean_object* v___x_12_; 
v_numHyps_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_numHyps_11_);
lean_dec_ref_known(v_t_6_, 1);
v___x_12_ = lean_apply_1(v_k_7_, v_numHyps_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_CasesAltInfo_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctor_elim___redArg(lean_object* v_t_25_, lean_object* v_ctor_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_25_, v_ctor_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctor_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_ctor_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_29_, v_ctor_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_default_elim___redArg(lean_object* v_t_33_, lean_object* v_default_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_33_, v_default_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_default_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_default_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_37_, v_default_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesInfo_numAlts(lean_object* v_c_46_){
_start:
{
lean_object* v_altNumParams_47_; lean_object* v___x_48_; 
v_altNumParams_47_ = lean_ctor_get(v_c_46_, 5);
v___x_48_ = lean_array_get_size(v_altNumParams_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesInfo_numAlts___boxed(lean_object* v_c_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_CasesInfo_numAlts(v_c_49_);
lean_dec_ref(v_c_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__1(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_6218__overap_59_; lean_object* v___x_60_; 
v___f_58_ = ((lean_object*)(l_panic___at___00Lean_getCasesInfo_x3f_spec__1___closed__0));
v___x_6218__overap_59_ = lean_panic_fn_borrowed(v___f_58_, v_msg_52_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
v___x_60_ = lean_apply_5(v___x_6218__overap_59_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, lean_box(0));
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__1___boxed(lean_object* v_msg_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__1(v_msg_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__3(lean_object* v_msg_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_6240__overap_75_; lean_object* v___x_76_; 
v___f_74_ = ((lean_object*)(l_panic___at___00Lean_getCasesInfo_x3f_spec__1___closed__0));
v___x_6240__overap_75_ = lean_panic_fn_borrowed(v___f_74_, v_msg_68_);
lean_inc(v___y_72_);
lean_inc_ref(v___y_71_);
lean_inc(v___y_70_);
lean_inc_ref(v___y_69_);
v___x_76_ = lean_apply_5(v___x_6240__overap_75_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, lean_box(0));
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__3___boxed(lean_object* v_msg_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__3(v_msg_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg___lam__0(lean_object* v_k_84_, lean_object* v_b_85_, lean_object* v_c_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg___lam__0___boxed(lean_object* v_k_93_, lean_object* v_b_94_, lean_object* v_c_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg___lam__0(v_k_93_, v_b_94_, v_c_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg(lean_object* v_type_102_, lean_object* v_k_103_, uint8_t v_cleanupAnnotations_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___f_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___f_110_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg___boxed(lean_object* v_type_130_, lean_object* v_k_131_, lean_object* v_cleanupAnnotations_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_138_; lean_object* v_res_139_; 
v_cleanupAnnotations_boxed_138_ = lean_unbox(v_cleanupAnnotations_132_);
v_res_139_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg(v_type_130_, v_k_131_, v_cleanupAnnotations_boxed_138_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6(lean_object* v_00_u03b1_140_, lean_object* v_type_141_, lean_object* v_k_142_, uint8_t v_cleanupAnnotations_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg(v_type_141_, v_k_142_, v_cleanupAnnotations_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___boxed(lean_object* v_00_u03b1_150_, lean_object* v_type_151_, lean_object* v_k_152_, lean_object* v_cleanupAnnotations_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_159_; lean_object* v_res_160_; 
v_cleanupAnnotations_boxed_159_ = lean_unbox(v_cleanupAnnotations_153_);
v_res_160_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6(v_00_u03b1_150_, v_type_151_, v_k_152_, v_cleanupAnnotations_boxed_159_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__5(size_t v_sz_161_, size_t v_i_162_, lean_object* v_bs_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = lean_usize_dec_lt(v_i_162_, v_sz_161_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v_bs_163_);
return v___x_170_;
}
else
{
lean_object* v_v_171_; lean_object* v___x_172_; 
v_v_171_ = lean_array_uget_borrowed(v_bs_163_, v_i_162_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v_v_171_);
v___x_172_ = lean_infer_type(v_v_171_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v_bs_x27_175_; size_t v___x_176_; size_t v___x_177_; lean_object* v___x_178_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = lean_unsigned_to_nat(0u);
v_bs_x27_175_ = lean_array_uset(v_bs_163_, v_i_162_, v___x_174_);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_add(v_i_162_, v___x_176_);
v___x_178_ = lean_array_uset(v_bs_x27_175_, v_i_162_, v_a_173_);
v_i_162_ = v___x_177_;
v_bs_163_ = v___x_178_;
goto _start;
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec_ref(v_bs_163_);
v_a_180_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_172_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_172_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__5___boxed(lean_object* v_sz_188_, lean_object* v_i_189_, lean_object* v_bs_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
size_t v_sz_boxed_196_; size_t v_i_boxed_197_; lean_object* v_res_198_; 
v_sz_boxed_196_ = lean_unbox_usize(v_sz_188_);
lean_dec(v_sz_188_);
v_i_boxed_197_ = lean_unbox_usize(v_i_189_);
lean_dec(v_i_189_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__5(v_sz_boxed_196_, v_i_boxed_197_, v_bs_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_198_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_instMonadEIO(lean_box(0));
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7(lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_toApplicative_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_273_; 
v___x_210_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__0);
v___x_211_ = l_StateRefT_x27_instMonad___redArg(v___x_210_);
v_toApplicative_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_211_, 1);
lean_dec(v_unused_274_);
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_273_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_toApplicative_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_273_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_toFunctor_216_; lean_object* v_toSeq_217_; lean_object* v_toSeqLeft_218_; lean_object* v_toSeqRight_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_271_; 
v_toFunctor_216_ = lean_ctor_get(v_toApplicative_212_, 0);
v_toSeq_217_ = lean_ctor_get(v_toApplicative_212_, 2);
v_toSeqLeft_218_ = lean_ctor_get(v_toApplicative_212_, 3);
v_toSeqRight_219_ = lean_ctor_get(v_toApplicative_212_, 4);
v_isSharedCheck_271_ = !lean_is_exclusive(v_toApplicative_212_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v_toApplicative_212_, 1);
lean_dec(v_unused_272_);
v___x_221_ = v_toApplicative_212_;
v_isShared_222_ = v_isSharedCheck_271_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_toSeqRight_219_);
lean_inc(v_toSeqLeft_218_);
lean_inc(v_toSeq_217_);
lean_inc(v_toFunctor_216_);
lean_dec(v_toApplicative_212_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_271_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___x_232_; 
v___f_223_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__1));
v___f_224_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__2));
lean_inc_ref(v_toFunctor_216_);
v___f_225_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_225_, 0, v_toFunctor_216_);
v___f_226_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_226_, 0, v_toFunctor_216_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___f_225_);
lean_ctor_set(v___x_227_, 1, v___f_226_);
v___f_228_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_228_, 0, v_toSeqRight_219_);
v___f_229_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_229_, 0, v_toSeqLeft_218_);
v___f_230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_230_, 0, v_toSeq_217_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 4, v___f_228_);
lean_ctor_set(v___x_221_, 3, v___f_229_);
lean_ctor_set(v___x_221_, 2, v___f_230_);
lean_ctor_set(v___x_221_, 1, v___f_223_);
lean_ctor_set(v___x_221_, 0, v___x_227_);
v___x_232_ = v___x_221_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___f_223_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v___f_230_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v___f_229_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v___f_228_);
v___x_232_ = v_reuseFailAlloc_270_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___f_224_);
lean_ctor_set(v___x_214_, 0, v___x_232_);
v___x_234_ = v___x_214_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___f_224_);
v___x_234_ = v_reuseFailAlloc_269_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v_toApplicative_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_267_; 
v___x_235_ = l_StateRefT_x27_instMonad___redArg(v___x_234_);
v_toApplicative_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_235_, 1);
lean_dec(v_unused_268_);
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_267_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toApplicative_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_267_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_toFunctor_240_; lean_object* v_toSeq_241_; lean_object* v_toSeqLeft_242_; lean_object* v_toSeqRight_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_265_; 
v_toFunctor_240_ = lean_ctor_get(v_toApplicative_236_, 0);
v_toSeq_241_ = lean_ctor_get(v_toApplicative_236_, 2);
v_toSeqLeft_242_ = lean_ctor_get(v_toApplicative_236_, 3);
v_toSeqRight_243_ = lean_ctor_get(v_toApplicative_236_, 4);
v_isSharedCheck_265_ = !lean_is_exclusive(v_toApplicative_236_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v_toApplicative_236_, 1);
lean_dec(v_unused_266_);
v___x_245_ = v_toApplicative_236_;
v_isShared_246_ = v_isSharedCheck_265_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_toSeqRight_243_);
lean_inc(v_toSeqLeft_242_);
lean_inc(v_toSeq_241_);
lean_inc(v_toFunctor_240_);
lean_dec(v_toApplicative_236_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_265_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_256_; 
v___f_247_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__3));
v___f_248_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___closed__4));
lean_inc_ref(v_toFunctor_240_);
v___f_249_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_249_, 0, v_toFunctor_240_);
v___f_250_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_250_, 0, v_toFunctor_240_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___f_249_);
lean_ctor_set(v___x_251_, 1, v___f_250_);
v___f_252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_252_, 0, v_toSeqRight_243_);
v___f_253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_253_, 0, v_toSeqLeft_242_);
v___f_254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_254_, 0, v_toSeq_241_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 4, v___f_252_);
lean_ctor_set(v___x_245_, 3, v___f_253_);
lean_ctor_set(v___x_245_, 2, v___f_254_);
lean_ctor_set(v___x_245_, 1, v___f_247_);
lean_ctor_set(v___x_245_, 0, v___x_251_);
v___x_256_ = v___x_245_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___f_247_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v___f_254_);
lean_ctor_set(v_reuseFailAlloc_264_, 3, v___f_253_);
lean_ctor_set(v_reuseFailAlloc_264_, 4, v___f_252_);
v___x_256_ = v_reuseFailAlloc_264_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___f_248_);
lean_ctor_set(v___x_238_, 0, v___x_256_);
v___x_258_ = v___x_238_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___f_248_);
v___x_258_ = v_reuseFailAlloc_263_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_8238__overap_261_; lean_object* v___x_262_; 
v___x_259_ = lean_box(0);
v___x_260_ = l_instInhabitedOfMonad___redArg(v___x_258_, v___x_259_);
v___x_8238__overap_261_ = lean_panic_fn_borrowed(v___x_260_, v_msg_204_);
lean_dec(v___x_260_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
v___x_262_ = lean_apply_5(v___x_8238__overap_261_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, lean_box(0));
return v___x_262_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7___boxed(lean_object* v_msg_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7(v_msg_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6_spec__10(lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v___x_290_; lean_object* v_mctx_291_; lean_object* v_lctx_292_; lean_object* v_options_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = lean_st_ref_get(v___y_284_);
v_mctx_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_290_);
v_lctx_292_ = lean_ctor_get(v___y_283_, 2);
v_options_293_ = lean_ctor_get(v___y_285_, 2);
lean_inc_ref(v_options_293_);
lean_inc_ref(v_lctx_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v_env_289_);
lean_ctor_set(v___x_294_, 1, v_mctx_291_);
lean_ctor_set(v___x_294_, 2, v_lctx_292_);
lean_ctor_set(v___x_294_, 3, v_options_293_);
v___x_295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_msgData_282_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6_spec__10___boxed(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6_spec__10(v_msgData_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___redArg(lean_object* v_msg_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_ref_310_; lean_object* v___x_311_; lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
v_ref_310_ = lean_ctor_get(v___y_307_, 5);
v___x_311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6_spec__10(v_msg_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_inc(v_ref_310_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_ref_310_);
lean_ctor_set(v___x_316_, 1, v_a_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 1);
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___redArg___boxed(lean_object* v_msg_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___redArg(v_msg_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__0));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__3(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__2));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__7(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__6));
v___x_338_ = lean_unsigned_to_nat(11u);
v___x_339_ = lean_unsigned_to_nat(122u);
v___x_340_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__5));
v___x_341_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__4));
v___x_342_ = l_mkPanicMessageWithDecl(v___x_341_, v___x_340_, v___x_339_, v___x_338_, v___x_337_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4(lean_object* v_constName_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_357_; lean_object* v_env_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
v___x_357_ = lean_st_ref_get(v___y_347_);
v_env_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref(v_env_358_);
lean_dec(v___x_357_);
v___x_359_ = 0;
lean_inc(v_constName_343_);
v___x_360_ = l_Lean_Environment_findAsync_x3f(v_env_358_, v_constName_343_, v___x_359_);
if (lean_obj_tag(v___x_360_) == 1)
{
lean_object* v_val_361_; uint8_t v_kind_362_; 
v_val_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_val_361_);
lean_dec_ref_known(v___x_360_, 1);
v_kind_362_ = lean_ctor_get_uint8(v_val_361_, sizeof(void*)*3);
if (v_kind_362_ == 6)
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_361_);
if (lean_obj_tag(v___x_363_) == 6)
{
lean_object* v_val_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec(v_constName_343_);
v_val_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_val_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 0);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_val_364_);
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
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec_ref(v___x_363_);
v___x_372_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__7);
v___x_373_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__7(v___x_372_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
if (lean_obj_tag(v_a_374_) == 0)
{
lean_del_object(v___x_376_);
goto v___jp_349_;
}
else
{
lean_object* v_val_378_; lean_object* v___x_380_; 
lean_dec(v_constName_343_);
v_val_378_ = lean_ctor_get(v_a_374_, 0);
lean_inc(v_val_378_);
lean_dec_ref_known(v_a_374_, 1);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_val_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_val_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_constName_343_);
v_a_383_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_373_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_373_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
else
{
lean_dec(v_val_361_);
goto v___jp_349_;
}
}
else
{
lean_dec(v___x_360_);
goto v___jp_349_;
}
v___jp_349_:
{
lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_350_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1);
v___x_351_ = 0;
v___x_352_ = l_Lean_MessageData_ofConstName(v_constName_343_, v___x_351_);
v___x_353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_350_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__3);
v___x_355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___redArg(v___x_355_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___boxed(lean_object* v_constName_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4(v_constName_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__3(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__2));
v___x_402_ = lean_unsigned_to_nat(10u);
v___x_403_ = lean_unsigned_to_nat(73u);
v___x_404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_406_ = l_mkPanicMessageWithDecl(v___x_405_, v___x_404_, v___x_403_, v___x_402_, v___x_401_);
return v___x_406_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__4(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_407_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__6));
v___x_408_ = lean_unsigned_to_nat(65u);
v___x_409_ = lean_unsigned_to_nat(82u);
v___x_410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_412_ = l_mkPanicMessageWithDecl(v___x_411_, v___x_410_, v___x_409_, v___x_408_, v___x_407_);
return v___x_412_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__6(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__5));
v___x_415_ = lean_unsigned_to_nat(12u);
v___x_416_ = lean_unsigned_to_nat(78u);
v___x_417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_419_ = l_mkPanicMessageWithDecl(v___x_418_, v___x_417_, v___x_416_, v___x_415_, v___x_414_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0(lean_object* v___x_420_, lean_object* v_ys_421_, lean_object* v_mr_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_Expr_isApp(v_mr_422_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__3);
v___x_430_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__3(v___x_429_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = l_Lean_Expr_appArg_x21(v_mr_422_);
v___x_432_ = l_Lean_Expr_isFVar(v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = l_Lean_Expr_getAppFn(v___x_431_);
lean_dec_ref(v___x_431_);
v___x_434_ = l_Lean_Expr_constName_x3f(v___x_433_);
lean_dec_ref(v___x_433_);
if (lean_obj_tag(v___x_434_) == 1)
{
lean_object* v_val_435_; lean_object* v___x_436_; 
v_val_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_n(v_val_435_, 2);
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4(v_val_435_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_446_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_446_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_numFields_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v_numFields_441_ = lean_ctor_get(v_a_437_, 4);
lean_inc(v_numFields_441_);
lean_dec(v_a_437_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_val_435_);
lean_ctor_set(v___x_442_, 1, v_numFields_441_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_val_435_);
v_a_447_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_436_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_436_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v___x_434_);
v___x_455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__4);
v___x_456_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__3(v___x_455_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
return v___x_456_;
}
}
else
{
uint8_t v___x_457_; 
v___x_457_ = lean_expr_eqv(v___x_431_, v___x_420_);
lean_dec_ref(v___x_431_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__6);
v___x_459_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__3(v___x_458_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_array_get_size(v_ys_421_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___boxed(lean_object* v___x_463_, lean_object* v_ys_464_, lean_object* v_mr_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0(v___x_463_, v_ys_464_, v_mr_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec_ref(v_mr_465_);
lean_dec_ref(v_ys_464_);
lean_dec_ref(v___x_463_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8(lean_object* v_val_472_, lean_object* v_a_473_, lean_object* v___x_474_, size_t v_sz_475_, size_t v_i_476_, lean_object* v_bs_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_476_, v_sz_475_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec_ref(v___x_474_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v_bs_477_);
return v___x_484_;
}
else
{
lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_v_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; 
lean_inc_ref(v___x_474_);
v___f_485_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___boxed), 8, 1);
lean_closure_set(v___f_485_, 0, v___x_474_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = l_Lean_instInhabitedExpr;
v_v_488_ = lean_array_uget_borrowed(v_bs_477_, v_i_476_);
v___x_489_ = lean_nat_sub(v_v_488_, v_val_472_);
v___x_490_ = lean_nat_sub(v___x_489_, v___x_486_);
lean_dec(v___x_489_);
v___x_491_ = lean_array_get_borrowed(v___x_487_, v_a_473_, v___x_490_);
lean_dec(v___x_490_);
v___x_492_ = 0;
lean_inc(v___x_491_);
v___x_493_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg(v___x_491_, v___f_485_, v___x_492_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; lean_object* v_bs_x27_496_; size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = lean_unsigned_to_nat(0u);
v_bs_x27_496_ = lean_array_uset(v_bs_477_, v_i_476_, v___x_495_);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_add(v_i_476_, v___x_497_);
v___x_499_ = lean_array_uset(v_bs_x27_496_, v_i_476_, v_a_494_);
v_i_476_ = v___x_498_;
v_bs_477_ = v___x_499_;
goto _start;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v_bs_477_);
lean_dec_ref(v___x_474_);
v_a_501_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_493_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___boxed(lean_object* v_val_509_, lean_object* v_a_510_, lean_object* v___x_511_, lean_object* v_sz_512_, lean_object* v_i_513_, lean_object* v_bs_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
size_t v_sz_boxed_520_; size_t v_i_boxed_521_; lean_object* v_res_522_; 
v_sz_boxed_520_ = lean_unbox_usize(v_sz_512_);
lean_dec(v_sz_512_);
v_i_boxed_521_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8(v_val_509_, v_a_510_, v___x_511_, v_sz_boxed_520_, v_i_boxed_521_, v_bs_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v_a_510_);
lean_dec(v_val_509_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3_spec__7(lean_object* v_xs_523_, lean_object* v_v_524_, lean_object* v_i_525_){
_start:
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_array_get_size(v_xs_523_);
v___x_527_ = lean_nat_dec_lt(v_i_525_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v_i_525_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_fget_borrowed(v_xs_523_, v_i_525_);
v___x_530_ = lean_expr_eqv(v___x_529_, v_v_524_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_i_525_, v___x_531_);
lean_dec(v_i_525_);
v_i_525_ = v___x_532_;
goto _start;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_i_525_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3_spec__7___boxed(lean_object* v_xs_535_, lean_object* v_v_536_, lean_object* v_i_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3_spec__7(v_xs_535_, v_v_536_, v_i_537_);
lean_dec_ref(v_v_536_);
lean_dec_ref(v_xs_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3(lean_object* v_xs_539_, lean_object* v_v_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3_spec__7(v_xs_539_, v_v_540_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3___boxed(lean_object* v_xs_543_, lean_object* v_v_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3(v_xs_543_, v_v_544_);
lean_dec_ref(v_v_544_);
lean_dec_ref(v_xs_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2(lean_object* v_xs_546_, lean_object* v_v_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2_spec__3(v_xs_546_, v_v_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v___x_549_; 
v___x_549_ = lean_box(0);
return v___x_549_;
}
else
{
lean_object* v_val_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_val_550_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_548_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_val_550_);
lean_dec(v___x_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_val_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2___boxed(lean_object* v_xs_558_, lean_object* v_v_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2(v_xs_558_, v_v_559_);
lean_dec_ref(v_v_559_);
lean_dec_ref(v_xs_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__7___redArg(lean_object* v_a_561_, lean_object* v_b_562_){
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
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_587_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___lam__0___closed__0));
v___x_588_ = lean_unsigned_to_nat(6u);
v___x_589_ = lean_unsigned_to_nat(62u);
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_592_ = l_mkPanicMessageWithDecl(v___x_591_, v___x_590_, v___x_589_, v___x_588_, v___x_587_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___lam__0___closed__2));
v___x_595_ = lean_unsigned_to_nat(6u);
v___x_596_ = lean_unsigned_to_nat(63u);
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_599_ = l_mkPanicMessageWithDecl(v___x_598_, v___x_597_, v___x_596_, v___x_595_, v___x_594_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___lam__0___closed__4));
v___x_602_ = lean_unsigned_to_nat(6u);
v___x_603_ = lean_unsigned_to_nat(64u);
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_606_ = l_mkPanicMessageWithDecl(v___x_605_, v___x_604_, v___x_603_, v___x_602_, v___x_601_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__7(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_609_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__6));
v___x_610_ = lean_unsigned_to_nat(76u);
v___x_611_ = lean_unsigned_to_nat(66u);
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_614_ = l_mkPanicMessageWithDecl(v___x_613_, v___x_612_, v___x_611_, v___x_610_, v___x_609_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__8(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_615_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__6));
v___x_616_ = lean_unsigned_to_nat(49u);
v___x_617_ = lean_unsigned_to_nat(65u);
v___x_618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__1));
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8___lam__0___closed__0));
v___x_620_ = l_mkPanicMessageWithDecl(v___x_619_, v___x_618_, v___x_617_, v___x_616_, v___x_615_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___lam__0(lean_object* v_declName_621_, lean_object* v_xs_622_, lean_object* v_r_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = l_Lean_Expr_isApp(v_r_623_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v_declName_621_);
v___x_630_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__1, &l_Lean_getCasesInfo_x3f___lam__0___closed__1_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__1);
v___x_631_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__1(v___x_630_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
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
v___x_634_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__3, &l_Lean_getCasesInfo_x3f___lam__0___closed__3_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__3);
v___x_635_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__1(v___x_634_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
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
v___x_638_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__5, &l_Lean_getCasesInfo_x3f___lam__0___closed__5_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__5);
v___x_639_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__1(v___x_638_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__2(v_xs_622_, v___x_632_);
lean_dec_ref(v___x_632_);
if (lean_obj_tag(v___x_640_) == 1)
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_726_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_726_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_726_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_726_;
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
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = l_Lean_Expr_getAppFn(v_a_648_);
lean_dec(v_a_648_);
v___x_650_ = l_Lean_Expr_constName_x3f(v___x_649_);
lean_dec_ref(v___x_649_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_715_; 
v_val_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_715_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_715_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_715_;
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
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__5(v_sz_659_, v___x_660_, v___x_658_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___y_664_; uint8_t v___y_696_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; uint8_t v___x_701_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_698_ = lean_array_get_size(v_a_662_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_nat_dec_eq(v___x_698_, v___x_699_);
v___x_701_ = lean_bool_not(v___x_700_);
if (v___x_701_ == 0)
{
lean_dec_ref(v___x_636_);
v___y_696_ = v___x_701_;
goto v___jp_695_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; uint8_t v___x_706_; 
v___x_702_ = lean_array_get_borrowed(v___x_645_, v_a_662_, v___x_699_);
v___x_703_ = l_Lean_Expr_getForallBody(v___x_702_);
v___x_704_ = l_Lean_Expr_getAppFn(v___x_703_);
lean_dec_ref(v___x_703_);
v___x_705_ = lean_expr_eqv(v___x_704_, v___x_636_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_704_);
v___x_706_ = lean_bool_not(v___x_705_);
v___y_696_ = v___x_706_;
goto v___jp_695_;
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
v___x_670_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___lam__0___closed__6));
v___x_671_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__7___redArg(v___x_669_, v___x_670_);
v_sz_672_ = lean_array_size(v___x_671_);
lean_inc(v___x_646_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__8(v_val_641_, v_a_662_, v___x_646_, v_sz_672_, v___x_660_, v___x_671_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
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
lean_dec_ref_known(v___x_666_, 2);
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
v___jp_695_:
{
if (v___y_696_ == 0)
{
v___y_664_ = v___x_656_;
goto v___jp_663_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = lean_unsigned_to_nat(2u);
v___y_664_ = v___x_697_;
goto v___jp_663_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_del_object(v___x_653_);
lean_dec(v_val_651_);
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec_ref(v___x_636_);
lean_dec(v_declName_621_);
v_a_707_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_661_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_661_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v___x_650_);
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec_ref(v___x_636_);
lean_dec(v_declName_621_);
v___x_716_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__7, &l_Lean_getCasesInfo_x3f___lam__0___closed__7_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__7);
v___x_717_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__1(v___x_716_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_717_;
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec_ref(v___x_636_);
lean_dec(v_declName_621_);
v_a_718_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_647_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_647_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v___x_640_);
lean_dec_ref(v___x_636_);
lean_dec(v_declName_621_);
v___x_727_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__8, &l_Lean_getCasesInfo_x3f___lam__0___closed__8_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__8);
v___x_728_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__1(v___x_727_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___lam__0___boxed(lean_object* v_declName_729_, lean_object* v_xs_730_, lean_object* v_r_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_getCasesInfo_x3f___lam__0(v_declName_729_, v_xs_730_, v_r_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec_ref(v_r_731_);
lean_dec_ref(v_xs_730_);
return v_res_737_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__0(void){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_738_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__0);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
lean_ctor_set(v___x_743_, 3, v___x_742_);
lean_ctor_set(v___x_743_, 4, v___x_741_);
lean_ctor_set(v___x_743_, 5, v___x_741_);
lean_ctor_set(v___x_743_, 6, v___x_741_);
lean_ctor_set(v___x_743_, 7, v___x_741_);
lean_ctor_set(v___x_743_, 8, v___x_741_);
lean_ctor_set(v___x_743_, 9, v___x_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__3(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(32u);
v___x_745_ = lean_mk_empty_array_with_capacity(v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4(void){
_start:
{
size_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_747_ = ((size_t)5ULL);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_unsigned_to_nat(32u);
v___x_750_ = lean_mk_empty_array_with_capacity(v___x_749_);
v___x_751_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__3);
v___x_752_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
lean_ctor_set(v___x_752_, 2, v___x_748_);
lean_ctor_set(v___x_752_, 3, v___x_748_);
lean_ctor_set_usize(v___x_752_, 4, v___x_747_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = lean_box(1);
v___x_754_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4);
v___x_755_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__1);
v___x_756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
lean_ctor_set(v___x_756_, 2, v___x_753_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(lean_object* v_msgData_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v_env_762_; lean_object* v_options_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_761_ = lean_st_ref_get(v___y_759_);
v_env_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_env_762_);
lean_dec(v___x_761_);
v_options_763_ = lean_ctor_get(v___y_758_, 2);
v___x_764_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2);
v___x_765_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5);
lean_inc_ref(v_options_763_);
v___x_766_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_766_, 0, v_env_762_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
lean_ctor_set(v___x_766_, 3, v_options_763_);
v___x_767_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_msgData_757_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___boxed(lean_object* v_msgData_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(v_msgData_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(lean_object* v_msg_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_ref_778_; lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_ref_778_ = lean_ctor_get(v___y_775_, 5);
v___x_779_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(v_msg_774_, v___y_775_, v___y_776_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_inc(v_ref_778_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_ref_778_);
lean_ctor_set(v___x_784_, 1, v_a_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 1);
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg___boxed(lean_object* v_msg_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(lean_object* v_ref_794_, lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_fileName_799_; lean_object* v_fileMap_800_; lean_object* v_options_801_; lean_object* v_currRecDepth_802_; lean_object* v_maxRecDepth_803_; lean_object* v_ref_804_; lean_object* v_currNamespace_805_; lean_object* v_openDecls_806_; lean_object* v_initHeartbeats_807_; lean_object* v_maxHeartbeats_808_; lean_object* v_quotContext_809_; lean_object* v_currMacroScope_810_; uint8_t v_diag_811_; lean_object* v_cancelTk_x3f_812_; uint8_t v_suppressElabErrors_813_; lean_object* v_inheritedTraceOptions_814_; lean_object* v_ref_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_fileName_799_ = lean_ctor_get(v___y_796_, 0);
v_fileMap_800_ = lean_ctor_get(v___y_796_, 1);
v_options_801_ = lean_ctor_get(v___y_796_, 2);
v_currRecDepth_802_ = lean_ctor_get(v___y_796_, 3);
v_maxRecDepth_803_ = lean_ctor_get(v___y_796_, 4);
v_ref_804_ = lean_ctor_get(v___y_796_, 5);
v_currNamespace_805_ = lean_ctor_get(v___y_796_, 6);
v_openDecls_806_ = lean_ctor_get(v___y_796_, 7);
v_initHeartbeats_807_ = lean_ctor_get(v___y_796_, 8);
v_maxHeartbeats_808_ = lean_ctor_get(v___y_796_, 9);
v_quotContext_809_ = lean_ctor_get(v___y_796_, 10);
v_currMacroScope_810_ = lean_ctor_get(v___y_796_, 11);
v_diag_811_ = lean_ctor_get_uint8(v___y_796_, sizeof(void*)*14);
v_cancelTk_x3f_812_ = lean_ctor_get(v___y_796_, 12);
v_suppressElabErrors_813_ = lean_ctor_get_uint8(v___y_796_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_814_ = lean_ctor_get(v___y_796_, 13);
v_ref_815_ = l_Lean_replaceRef(v_ref_794_, v_ref_804_);
lean_inc_ref(v_inheritedTraceOptions_814_);
lean_inc(v_cancelTk_x3f_812_);
lean_inc(v_currMacroScope_810_);
lean_inc(v_quotContext_809_);
lean_inc(v_maxHeartbeats_808_);
lean_inc(v_initHeartbeats_807_);
lean_inc(v_openDecls_806_);
lean_inc(v_currNamespace_805_);
lean_inc(v_maxRecDepth_803_);
lean_inc(v_currRecDepth_802_);
lean_inc_ref(v_options_801_);
lean_inc_ref(v_fileMap_800_);
lean_inc_ref(v_fileName_799_);
v___x_816_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_816_, 0, v_fileName_799_);
lean_ctor_set(v___x_816_, 1, v_fileMap_800_);
lean_ctor_set(v___x_816_, 2, v_options_801_);
lean_ctor_set(v___x_816_, 3, v_currRecDepth_802_);
lean_ctor_set(v___x_816_, 4, v_maxRecDepth_803_);
lean_ctor_set(v___x_816_, 5, v_ref_815_);
lean_ctor_set(v___x_816_, 6, v_currNamespace_805_);
lean_ctor_set(v___x_816_, 7, v_openDecls_806_);
lean_ctor_set(v___x_816_, 8, v_initHeartbeats_807_);
lean_ctor_set(v___x_816_, 9, v_maxHeartbeats_808_);
lean_ctor_set(v___x_816_, 10, v_quotContext_809_);
lean_ctor_set(v___x_816_, 11, v_currMacroScope_810_);
lean_ctor_set(v___x_816_, 12, v_cancelTk_x3f_812_);
lean_ctor_set(v___x_816_, 13, v_inheritedTraceOptions_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*14, v_diag_811_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*14 + 1, v_suppressElabErrors_813_);
v___x_817_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_795_, v___x_816_, v___y_797_);
lean_dec_ref_known(v___x_816_, 14);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg___boxed(lean_object* v_ref_818_, lean_object* v_msg_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_818_, v_msg_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v_ref_818_);
return v_res_823_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0));
v___x_826_ = l_Lean_stringToMessageData(v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2));
v___x_829_ = l_Lean_stringToMessageData(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4));
v___x_832_ = l_Lean_stringToMessageData(v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6));
v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8));
v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10));
v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(lean_object* v_msg_845_, lean_object* v_declHint_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v_env_850_; uint8_t v___y_852_; uint8_t v___x_908_; uint8_t v___x_909_; 
v___x_849_ = lean_st_ref_get(v___y_847_);
v_env_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc_ref(v_env_850_);
lean_dec(v___x_849_);
v___x_908_ = l_Lean_Name_isAnonymous(v_declHint_846_);
v___x_909_ = lean_bool_not(v___x_908_);
if (v___x_909_ == 0)
{
v___y_852_ = v___x_909_;
goto v___jp_851_;
}
else
{
uint8_t v_isExporting_910_; 
v_isExporting_910_ = lean_ctor_get_uint8(v_env_850_, sizeof(void*)*8);
v___y_852_ = v_isExporting_910_;
goto v___jp_851_;
}
v___jp_851_:
{
if (v___y_852_ == 0)
{
lean_object* v___x_853_; 
lean_dec_ref(v_env_850_);
lean_dec(v_declHint_846_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_msg_845_);
return v___x_853_;
}
else
{
uint8_t v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_854_ = 0;
lean_inc_ref(v_env_850_);
v___x_855_ = l_Lean_Environment_setExporting(v_env_850_, v___x_854_);
lean_inc(v_declHint_846_);
lean_inc_ref(v___x_855_);
v___x_856_ = l_Lean_Environment_contains(v___x_855_, v_declHint_846_, v___y_852_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec_ref(v___x_855_);
lean_dec_ref(v_env_850_);
lean_dec(v_declHint_846_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v_msg_845_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_c_863_; lean_object* v___x_864_; 
v___x_858_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__2);
v___x_859_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__5);
v___x_860_ = l_Lean_Options_empty;
v___x_861_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_861_, 0, v___x_855_);
lean_ctor_set(v___x_861_, 1, v___x_858_);
lean_ctor_set(v___x_861_, 2, v___x_859_);
lean_ctor_set(v___x_861_, 3, v___x_860_);
lean_inc(v_declHint_846_);
v___x_862_ = l_Lean_MessageData_ofConstName(v_declHint_846_, v___x_854_);
v_c_863_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_863_, 0, v___x_861_);
lean_ctor_set(v_c_863_, 1, v___x_862_);
v___x_864_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_850_, v_declHint_846_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref(v_env_850_);
lean_dec(v_declHint_846_);
v___x_865_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v_c_863_);
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_MessageData_note(v___x_868_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v_msg_845_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
else
{
lean_object* v_val_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_907_; 
v_val_872_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_907_ == 0)
{
v___x_874_ = v___x_864_;
v_isShared_875_ = v_isSharedCheck_907_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_val_872_);
lean_dec(v___x_864_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_907_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_mod_879_; uint8_t v___x_880_; 
v___x_876_ = lean_box(0);
v___x_877_ = l_Lean_Environment_header(v_env_850_);
lean_dec_ref(v_env_850_);
v___x_878_ = l_Lean_EnvironmentHeader_moduleNames(v___x_877_);
v_mod_879_ = lean_array_get(v___x_876_, v___x_878_, v_val_872_);
lean_dec(v_val_872_);
lean_dec_ref(v___x_878_);
v___x_880_ = l_Lean_isPrivateName(v_declHint_846_);
lean_dec(v_declHint_846_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_c_863_);
v___x_883_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_MessageData_ofName(v_mod_879_);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_MessageData_note(v___x_888_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v_msg_845_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 0);
lean_ctor_set(v___x_874_, 0, v___x_890_);
v___x_892_ = v___x_874_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
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
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v_c_863_);
v___x_896_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_MessageData_ofName(v_mod_879_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_MessageData_note(v___x_901_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v_msg_845_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 0);
lean_ctor_set(v___x_874_, 0, v___x_903_);
v___x_905_ = v___x_874_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___boxed(lean_object* v_msg_911_, lean_object* v_declHint_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_911_, v_declHint_912_, v___y_913_);
lean_dec(v___y_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(lean_object* v_msg_916_, lean_object* v_declHint_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_931_; 
v___x_921_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_916_, v_declHint_917_, v___y_919_);
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_931_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_926_ = l_Lean_unknownIdentifierMessageTag;
v___x_927_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_922_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_927_);
v___x_929_ = v___x_924_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15___boxed(lean_object* v_msg_932_, lean_object* v_declHint_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(v_msg_932_, v_declHint_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_938_, lean_object* v_msg_939_, lean_object* v_declHint_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; lean_object* v_a_945_; lean_object* v___x_946_; 
v___x_944_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(v_msg_939_, v_declHint_940_, v___y_941_, v___y_942_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref(v___x_944_);
v___x_946_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_938_, v_a_945_, v___y_941_, v___y_942_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_947_, lean_object* v_msg_948_, lean_object* v_declHint_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_947_, v_msg_948_, v_declHint_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_ref_947_);
return v_res_953_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_957_, lean_object* v_constName_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_962_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_963_ = 0;
lean_inc(v_constName_958_);
v___x_964_ = l_Lean_MessageData_ofConstName(v_constName_958_, v___x_963_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_962_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4___closed__1);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_957_, v___x_967_, v_constName_958_, v___y_959_, v___y_960_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_969_, lean_object* v_constName_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_969_, v_constName_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v_ref_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___redArg(lean_object* v_constName_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_ref_979_; lean_object* v___x_980_; 
v_ref_979_ = lean_ctor_get(v___y_976_, 5);
v___x_980_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_979_, v_constName_975_, v___y_976_, v___y_977_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0(lean_object* v_constName_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v_env_991_; uint8_t v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_st_ref_get(v___y_988_);
v_env_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc_ref(v_env_991_);
lean_dec(v___x_990_);
v___x_992_ = 0;
lean_inc(v_constName_986_);
v___x_993_ = l_Lean_Environment_findConstVal_x3f(v_env_991_, v_constName_986_, v___x_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_986_, v___y_987_, v___y_988_);
return v___x_994_;
}
else
{
lean_object* v_val_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_constName_986_);
v_val_995_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_993_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_val_995_);
lean_dec(v___x_993_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set_tag(v___x_997_, 0);
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_val_995_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0___boxed(lean_object* v_constName_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0(v_constName_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1007_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__0(void){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__1(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__0, &l_Lean_getCasesInfo_x3f___closed__0_once, _init_l_Lean_getCasesInfo_x3f___closed__0);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__2(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1011_ = lean_box(1);
v___x_1012_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4);
v___x_1013_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__1, &l_Lean_getCasesInfo_x3f___closed__1_once, _init_l_Lean_getCasesInfo_x3f___closed__1);
v___x_1014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1012_);
lean_ctor_set(v___x_1014_, 2, v___x_1011_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__4(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__1, &l_Lean_getCasesInfo_x3f___closed__1_once, _init_l_Lean_getCasesInfo_x3f___closed__1);
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_ctor_set(v___x_1019_, 2, v___x_1018_);
lean_ctor_set(v___x_1019_, 3, v___x_1018_);
lean_ctor_set(v___x_1019_, 4, v___x_1017_);
lean_ctor_set(v___x_1019_, 5, v___x_1017_);
lean_ctor_set(v___x_1019_, 6, v___x_1017_);
lean_ctor_set(v___x_1019_, 7, v___x_1017_);
lean_ctor_set(v___x_1019_, 8, v___x_1017_);
lean_ctor_set(v___x_1019_, 9, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__5(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__1, &l_Lean_getCasesInfo_x3f___closed__1_once, _init_l_Lean_getCasesInfo_x3f___closed__1);
v___x_1021_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
lean_ctor_set(v___x_1021_, 2, v___x_1020_);
lean_ctor_set(v___x_1021_, 3, v___x_1020_);
lean_ctor_set(v___x_1021_, 4, v___x_1020_);
lean_ctor_set(v___x_1021_, 5, v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__6(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__1, &l_Lean_getCasesInfo_x3f___closed__1_once, _init_l_Lean_getCasesInfo_x3f___closed__1);
v___x_1023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
lean_ctor_set(v___x_1023_, 2, v___x_1022_);
lean_ctor_set(v___x_1023_, 3, v___x_1022_);
lean_ctor_set(v___x_1023_, 4, v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__7(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1024_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__6, &l_Lean_getCasesInfo_x3f___closed__6_once, _init_l_Lean_getCasesInfo_x3f___closed__6);
v___x_1025_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___closed__4);
v___x_1026_ = lean_box(1);
v___x_1027_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__5, &l_Lean_getCasesInfo_x3f___closed__5_once, _init_l_Lean_getCasesInfo_x3f___closed__5);
v___x_1028_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__4, &l_Lean_getCasesInfo_x3f___closed__4_once, _init_l_Lean_getCasesInfo_x3f___closed__4);
v___x_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1027_);
lean_ctor_set(v___x_1029_, 2, v___x_1026_);
lean_ctor_set(v___x_1029_, 3, v___x_1025_);
lean_ctor_set(v___x_1029_, 4, v___x_1024_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f(lean_object* v_declName_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v_env_1035_; uint8_t v___x_1036_; 
v___x_1034_ = lean_st_ref_get(v_a_1032_);
v_env_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_env_1035_);
lean_dec(v___x_1034_);
lean_inc(v_declName_1030_);
v___x_1036_ = l_Lean_isCasesOnLike(v_env_1035_, v_declName_1030_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec(v_declName_1030_);
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; 
lean_inc(v_declName_1030_);
v___x_1039_ = l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0(v_declName_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; uint8_t v___x_1041_; uint8_t v___x_1042_; uint8_t v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; uint64_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_type_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = 0;
v___x_1042_ = 1;
v___x_1043_ = 0;
v___x_1044_ = 2;
v___x_1045_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1045_, 0, v___x_1041_);
lean_ctor_set_uint8(v___x_1045_, 1, v___x_1041_);
lean_ctor_set_uint8(v___x_1045_, 2, v___x_1041_);
lean_ctor_set_uint8(v___x_1045_, 3, v___x_1041_);
lean_ctor_set_uint8(v___x_1045_, 4, v___x_1041_);
lean_ctor_set_uint8(v___x_1045_, 5, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 6, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 7, v___x_1041_);
lean_ctor_set_uint8(v___x_1045_, 8, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 9, v___x_1042_);
lean_ctor_set_uint8(v___x_1045_, 10, v___x_1043_);
lean_ctor_set_uint8(v___x_1045_, 11, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 12, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 13, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 14, v___x_1044_);
lean_ctor_set_uint8(v___x_1045_, 15, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 16, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 17, v___x_1036_);
lean_ctor_set_uint8(v___x_1045_, 18, v___x_1036_);
v___x_1046_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set_uint64(v___x_1047_, sizeof(void*)*1, v___x_1046_);
v___x_1048_ = lean_box(1);
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__2, &l_Lean_getCasesInfo_x3f___closed__2_once, _init_l_Lean_getCasesInfo_x3f___closed__2);
v___x_1051_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___closed__3));
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1053_, 0, v___x_1047_);
lean_ctor_set(v___x_1053_, 1, v___x_1048_);
lean_ctor_set(v___x_1053_, 2, v___x_1050_);
lean_ctor_set(v___x_1053_, 3, v___x_1051_);
lean_ctor_set(v___x_1053_, 4, v___x_1052_);
lean_ctor_set(v___x_1053_, 5, v___x_1049_);
lean_ctor_set(v___x_1053_, 6, v___x_1052_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*7, v___x_1041_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*7 + 1, v___x_1041_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*7 + 2, v___x_1041_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*7 + 3, v___x_1036_);
v___x_1054_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__7, &l_Lean_getCasesInfo_x3f___closed__7_once, _init_l_Lean_getCasesInfo_x3f___closed__7);
v___x_1055_ = lean_st_mk_ref(v___x_1054_);
v_type_1056_ = lean_ctor_get(v_a_1040_, 2);
lean_inc_ref(v_type_1056_);
lean_dec(v_a_1040_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_getCasesInfo_x3f___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1057_, 0, v_declName_1030_);
v___x_1058_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__6___redArg(v_type_1056_, v___f_1057_, v___x_1041_, v___x_1053_, v___x_1055_, v_a_1031_, v_a_1032_);
lean_dec_ref_known(v___x_1053_, 7);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_st_ref_get(v___x_1055_);
lean_dec(v___x_1055_);
lean_dec(v___x_1063_);
if (v_isShared_1062_ == 0)
{
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1059_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
else
{
lean_dec(v___x_1055_);
return v___x_1058_;
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_declName_1030_);
v_a_1068_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1039_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1039_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___boxed(lean_object* v_declName_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_getCasesInfo_x3f(v_declName_1076_, v_a_1077_, v_a_1078_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__7(lean_object* v_inst_1081_, lean_object* v_R_1082_, lean_object* v_a_1083_, lean_object* v_b_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__7___redArg(v_a_1083_, v_b_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b1_1086_, lean_object* v_constName_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_constName_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0(v_00_u03b1_1092_, v_constName_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6(lean_object* v_00_u03b1_1098_, lean_object* v_msg_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___redArg(v_msg_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_msg_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__4_spec__6(v_00_u03b1_1106_, v_msg_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_1114_, lean_object* v_ref_1115_, lean_object* v_constName_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_1115_, v_constName_1116_, v___y_1117_, v___y_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1121_, lean_object* v_ref_1122_, lean_object* v_constName_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4(v_00_u03b1_1121_, v_ref_1122_, v_constName_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v_ref_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_1128_, lean_object* v_ref_1129_, lean_object* v_msg_1130_, lean_object* v_declHint_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1129_, v_msg_1130_, v_declHint_1131_, v___y_1132_, v___y_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_ref_1137_, lean_object* v_msg_1138_, lean_object* v_declHint_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_1136_, v_ref_1137_, v_msg_1138_, v_declHint_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_ref_1137_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17(lean_object* v_msg_1144_, lean_object* v_declHint_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_1144_, v_declHint_1145_, v___y_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___boxed(lean_object* v_msg_1150_, lean_object* v_declHint_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17(v_msg_1150_, v_declHint_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16(lean_object* v_00_u03b1_1156_, lean_object* v_ref_1157_, lean_object* v_msg_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_1157_, v_msg_1158_, v___y_1159_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_ref_1164_, lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16(v_00_u03b1_1163_, v_ref_1164_, v_msg_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v_ref_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19(lean_object* v_00_u03b1_1170_, lean_object* v_msg_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_1171_, v___y_1172_, v___y_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_msg_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19(v_00_u03b1_1176_, v_msg_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1181_;
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
