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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_instMonadEIO___redArg();
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t l_Lean_isCasesOnLike(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorIdx___impl___boxed(lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_getCasesInfo_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_getCasesInfo_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.CasesInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.getCasesInfo\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: mr.isApp\n          "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "assertion violation: motiveArg == xs[discrPos]!\n            "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_getCasesInfo_x3f___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__0;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__1;
static const lean_array_object l_Lean_getCasesInfo_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getCasesInfo_x3f___closed__2 = (const lean_object*)&l_Lean_getCasesInfo_x3f___closed__2_value;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__3;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__4;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__5;
static lean_once_cell_t l_Lean_getCasesInfo_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getCasesInfo_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_CasesAltInfo_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_ctorName_7_; lean_object* v_numFields_8_; lean_object* v___x_9_; 
v_ctorName_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ctorName_7_);
v_numFields_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_numFields_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_ctorName_7_, v_numFields_8_);
return v___x_9_;
}
else
{
lean_object* v_numHyps_10_; lean_object* v___x_11_; 
v_numHyps_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_numHyps_10_);
lean_dec_ref_known(v_t_5_, 1);
v___x_11_ = lean_apply_1(v_k_6_, v_numHyps_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_CasesAltInfo_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctor_elim___redArg(lean_object* v_t_24_, lean_object* v_ctor_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_24_, v_ctor_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_ctor_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_ctor_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_28_, v_ctor_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_default_elim___redArg(lean_object* v_t_32_, lean_object* v_default_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_32_, v_default_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesAltInfo_default_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_default_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_CasesAltInfo_ctorElim___redArg(v_t_36_, v_default_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesInfo_numAlts(lean_object* v_c_45_){
_start:
{
lean_object* v_altNumParams_46_; lean_object* v___x_47_; 
v_altNumParams_46_ = lean_ctor_get(v_c_45_, 6);
v___x_47_ = lean_array_get_size(v_altNumParams_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_CasesInfo_numAlts___boxed(lean_object* v_c_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_CasesInfo_numAlts(v_c_48_);
lean_dec_ref(v_c_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__0(lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_3407__overap_58_; lean_object* v___x_59_; 
v___f_57_ = ((lean_object*)(l_panic___at___00Lean_getCasesInfo_x3f_spec__0___closed__0));
v___x_3407__overap_58_ = lean_panic_fn_borrowed(v___f_57_, v_msg_51_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
v___x_59_ = lean_apply_5(v___x_3407__overap_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, lean_box(0));
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__0___boxed(lean_object* v_msg_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__0(v_msg_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__2(lean_object* v_msg_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_3429__overap_74_; lean_object* v___x_75_; 
v___f_73_ = ((lean_object*)(l_panic___at___00Lean_getCasesInfo_x3f_spec__0___closed__0));
v___x_3429__overap_74_ = lean_panic_fn_borrowed(v___f_73_, v_msg_67_);
lean_inc(v___y_71_);
lean_inc_ref(v___y_70_);
lean_inc(v___y_69_);
lean_inc_ref(v___y_68_);
v___x_75_ = lean_apply_5(v___x_3429__overap_74_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, lean_box(0));
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getCasesInfo_x3f_spec__2___boxed(lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__2(v_msg_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg___lam__0(lean_object* v_k_83_, lean_object* v_b_84_, lean_object* v_c_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; 
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
v___x_91_ = lean_apply_7(v_k_83_, v_b_84_, v_c_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, lean_box(0));
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg___lam__0___boxed(lean_object* v_k_92_, lean_object* v_b_93_, lean_object* v_c_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg___lam__0(v_k_92_, v_b_93_, v_c_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg(lean_object* v_type_101_, lean_object* v_k_102_, uint8_t v_cleanupAnnotations_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___f_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___f_109_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_109_, 0, v_k_102_);
v___x_110_ = 0;
v___x_111_ = lean_box(0);
v___x_112_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_110_, v___x_111_, v_type_101_, v___f_109_, v_cleanupAnnotations_103_, v___x_110_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_121_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_112_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_112_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg___boxed(lean_object* v_type_129_, lean_object* v_k_130_, lean_object* v_cleanupAnnotations_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_137_; lean_object* v_res_138_; 
v_cleanupAnnotations_boxed_137_ = lean_unbox(v_cleanupAnnotations_131_);
v_res_138_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg(v_type_129_, v_k_130_, v_cleanupAnnotations_boxed_137_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5(lean_object* v_00_u03b1_139_, lean_object* v_type_140_, lean_object* v_k_141_, uint8_t v_cleanupAnnotations_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg(v_type_140_, v_k_141_, v_cleanupAnnotations_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___boxed(lean_object* v_00_u03b1_149_, lean_object* v_type_150_, lean_object* v_k_151_, lean_object* v_cleanupAnnotations_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_158_; lean_object* v_res_159_; 
v_cleanupAnnotations_boxed_158_ = lean_unbox(v_cleanupAnnotations_152_);
v_res_159_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5(v_00_u03b1_149_, v_type_150_, v_k_151_, v_cleanupAnnotations_boxed_158_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__6___redArg(lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
lean_object* v_next_162_; 
v_next_162_ = lean_ctor_get(v_a_160_, 0);
lean_inc(v_next_162_);
if (lean_obj_tag(v_next_162_) == 0)
{
lean_dec_ref(v_a_160_);
return v_b_161_;
}
else
{
lean_object* v_upperBound_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_183_; 
v_upperBound_163_ = lean_ctor_get(v_a_160_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_a_160_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_a_160_, 0);
lean_dec(v_unused_184_);
v___x_165_ = v_a_160_;
v_isShared_166_ = v_isSharedCheck_183_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_upperBound_163_);
lean_dec(v_a_160_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_183_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_val_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_182_; 
v_val_167_ = lean_ctor_get(v_next_162_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_next_162_);
if (v_isSharedCheck_182_ == 0)
{
v___x_169_ = v_next_162_;
v_isShared_170_ = v_isSharedCheck_182_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_val_167_);
lean_dec(v_next_162_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_182_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_lt(v_val_167_, v_upperBound_163_);
if (v___x_171_ == 0)
{
lean_del_object(v___x_169_);
lean_dec(v_val_167_);
lean_del_object(v___x_165_);
lean_dec(v_upperBound_163_);
return v_b_161_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_add(v_val_167_, v___x_172_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_173_);
v___x_175_ = v___x_169_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_181_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_175_);
v___x_177_ = v___x_165_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_upperBound_163_);
v___x_177_ = v_reuseFailAlloc_180_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = lean_array_push(v_b_161_, v_val_167_);
v_a_160_ = v___x_177_;
v_b_161_ = v___x_178_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1_spec__4(lean_object* v_xs_185_, lean_object* v_v_186_, lean_object* v_i_187_){
_start:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_array_get_size(v_xs_185_);
v___x_189_ = lean_nat_dec_lt(v_i_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
lean_dec(v_i_187_);
v___x_190_ = lean_box(0);
return v___x_190_;
}
else
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_array_fget_borrowed(v_xs_185_, v_i_187_);
v___x_192_ = lean_expr_eqv(v___x_191_, v_v_186_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_i_187_, v___x_193_);
lean_dec(v_i_187_);
v_i_187_ = v___x_194_;
goto _start;
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v_i_187_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1_spec__4___boxed(lean_object* v_xs_197_, lean_object* v_v_198_, lean_object* v_i_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1_spec__4(v_xs_197_, v_v_198_, v_i_199_);
lean_dec_ref(v_v_198_);
lean_dec_ref(v_xs_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1(lean_object* v_xs_201_, lean_object* v_v_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1_spec__4(v_xs_201_, v_v_202_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1___boxed(lean_object* v_xs_205_, lean_object* v_v_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1(v_xs_205_, v_v_206_);
lean_dec_ref(v_v_206_);
lean_dec_ref(v_xs_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1(lean_object* v_xs_208_, lean_object* v_v_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1_spec__1(v_xs_208_, v_v_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_box(0);
return v___x_211_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_210_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_dec(v___x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_val_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1___boxed(lean_object* v_xs_220_, lean_object* v_v_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1(v_xs_220_, v_v_221_);
lean_dec_ref(v_v_221_);
lean_dec_ref(v_xs_220_);
return v_res_222_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_instMonadEIO___redArg();
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5(lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toApplicative_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_297_; 
v___x_234_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__0);
v___x_235_ = l_StateRefT_x27_instMonad___redArg(v___x_234_);
v_toApplicative_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v___x_235_, 1);
lean_dec(v_unused_298_);
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_297_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toApplicative_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_297_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_toFunctor_240_; lean_object* v_toSeq_241_; lean_object* v_toSeqLeft_242_; lean_object* v_toSeqRight_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_295_; 
v_toFunctor_240_ = lean_ctor_get(v_toApplicative_236_, 0);
v_toSeq_241_ = lean_ctor_get(v_toApplicative_236_, 2);
v_toSeqLeft_242_ = lean_ctor_get(v_toApplicative_236_, 3);
v_toSeqRight_243_ = lean_ctor_get(v_toApplicative_236_, 4);
v_isSharedCheck_295_ = !lean_is_exclusive(v_toApplicative_236_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_toApplicative_236_, 1);
lean_dec(v_unused_296_);
v___x_245_ = v_toApplicative_236_;
v_isShared_246_ = v_isSharedCheck_295_;
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
v_isShared_246_ = v_isSharedCheck_295_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_256_; 
v___f_247_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__1));
v___f_248_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__2));
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
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___f_247_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v___f_254_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v___f_253_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v___f_252_);
v___x_256_ = v_reuseFailAlloc_294_;
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
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___f_248_);
v___x_258_ = v_reuseFailAlloc_293_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v_toApplicative_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_291_; 
v___x_259_ = l_StateRefT_x27_instMonad___redArg(v___x_258_);
v_toApplicative_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v___x_259_, 1);
lean_dec(v_unused_292_);
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_291_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_toApplicative_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_291_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_toFunctor_264_; lean_object* v_toSeq_265_; lean_object* v_toSeqLeft_266_; lean_object* v_toSeqRight_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_289_; 
v_toFunctor_264_ = lean_ctor_get(v_toApplicative_260_, 0);
v_toSeq_265_ = lean_ctor_get(v_toApplicative_260_, 2);
v_toSeqLeft_266_ = lean_ctor_get(v_toApplicative_260_, 3);
v_toSeqRight_267_ = lean_ctor_get(v_toApplicative_260_, 4);
v_isSharedCheck_289_ = !lean_is_exclusive(v_toApplicative_260_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v_toApplicative_260_, 1);
lean_dec(v_unused_290_);
v___x_269_ = v_toApplicative_260_;
v_isShared_270_ = v_isSharedCheck_289_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_toSeqRight_267_);
lean_inc(v_toSeqLeft_266_);
lean_inc(v_toSeq_265_);
lean_inc(v_toFunctor_264_);
lean_dec(v_toApplicative_260_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_289_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___x_280_; 
v___f_271_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__3));
v___f_272_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___closed__4));
lean_inc_ref(v_toFunctor_264_);
v___f_273_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_273_, 0, v_toFunctor_264_);
v___f_274_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_274_, 0, v_toFunctor_264_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___f_273_);
lean_ctor_set(v___x_275_, 1, v___f_274_);
v___f_276_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_276_, 0, v_toSeqRight_267_);
v___f_277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_277_, 0, v_toSeqLeft_266_);
v___f_278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_278_, 0, v_toSeq_265_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v___f_276_);
lean_ctor_set(v___x_269_, 3, v___f_277_);
lean_ctor_set(v___x_269_, 2, v___f_278_);
lean_ctor_set(v___x_269_, 1, v___f_271_);
lean_ctor_set(v___x_269_, 0, v___x_275_);
v___x_280_ = v___x_269_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___f_271_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v___f_278_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v___f_277_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v___f_276_);
v___x_280_ = v_reuseFailAlloc_288_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_282_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___f_272_);
lean_ctor_set(v___x_262_, 0, v___x_280_);
v___x_282_ = v___x_262_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___f_272_);
v___x_282_ = v_reuseFailAlloc_287_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_5476__overap_285_; lean_object* v___x_286_; 
v___x_283_ = lean_box(0);
v___x_284_ = l_instInhabitedOfMonad___redArg(v___x_282_, v___x_283_);
v___x_5476__overap_285_ = lean_panic_fn_borrowed(v___x_284_, v_msg_228_);
lean_dec(v___x_284_);
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
v___x_286_ = lean_apply_5(v___x_5476__overap_285_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, lean_box(0));
return v___x_286_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5___boxed(lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5(v_msg_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4_spec__7(lean_object* v_msgData_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v_env_313_; uint8_t v___x_314_; lean_object* v_env_315_; lean_object* v___x_316_; lean_object* v_toCold_317_; lean_object* v_mctx_318_; lean_object* v_lctx_319_; lean_object* v_options_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_312_ = lean_st_ref_get(v___y_310_);
v_env_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc_ref(v_env_313_);
lean_dec(v___x_312_);
v___x_314_ = 0;
v_env_315_ = l_Lean_Environment_setRecordingDeps(v_env_313_, v___x_314_);
v___x_316_ = lean_st_ref_get(v___y_308_);
v_toCold_317_ = lean_ctor_get(v___y_309_, 0);
v_mctx_318_ = lean_ctor_get(v___x_316_, 0);
lean_inc_ref(v_mctx_318_);
lean_dec(v___x_316_);
v_lctx_319_ = lean_ctor_get(v___y_307_, 2);
v_options_320_ = lean_ctor_get(v_toCold_317_, 2);
lean_inc_ref(v_options_320_);
lean_inc_ref(v_lctx_319_);
v___x_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_321_, 0, v_env_315_);
lean_ctor_set(v___x_321_, 1, v_mctx_318_);
lean_ctor_set(v___x_321_, 2, v_lctx_319_);
lean_ctor_set(v___x_321_, 3, v_options_320_);
v___x_322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_msgData_306_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4_spec__7___boxed(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4_spec__7(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___redArg(lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_ref_337_; lean_object* v___x_338_; lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_347_; 
v_ref_337_ = lean_ctor_get(v___y_334_, 2);
v___x_338_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4_spec__7(v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_347_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_inc(v_ref_337_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_ref_337_);
lean_ctor_set(v___x_343_, 1, v_a_339_);
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 1);
lean_ctor_set(v___x_341_, 0, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___redArg___boxed(lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___redArg(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_354_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__0));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__3(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__2));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__7(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_364_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__6));
v___x_365_ = lean_unsigned_to_nat(11u);
v___x_366_ = lean_unsigned_to_nat(122u);
v___x_367_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__5));
v___x_368_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__4));
v___x_369_ = l_mkPanicMessageWithDecl(v___x_368_, v___x_367_, v___x_366_, v___x_365_, v___x_364_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3(lean_object* v_constName_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_384_; lean_object* v_env_385_; uint8_t v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_st_ref_get(v___y_374_);
v_env_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc_ref(v_env_385_);
lean_dec(v___x_384_);
v___x_386_ = 0;
lean_inc(v_constName_370_);
v___x_387_ = l_Lean_Environment_findAsync_x3f(v_env_385_, v_constName_370_, v___x_386_);
if (lean_obj_tag(v___x_387_) == 1)
{
lean_object* v_val_388_; uint8_t v_kind_389_; 
v_val_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v___x_387_, 1);
v_kind_389_ = lean_ctor_get_uint8(v_val_388_, sizeof(void*)*3);
if (v_kind_389_ == 6)
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_388_);
if (lean_obj_tag(v___x_390_) == 6)
{
lean_object* v_val_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_constName_370_);
v_val_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_val_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 0);
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_val_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref(v___x_390_);
v___x_399_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__7);
v___x_400_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__5(v___x_399_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
if (lean_obj_tag(v_a_401_) == 0)
{
lean_del_object(v___x_403_);
goto v___jp_376_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; 
lean_dec(v_constName_370_);
v_val_405_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v_a_401_, 1);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v_val_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_val_405_);
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
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_constName_370_);
v_a_410_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_400_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_400_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
else
{
lean_dec(v_val_388_);
goto v___jp_376_;
}
}
else
{
lean_dec(v___x_387_);
goto v___jp_376_;
}
v___jp_376_:
{
lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_377_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1);
v___x_378_ = 0;
v___x_379_ = l_Lean_MessageData_ofConstName(v_constName_370_, v___x_378_);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_377_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__3);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___redArg(v___x_382_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___boxed(lean_object* v_constName_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3(v_constName_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_424_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__3(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__2));
v___x_429_ = lean_unsigned_to_nat(10u);
v___x_430_ = lean_unsigned_to_nat(75u);
v___x_431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_433_ = l_mkPanicMessageWithDecl(v___x_432_, v___x_431_, v___x_430_, v___x_429_, v___x_428_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__4(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_434_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__6));
v___x_435_ = lean_unsigned_to_nat(65u);
v___x_436_ = lean_unsigned_to_nat(84u);
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_439_ = l_mkPanicMessageWithDecl(v___x_438_, v___x_437_, v___x_436_, v___x_435_, v___x_434_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__6(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__5));
v___x_442_ = lean_unsigned_to_nat(12u);
v___x_443_ = lean_unsigned_to_nat(80u);
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_446_ = l_mkPanicMessageWithDecl(v___x_445_, v___x_444_, v___x_443_, v___x_442_, v___x_441_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0(lean_object* v___x_447_, lean_object* v_ys_448_, lean_object* v_mr_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_Expr_isApp(v_mr_449_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__3);
v___x_457_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__2(v___x_456_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = l_Lean_Expr_appArg_x21(v_mr_449_);
v___x_459_ = l_Lean_Expr_isFVar(v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = l_Lean_Expr_getAppFn(v___x_458_);
lean_dec_ref(v___x_458_);
v___x_461_ = l_Lean_Expr_constName_x3f(v___x_460_);
lean_dec_ref(v___x_460_);
if (lean_obj_tag(v___x_461_) == 1)
{
lean_object* v_val_462_; lean_object* v___x_463_; 
v_val_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_n(v_val_462_, 2);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3(v_val_462_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_473_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_473_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_numFields_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v_numFields_468_ = lean_ctor_get(v_a_464_, 4);
lean_inc(v_numFields_468_);
lean_dec(v_a_464_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v_val_462_);
lean_ctor_set(v___x_469_, 1, v_numFields_468_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_469_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_val_462_);
v_a_474_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_463_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_463_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v___x_461_);
v___x_482_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__4);
v___x_483_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__2(v___x_482_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_483_;
}
}
else
{
uint8_t v___x_484_; 
v___x_484_ = lean_expr_eqv(v___x_458_, v___x_447_);
lean_dec_ref(v___x_458_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__6);
v___x_486_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__2(v___x_485_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_array_get_size(v_ys_448_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___boxed(lean_object* v___x_490_, lean_object* v_ys_491_, lean_object* v_mr_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0(v___x_490_, v_ys_491_, v_mr_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec_ref(v_mr_492_);
lean_dec_ref(v_ys_491_);
lean_dec_ref(v___x_490_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7(lean_object* v_val_499_, lean_object* v_a_500_, lean_object* v___x_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_bs_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v___x_501_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_bs_504_);
return v___x_511_;
}
else
{
lean_object* v___f_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_v_515_; lean_object* v___x_516_; lean_object* v_bs_x27_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; 
lean_inc_ref(v___x_501_);
v___f_512_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___boxed), 8, 1);
lean_closure_set(v___f_512_, 0, v___x_501_);
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = l_Lean_instInhabitedExpr;
v_v_515_ = lean_array_uget(v_bs_504_, v_i_503_);
v___x_516_ = lean_unsigned_to_nat(0u);
v_bs_x27_517_ = lean_array_uset(v_bs_504_, v_i_503_, v___x_516_);
v___x_518_ = lean_nat_sub(v_v_515_, v_val_499_);
lean_dec(v_v_515_);
v___x_519_ = lean_nat_sub(v___x_518_, v___x_513_);
lean_dec(v___x_518_);
v___x_520_ = lean_array_get_borrowed(v___x_514_, v_a_500_, v___x_519_);
lean_dec(v___x_519_);
v___x_521_ = 0;
lean_inc(v___x_520_);
v___x_522_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg(v___x_520_, v___f_512_, v___x_521_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_add(v_i_503_, v___x_524_);
v___x_526_ = lean_array_uset(v_bs_x27_517_, v_i_503_, v_a_523_);
v_i_503_ = v___x_525_;
v_bs_504_ = v___x_526_;
goto _start;
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v_bs_x27_517_);
lean_dec_ref(v___x_501_);
v_a_528_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_522_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_522_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___boxed(lean_object* v_val_536_, lean_object* v_a_537_, lean_object* v___x_538_, lean_object* v_sz_539_, lean_object* v_i_540_, lean_object* v_bs_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
size_t v_sz_boxed_547_; size_t v_i_boxed_548_; lean_object* v_res_549_; 
v_sz_boxed_547_ = lean_unbox_usize(v_sz_539_);
lean_dec(v_sz_539_);
v_i_boxed_548_ = lean_unbox_usize(v_i_540_);
lean_dec(v_i_540_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7(v_val_536_, v_a_537_, v___x_538_, v_sz_boxed_547_, v_i_boxed_548_, v_bs_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec_ref(v_a_537_);
lean_dec(v_val_536_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__4(size_t v_sz_550_, size_t v_i_551_, lean_object* v_bs_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_lt(v_i_551_, v_sz_550_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v_bs_552_);
return v___x_559_;
}
else
{
lean_object* v_v_560_; lean_object* v___x_561_; lean_object* v_bs_x27_562_; lean_object* v___x_563_; 
v_v_560_ = lean_array_uget(v_bs_552_, v_i_551_);
v___x_561_ = lean_unsigned_to_nat(0u);
v_bs_x27_562_ = lean_array_uset(v_bs_552_, v_i_551_, v___x_561_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
v___x_563_ = lean_infer_type(v_v_560_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_add(v_i_551_, v___x_565_);
v___x_567_ = lean_array_uset(v_bs_x27_562_, v_i_551_, v_a_564_);
v_i_551_ = v___x_566_;
v_bs_552_ = v___x_567_;
goto _start;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec_ref(v_bs_x27_562_);
v_a_569_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_563_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_563_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__4___boxed(lean_object* v_sz_577_, lean_object* v_i_578_, lean_object* v_bs_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_577_);
lean_dec(v_sz_577_);
v_i_boxed_586_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__4(v_sz_boxed_585_, v_i_boxed_586_, v_bs_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_587_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_589_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___lam__0___closed__0));
v___x_590_ = lean_unsigned_to_nat(6u);
v___x_591_ = lean_unsigned_to_nat(63u);
v___x_592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_594_ = l_mkPanicMessageWithDecl(v___x_593_, v___x_592_, v___x_591_, v___x_590_, v___x_589_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_596_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___lam__0___closed__2));
v___x_597_ = lean_unsigned_to_nat(6u);
v___x_598_ = lean_unsigned_to_nat(64u);
v___x_599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_601_ = l_mkPanicMessageWithDecl(v___x_600_, v___x_599_, v___x_598_, v___x_597_, v___x_596_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___lam__0___closed__4));
v___x_604_ = lean_unsigned_to_nat(6u);
v___x_605_ = lean_unsigned_to_nat(65u);
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_608_ = l_mkPanicMessageWithDecl(v___x_607_, v___x_606_, v___x_605_, v___x_604_, v___x_603_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__7(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_611_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__6));
v___x_612_ = lean_unsigned_to_nat(76u);
v___x_613_ = lean_unsigned_to_nat(68u);
v___x_614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_616_ = l_mkPanicMessageWithDecl(v___x_615_, v___x_614_, v___x_613_, v___x_612_, v___x_611_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__8(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_617_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__6));
v___x_618_ = lean_unsigned_to_nat(51u);
v___x_619_ = lean_unsigned_to_nat(67u);
v___x_620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_622_ = l_mkPanicMessageWithDecl(v___x_621_, v___x_620_, v___x_619_, v___x_618_, v___x_617_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___lam__0___closed__9(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_623_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__6));
v___x_624_ = lean_unsigned_to_nat(49u);
v___x_625_ = lean_unsigned_to_nat(66u);
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__1));
v___x_627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7___lam__0___closed__0));
v___x_628_ = l_mkPanicMessageWithDecl(v___x_627_, v___x_626_, v___x_625_, v___x_624_, v___x_623_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___lam__0(lean_object* v___x_629_, lean_object* v_declName_630_, lean_object* v_xs_631_, lean_object* v_r_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
uint8_t v___x_638_; 
v___x_638_ = l_Lean_Expr_isApp(v_r_632_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v_declName_630_);
v___x_639_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__1, &l_Lean_getCasesInfo_x3f___lam__0___closed__1_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__1);
v___x_640_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__0(v___x_639_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = l_Lean_Expr_appArg_x21(v_r_632_);
v___x_642_ = l_Lean_Expr_isFVar(v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec_ref(v___x_641_);
lean_dec(v_declName_630_);
v___x_643_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__3, &l_Lean_getCasesInfo_x3f___lam__0___closed__3_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__3);
v___x_644_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__0(v___x_643_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = l_Lean_Expr_getAppFn(v_r_632_);
v___x_646_ = l_Lean_Expr_isFVar(v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec_ref(v___x_645_);
lean_dec_ref(v___x_641_);
lean_dec(v_declName_630_);
v___x_647_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__5, &l_Lean_getCasesInfo_x3f___lam__0___closed__5_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__5);
v___x_648_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__0(v___x_647_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1(v_xs_631_, v___x_641_);
lean_dec_ref(v___x_641_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_val_650_; lean_object* v___x_651_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = l_Array_idxOf_x3f___at___00Lean_getCasesInfo_x3f_spec__1(v_xs_631_, v___x_645_);
if (lean_obj_tag(v___x_651_) == 1)
{
lean_object* v_val_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_732_; 
v_val_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_732_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_732_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_val_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_732_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_array_get_size(v_xs_631_);
v___x_657_ = lean_array_get_borrowed(v___x_629_, v_xs_631_, v_val_650_);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc(v___x_657_);
v___x_658_ = lean_infer_type(v___x_657_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = l_Lean_Expr_getAppFn(v_a_659_);
lean_dec(v_a_659_);
v___x_661_ = l_Lean_Expr_constName_x3f(v___x_660_);
lean_dec_ref(v___x_660_);
if (lean_obj_tag(v___x_661_) == 1)
{
lean_object* v_val_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_721_; 
v_val_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_721_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_721_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_val_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_721_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; size_t v_sz_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_add(v_val_650_, v___x_666_);
v___x_668_ = l_Array_extract___redArg(v_xs_631_, v___x_667_, v___x_656_);
v_sz_669_ = lean_array_size(v___x_668_);
v___x_670_ = ((size_t)0ULL);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__4(v_sz_669_, v___x_670_, v___x_668_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___y_674_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_705_ = lean_array_get_size(v_a_672_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_nat_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
if (v___x_646_ == 0)
{
lean_dec_ref(v___x_645_);
v___y_674_ = v___x_666_;
goto v___jp_673_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_708_ = lean_array_get_borrowed(v___x_629_, v_a_672_, v___x_706_);
v___x_709_ = l_Lean_Expr_getForallBody(v___x_708_);
v___x_710_ = l_Lean_Expr_getAppFn(v___x_709_);
lean_dec_ref(v___x_709_);
v___x_711_ = lean_expr_eqv(v___x_710_, v___x_645_);
lean_dec_ref(v___x_645_);
lean_dec_ref(v___x_710_);
if (v___x_711_ == 0)
{
if (v___x_646_ == 0)
{
v___y_674_ = v___x_666_;
goto v___jp_673_;
}
else
{
lean_object* v___x_712_; 
v___x_712_ = lean_unsigned_to_nat(2u);
v___y_674_ = v___x_712_;
goto v___jp_673_;
}
}
else
{
v___y_674_ = v___x_666_;
goto v___jp_673_;
}
}
}
else
{
lean_dec_ref(v___x_645_);
v___y_674_ = v___x_666_;
goto v___jp_673_;
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_675_ = lean_nat_add(v_val_650_, v___y_674_);
lean_inc(v___x_675_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_656_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_675_);
v___x_678_ = v___x_664_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_675_);
v___x_678_ = v_reuseFailAlloc_704_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; size_t v_sz_682_; lean_object* v___x_683_; 
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_656_);
v___x_680_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___lam__0___closed__6));
v___x_681_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__6___redArg(v___x_679_, v___x_680_);
v_sz_682_ = lean_array_size(v___x_681_);
lean_inc(v___x_657_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_getCasesInfo_x3f_spec__7(v_val_650_, v_a_672_, v___x_657_, v_sz_682_, v___x_670_, v___x_681_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v_a_672_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_695_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_695_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_688_, 0, v_declName_630_);
lean_ctor_set(v___x_688_, 1, v_val_662_);
lean_ctor_set(v___x_688_, 2, v___x_656_);
lean_ctor_set(v___x_688_, 3, v_val_650_);
lean_ctor_set(v___x_688_, 4, v_val_652_);
lean_ctor_set(v___x_688_, 5, v___x_676_);
lean_ctor_set(v___x_688_, 6, v_a_684_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_688_);
v___x_690_ = v___x_654_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_690_);
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
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
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref_known(v___x_676_, 2);
lean_dec(v_val_662_);
lean_del_object(v___x_654_);
lean_dec(v_val_652_);
lean_dec(v_val_650_);
lean_dec(v_declName_630_);
v_a_696_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_683_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_683_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_del_object(v___x_664_);
lean_dec(v_val_662_);
lean_del_object(v___x_654_);
lean_dec(v_val_652_);
lean_dec(v_val_650_);
lean_dec_ref(v___x_645_);
lean_dec(v_declName_630_);
v_a_713_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_671_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_671_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v___x_661_);
lean_del_object(v___x_654_);
lean_dec(v_val_652_);
lean_dec(v_val_650_);
lean_dec_ref(v___x_645_);
lean_dec(v_declName_630_);
v___x_722_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__7, &l_Lean_getCasesInfo_x3f___lam__0___closed__7_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__7);
v___x_723_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__0(v___x_722_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_723_;
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_del_object(v___x_654_);
lean_dec(v_val_652_);
lean_dec(v_val_650_);
lean_dec_ref(v___x_645_);
lean_dec(v_declName_630_);
v_a_724_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_658_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_658_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v___x_651_);
lean_dec(v_val_650_);
lean_dec_ref(v___x_645_);
lean_dec(v_declName_630_);
v___x_733_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__8, &l_Lean_getCasesInfo_x3f___lam__0___closed__8_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__8);
v___x_734_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__0(v___x_733_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_734_;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v___x_649_);
lean_dec_ref(v___x_645_);
lean_dec(v_declName_630_);
v___x_735_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___lam__0___closed__9, &l_Lean_getCasesInfo_x3f___lam__0___closed__9_once, _init_l_Lean_getCasesInfo_x3f___lam__0___closed__9);
v___x_736_ = l_panic___at___00Lean_getCasesInfo_x3f_spec__0(v___x_735_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___lam__0___boxed(lean_object* v___x_737_, lean_object* v_declName_738_, lean_object* v_xs_739_, lean_object* v_r_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_getCasesInfo_x3f___lam__0(v___x_737_, v_declName_738_, v_xs_739_, v_r_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v_r_740_);
lean_dec_ref(v_xs_739_);
lean_dec_ref(v___x_737_);
return v_res_746_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0(void){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_747_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_751_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
lean_ctor_set(v___x_753_, 2, v___x_752_);
lean_ctor_set(v___x_753_, 3, v___x_752_);
lean_ctor_set(v___x_753_, 4, v___x_751_);
lean_ctor_set(v___x_753_, 5, v___x_751_);
lean_ctor_set(v___x_753_, 6, v___x_751_);
lean_ctor_set(v___x_753_, 7, v___x_751_);
lean_ctor_set(v___x_753_, 8, v___x_751_);
lean_ctor_set(v___x_753_, 9, v___x_751_);
lean_ctor_set(v___x_753_, 10, v___x_751_);
lean_ctor_set(v___x_753_, 11, v___x_750_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__3(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_unsigned_to_nat(32u);
v___x_755_ = lean_mk_empty_array_with_capacity(v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4(void){
_start:
{
size_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_757_ = ((size_t)5ULL);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = lean_unsigned_to_nat(32u);
v___x_760_ = lean_mk_empty_array_with_capacity(v___x_759_);
v___x_761_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__3);
v___x_762_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
lean_ctor_set(v___x_762_, 2, v___x_758_);
lean_ctor_set(v___x_762_, 3, v___x_758_);
lean_ctor_set_usize(v___x_762_, 4, v___x_757_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_763_ = lean_box(1);
v___x_764_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4);
v___x_765_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__1);
v___x_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
lean_ctor_set(v___x_766_, 2, v___x_763_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20(lean_object* v_msgData_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; lean_object* v_toCold_772_; lean_object* v_env_773_; lean_object* v_options_774_; uint8_t v___x_775_; lean_object* v_env_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_771_ = lean_st_ref_get(v___y_769_);
v_toCold_772_ = lean_ctor_get(v___y_768_, 0);
v_env_773_ = lean_ctor_get(v___x_771_, 0);
lean_inc_ref(v_env_773_);
lean_dec(v___x_771_);
v_options_774_ = lean_ctor_get(v_toCold_772_, 2);
v___x_775_ = 0;
v_env_776_ = l_Lean_Environment_setRecordingDeps(v_env_773_, v___x_775_);
v___x_777_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2);
v___x_778_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5);
lean_inc_ref(v_options_774_);
v___x_779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_779_, 0, v_env_776_);
lean_ctor_set(v___x_779_, 1, v___x_777_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
lean_ctor_set(v___x_779_, 3, v_options_774_);
v___x_780_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v_msgData_767_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___boxed(lean_object* v_msgData_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20(v_msgData_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___redArg(lean_object* v_msg_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_ref_791_; lean_object* v___x_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_ref_791_ = lean_ctor_get(v___y_788_, 2);
v___x_792_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20(v_msg_787_, v___y_788_, v___y_789_);
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_inc(v_ref_791_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_ref_791_);
lean_ctor_set(v___x_797_, 1, v_a_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 1);
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___redArg(v_msg_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___redArg(lean_object* v_ref_807_, lean_object* v_msg_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_toCold_812_; lean_object* v_currRecDepth_813_; lean_object* v_ref_814_; uint16_t v_optionFlags_815_; uint8_t v_suppressElabErrors_816_; uint8_t v_isRecordingDeps_817_; lean_object* v_ref_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_toCold_812_ = lean_ctor_get(v___y_809_, 0);
v_currRecDepth_813_ = lean_ctor_get(v___y_809_, 1);
v_ref_814_ = lean_ctor_get(v___y_809_, 2);
v_optionFlags_815_ = lean_ctor_get_uint16(v___y_809_, sizeof(void*)*3);
v_suppressElabErrors_816_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*3 + 2);
v_isRecordingDeps_817_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*3 + 3);
v_ref_818_ = l_Lean_replaceRef(v_ref_807_, v_ref_814_);
lean_inc(v_currRecDepth_813_);
lean_inc_ref(v_toCold_812_);
v___x_819_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_819_, 0, v_toCold_812_);
lean_ctor_set(v___x_819_, 1, v_currRecDepth_813_);
lean_ctor_set(v___x_819_, 2, v_ref_818_);
lean_ctor_set_uint16(v___x_819_, sizeof(void*)*3, v_optionFlags_815_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 2, v_suppressElabErrors_816_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 3, v_isRecordingDeps_817_);
v___x_820_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___redArg(v_msg_808_, v___x_819_, v___y_810_);
lean_dec_ref_known(v___x_819_, 3);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___redArg___boxed(lean_object* v_ref_821_, lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___redArg(v_ref_821_, v_msg_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v_ref_821_);
return v_res_826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__0));
v___x_829_ = l_Lean_stringToMessageData(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__2));
v___x_832_ = l_Lean_stringToMessageData(v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__4));
v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_847_ = l_Lean_stringToMessageData(v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__15(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__14));
v___x_850_ = l_Lean_stringToMessageData(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__17(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__16));
v___x_853_ = l_Lean_stringToMessageData(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__19(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__18));
v___x_856_ = l_Lean_stringToMessageData(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__21(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__20));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_860_, lean_object* v_declHint_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_env_866_; uint8_t v___x_867_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_st_ref_get(v___y_862_);
v_env_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc_ref(v_env_866_);
lean_dec(v___x_865_);
v___x_867_ = l_Lean_Name_isAnonymous(v_declHint_861_);
if (v___x_867_ == 0)
{
uint8_t v_isExporting_868_; 
v_isExporting_868_ = lean_ctor_get_uint8(v_env_866_, sizeof(void*)*13);
if (v_isExporting_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec_ref(v_env_866_);
lean_dec(v_declHint_861_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_msg_860_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; uint8_t v___x_871_; 
lean_inc_ref(v_env_866_);
v___x_870_ = l_Lean_Environment_setExporting(v_env_866_, v___x_867_);
lean_inc(v_declHint_861_);
lean_inc_ref(v___x_870_);
v___x_871_ = l_Lean_Environment_contains(v___x_870_, v_declHint_861_, v_isExporting_868_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec_ref(v___x_870_);
lean_dec_ref(v_env_866_);
lean_dec(v_declHint_861_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_msg_860_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_c_878_; lean_object* v___x_879_; 
v___x_873_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__2);
v___x_874_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__5);
v___x_875_ = l_Lean_Options_empty;
v___x_876_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_876_, 0, v___x_870_);
lean_ctor_set(v___x_876_, 1, v___x_873_);
lean_ctor_set(v___x_876_, 2, v___x_874_);
lean_ctor_set(v___x_876_, 3, v___x_875_);
lean_inc(v_declHint_861_);
v___x_877_ = l_Lean_MessageData_ofConstName(v_declHint_861_, v___x_867_);
v_c_878_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_878_, 0, v___x_876_);
lean_ctor_set(v_c_878_, 1, v___x_877_);
v___x_879_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_866_, v_declHint_861_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec_ref(v_env_866_);
lean_dec(v_declHint_861_);
v___x_880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_c_878_);
v___x_882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_MessageData_note(v___x_883_);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v_msg_860_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
else
{
lean_object* v_val_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_943_; 
v_val_887_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_943_ == 0)
{
v___x_889_ = v___x_879_;
v_isShared_890_ = v_isSharedCheck_943_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_val_887_);
lean_dec(v___x_879_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_943_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v_modules_892_; lean_object* v_moduleNames_893_; lean_object* v_mod_894_; uint8_t v___y_896_; uint8_t v___x_926_; 
v___x_891_ = l_Lean_Environment_header(v_env_866_);
lean_dec_ref(v_env_866_);
v_modules_892_ = lean_ctor_get(v___x_891_, 3);
lean_inc_ref(v_modules_892_);
v_moduleNames_893_ = lean_ctor_get(v___x_891_, 4);
lean_inc_ref(v_moduleNames_893_);
lean_dec_ref(v___x_891_);
v_mod_894_ = lean_array_get(v___x_864_, v_moduleNames_893_, v_val_887_);
lean_dec_ref(v_moduleNames_893_);
v___x_926_ = l_Lean_isPrivateName(v_declHint_861_);
lean_dec(v_declHint_861_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_array_get_size(v_modules_892_);
v___x_928_ = lean_nat_dec_lt(v_val_887_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec_ref(v_modules_892_);
lean_dec(v_val_887_);
v___y_896_ = v___x_926_;
goto v___jp_895_;
}
else
{
lean_object* v___x_929_; lean_object* v_toImport_930_; uint8_t v_isExported_931_; 
v___x_929_ = lean_array_fget(v_modules_892_, v_val_887_);
lean_dec(v_val_887_);
lean_dec_ref(v_modules_892_);
v_toImport_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc_ref(v_toImport_930_);
lean_dec(v___x_929_);
v_isExported_931_ = lean_ctor_get_uint8(v_toImport_930_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_930_);
v___y_896_ = v_isExported_931_;
goto v___jp_895_;
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec_ref(v_modules_892_);
lean_del_object(v___x_889_);
lean_dec(v_val_887_);
v___x_932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v_c_878_);
v___x_934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__19);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_MessageData_ofName(v_mod_894_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__21);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_MessageData_note(v___x_939_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v_msg_860_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
v___jp_895_:
{
if (v___y_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_c_878_);
v___x_899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_MessageData_ofName(v_mod_894_);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_MessageData_note(v___x_904_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v_msg_860_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 0);
lean_ctor_set(v___x_889_, 0, v___x_906_);
v___x_908_ = v___x_889_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v_c_878_);
v___x_912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_MessageData_ofName(v_mod_894_);
lean_inc_ref(v___x_914_);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__15);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_914_);
v___x_919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___closed__17);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_MessageData_note(v___x_920_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v_msg_860_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 0);
lean_ctor_set(v___x_889_, 0, v___x_922_);
v___x_924_ = v___x_889_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
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
lean_object* v___x_944_; 
lean_dec_ref(v_env_866_);
lean_dec(v_declHint_861_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_msg_860_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_945_, lean_object* v_declHint_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_945_, v_declHint_946_, v___y_947_);
lean_dec(v___y_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16(lean_object* v_msg_950_, lean_object* v_declHint_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v___x_955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_950_, v_declHint_951_, v___y_953_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = l_Lean_unknownIdentifierMessageTag;
v___x_961_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v_a_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_966_, lean_object* v_declHint_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16(v_msg_966_, v_declHint_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___redArg(lean_object* v_ref_972_, lean_object* v_msg_973_, lean_object* v_declHint_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_a_979_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16(v_msg_973_, v_declHint_974_, v___y_975_, v___y_976_);
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref(v___x_978_);
v___x_980_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___redArg(v_ref_972_, v_a_979_, v___y_975_, v___y_976_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___redArg___boxed(lean_object* v_ref_981_, lean_object* v_msg_982_, lean_object* v_declHint_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___redArg(v_ref_981_, v_msg_982_, v_declHint_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v_ref_981_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__0));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg(lean_object* v_ref_991_, lean_object* v_constName_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_996_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___closed__1);
v___x_997_ = 0;
lean_inc(v_constName_992_);
v___x_998_ = l_Lean_MessageData_ofConstName(v_constName_992_, v___x_997_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_996_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3___closed__1);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___redArg(v_ref_991_, v___x_1001_, v_constName_992_, v___y_993_, v___y_994_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg___boxed(lean_object* v_ref_1003_, lean_object* v_constName_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg(v_ref_1003_, v_constName_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v_ref_1003_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___redArg(lean_object* v_constName_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_ref_1013_; lean_object* v___x_1014_; 
v_ref_1013_ = lean_ctor_get(v___y_1010_, 2);
v___x_1014_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg(v_ref_1013_, v_constName_1009_, v___y_1010_, v___y_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___redArg___boxed(lean_object* v_constName_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___redArg(v_constName_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8(lean_object* v_constName_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v_env_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_st_ref_get(v___y_1022_);
v_env_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc_ref(v_env_1025_);
lean_dec(v___x_1024_);
v___x_1026_ = 0;
lean_inc(v_constName_1020_);
v___x_1027_ = l_Lean_Environment_findConstVal_x3f(v_env_1025_, v_constName_1020_, v___x_1026_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___redArg(v_constName_1020_, v___y_1021_, v___y_1022_);
return v___x_1028_;
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v_constName_1020_);
v_val_1029_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1027_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_val_1029_);
lean_dec(v___x_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 0);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_val_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8___boxed(lean_object* v_constName_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8(v_constName_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1041_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__0(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__0);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__1(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1044_ = lean_box(1);
v___x_1045_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4);
v___x_1046_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__0, &l_Lean_getCasesInfo_x3f___closed__0_once, _init_l_Lean_getCasesInfo_x3f___closed__0);
v___x_1047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1045_);
lean_ctor_set(v___x_1047_, 2, v___x_1044_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__3(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1050_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1051_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__0, &l_Lean_getCasesInfo_x3f___closed__0_once, _init_l_Lean_getCasesInfo_x3f___closed__0);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
lean_ctor_set(v___x_1053_, 2, v___x_1052_);
lean_ctor_set(v___x_1053_, 3, v___x_1052_);
lean_ctor_set(v___x_1053_, 4, v___x_1051_);
lean_ctor_set(v___x_1053_, 5, v___x_1051_);
lean_ctor_set(v___x_1053_, 6, v___x_1051_);
lean_ctor_set(v___x_1053_, 7, v___x_1051_);
lean_ctor_set(v___x_1053_, 8, v___x_1051_);
lean_ctor_set(v___x_1053_, 9, v___x_1051_);
lean_ctor_set(v___x_1053_, 10, v___x_1051_);
lean_ctor_set(v___x_1053_, 11, v___x_1050_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__4(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__0, &l_Lean_getCasesInfo_x3f___closed__0_once, _init_l_Lean_getCasesInfo_x3f___closed__0);
v___x_1055_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
lean_ctor_set(v___x_1055_, 2, v___x_1054_);
lean_ctor_set(v___x_1055_, 3, v___x_1054_);
lean_ctor_set(v___x_1055_, 4, v___x_1054_);
lean_ctor_set(v___x_1055_, 5, v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__5(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__0, &l_Lean_getCasesInfo_x3f___closed__0_once, _init_l_Lean_getCasesInfo_x3f___closed__0);
v___x_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
lean_ctor_set(v___x_1057_, 2, v___x_1056_);
lean_ctor_set(v___x_1057_, 3, v___x_1056_);
lean_ctor_set(v___x_1057_, 4, v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_getCasesInfo_x3f___closed__6(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1058_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__5, &l_Lean_getCasesInfo_x3f___closed__5_once, _init_l_Lean_getCasesInfo_x3f___closed__5);
v___x_1059_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19_spec__20___closed__4);
v___x_1060_ = lean_box(1);
v___x_1061_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__4, &l_Lean_getCasesInfo_x3f___closed__4_once, _init_l_Lean_getCasesInfo_x3f___closed__4);
v___x_1062_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__3, &l_Lean_getCasesInfo_x3f___closed__3_once, _init_l_Lean_getCasesInfo_x3f___closed__3);
v___x_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_1061_);
lean_ctor_set(v___x_1063_, 2, v___x_1060_);
lean_ctor_set(v___x_1063_, 3, v___x_1059_);
lean_ctor_set(v___x_1063_, 4, v___x_1058_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f(lean_object* v_declName_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_env_1072_; uint8_t v___x_1073_; 
v___x_1068_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_declName_1064_, 2);
v___f_1069_ = lean_alloc_closure((void*)(l_Lean_getCasesInfo_x3f___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1069_, 0, v___x_1068_);
lean_closure_set(v___f_1069_, 1, v_declName_1064_);
v___x_1070_ = lean_box(1);
v___x_1071_ = lean_st_ref_get(v_a_1066_);
v_env_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc_ref(v_env_1072_);
lean_dec(v___x_1071_);
v___x_1073_ = l_Lean_isCasesOnLike(v_env_1072_, v_declName_1064_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec_ref(v___f_1069_);
lean_dec(v_declName_1064_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8(v_declName_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v_type_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; uint8_t v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; uint64_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v_type_1078_ = lean_ctor_get(v_a_1077_, 2);
lean_inc_ref(v_type_1078_);
lean_dec(v_a_1077_);
v___x_1079_ = 0;
v___x_1080_ = 1;
v___x_1081_ = 0;
v___x_1082_ = 2;
v___x_1083_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1083_, 0, v___x_1079_);
lean_ctor_set_uint8(v___x_1083_, 1, v___x_1079_);
lean_ctor_set_uint8(v___x_1083_, 2, v___x_1079_);
lean_ctor_set_uint8(v___x_1083_, 3, v___x_1079_);
lean_ctor_set_uint8(v___x_1083_, 4, v___x_1079_);
lean_ctor_set_uint8(v___x_1083_, 5, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 6, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 7, v___x_1079_);
lean_ctor_set_uint8(v___x_1083_, 8, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 9, v___x_1080_);
lean_ctor_set_uint8(v___x_1083_, 10, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, 11, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 12, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 13, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 14, v___x_1082_);
lean_ctor_set_uint8(v___x_1083_, 15, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 16, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 17, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 18, v___x_1073_);
lean_ctor_set_uint8(v___x_1083_, 19, v___x_1079_);
v___x_1084_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1083_);
v___x_1085_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set_uint64(v___x_1085_, sizeof(void*)*1, v___x_1084_);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__1, &l_Lean_getCasesInfo_x3f___closed__1_once, _init_l_Lean_getCasesInfo_x3f___closed__1);
v___x_1088_ = ((lean_object*)(l_Lean_getCasesInfo_x3f___closed__2));
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1090_, 0, v___x_1085_);
lean_ctor_set(v___x_1090_, 1, v___x_1070_);
lean_ctor_set(v___x_1090_, 2, v___x_1087_);
lean_ctor_set(v___x_1090_, 3, v___x_1088_);
lean_ctor_set(v___x_1090_, 4, v___x_1089_);
lean_ctor_set(v___x_1090_, 5, v___x_1086_);
lean_ctor_set(v___x_1090_, 6, v___x_1089_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*7, v___x_1079_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*7 + 1, v___x_1079_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*7 + 2, v___x_1079_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*7 + 3, v___x_1073_);
v___x_1091_ = lean_obj_once(&l_Lean_getCasesInfo_x3f___closed__6, &l_Lean_getCasesInfo_x3f___closed__6_once, _init_l_Lean_getCasesInfo_x3f___closed__6);
v___x_1092_ = lean_st_mk_ref(v___x_1091_);
v___x_1093_ = l_Lean_Meta_forallTelescope___at___00Lean_getCasesInfo_x3f_spec__5___redArg(v_type_1078_, v___f_1069_, v___x_1079_, v___x_1090_, v___x_1092_, v_a_1065_, v_a_1066_);
lean_dec_ref_known(v___x_1090_, 7);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_st_ref_get(v___x_1092_);
lean_dec(v___x_1092_);
lean_dec(v___x_1098_);
if (v_isShared_1097_ == 0)
{
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1094_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_dec(v___x_1092_);
return v___x_1093_;
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v___f_1069_);
v_a_1103_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1076_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1076_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getCasesInfo_x3f___boxed(lean_object* v_declName_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_getCasesInfo_x3f(v_declName_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__6(lean_object* v_inst_1116_, lean_object* v_R_1117_, lean_object* v_a_1118_, lean_object* v_b_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_getCasesInfo_x3f_spec__6___redArg(v_a_1118_, v_b_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4(lean_object* v_00_u03b1_1121_, lean_object* v_msg_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___redArg(v_msg_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_msg_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_getCasesInfo_x3f_spec__3_spec__4(v_00_u03b1_1129_, v_msg_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11(lean_object* v_00_u03b1_1137_, lean_object* v_constName_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___redArg(v_constName_1138_, v___y_1139_, v___y_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_constName_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11(v_00_u03b1_1143_, v_constName_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14(lean_object* v_00_u03b1_1149_, lean_object* v_ref_1150_, lean_object* v_constName_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___redArg(v_ref_1150_, v_constName_1151_, v___y_1152_, v___y_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_ref_1157_, lean_object* v_constName_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14(v_00_u03b1_1156_, v_ref_1157_, v_constName_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v_ref_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15(lean_object* v_00_u03b1_1163_, lean_object* v_ref_1164_, lean_object* v_msg_1165_, lean_object* v_declHint_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___redArg(v_ref_1164_, v_msg_1165_, v_declHint_1166_, v___y_1167_, v___y_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_ref_1172_, lean_object* v_msg_1173_, lean_object* v_declHint_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15(v_00_u03b1_1171_, v_ref_1172_, v_msg_1173_, v_declHint_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v_ref_1172_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17(lean_object* v_msg_1179_, lean_object* v_declHint_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_1179_, v_declHint_1180_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_1185_, lean_object* v_declHint_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__16_spec__17(v_msg_1185_, v_declHint_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17(lean_object* v_00_u03b1_1191_, lean_object* v_ref_1192_, lean_object* v_msg_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___redArg(v_ref_1192_, v_msg_1193_, v___y_1194_, v___y_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_ref_1199_, lean_object* v_msg_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17(v_00_u03b1_1198_, v_ref_1199_, v_msg_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v_ref_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_1205_, lean_object* v_msg_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___redArg(v_msg_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_getCasesInfo_x3f_spec__8_spec__11_spec__14_spec__15_spec__17_spec__19(v_00_u03b1_1211_, v_msg_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1216_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CasesInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
