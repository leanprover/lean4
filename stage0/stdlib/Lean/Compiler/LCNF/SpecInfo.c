// Lean compiler output
// Module: Lean.Compiler.LCNF.SpecInfo
// Imports: public import Lean.Compiler.LCNF.FixedParams public import Lean.Compiler.LCNF.InferType
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_nat_to_int(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Compiler_hasNospecializeAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getSpecializationArgs_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Compiler_hasWeakSpecializeAttribute(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.SpecParamInfo.fixedHO"};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Compiler.LCNF.SpecParamInfo.fixedNeutral"};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Compiler.LCNF.SpecParamInfo.user"};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Compiler.LCNF.SpecParamInfo.other"};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Compiler.LCNF.SpecParamInfo.fixedInst"};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11;
static lean_once_cell_t l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo = (const lean_object*)&l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "I"};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "W"};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "H"};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "N"};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "U"};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "O"};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value;
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecEntry = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ", alreadySpecialized\? "};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", info: "};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value)} };
static const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry = (const lean_object*)&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSpecState;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecState_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries(lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "specExtension"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 125, 66, 207, 170, 81, 149, 39)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_SpecState_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specExtension;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.SpecInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Compiler.LCNF.computeSpecEntries"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_computeSpecEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_computeSpecEntries___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_computeSpecEntries___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 178, 200, 12, 6, 8, 169, 47)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(239, 10, 5, 245, 97, 204, 194, 190)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_saveSpecEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_saveSpecEntries___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "SpecInfo"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 143, 90, 20, 187, 241, 210, 130)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(72, 221, 196, 202, 242, 20, 202, 54)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 252, 235, 237, 133, 48, 182, 31)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 107, 219, 87, 200, 53, 139, 182)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 11, 76, 70, 228, 174, 143, 241)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 151, 165, 105, 57, 237, 31, 157)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 32, 108, 248, 142, 238, 193, 222)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 232, 203, 212, 181, 229, 127, 130)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 208, 136, 97, 67, 35, 203, 29)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 28, 172, 95, 144, 231, 210, 82)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 101, 36, 130, 141, 225, 110, 6)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)(((size_t)(513551779) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(142, 89, 44, 236, 61, 209, 169, 61)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 94, 100, 117, 85, 240, 197, 64)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 114, 191, 226, 45, 202, 144, 166)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 120, 192, 10, 119, 154, 32, 73)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
uint8_t v_weak_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_weak_7_ = lean_ctor_get_uint8(v_t_5_, 0);
v___x_8_ = lean_box(v_weak_7_);
v___x_9_ = lean_apply_1(v_k_6_, v___x_8_);
return v___x_9_;
}
else
{
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg___boxed(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_10_, v_k_11_);
lean_dec(v_t_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_t_21_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(lean_object* v_t_25_, lean_object* v_fixedInst_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_25_, v_fixedInst_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg___boxed(lean_object* v_t_28_, lean_object* v_fixedInst_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(v_t_28_, v_fixedInst_29_);
lean_dec(v_t_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_fixedInst_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_32_, v_fixedInst_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_fixedInst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(v_motive_36_, v_t_37_, v_h_38_, v_fixedInst_39_);
lean_dec(v_t_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(lean_object* v_t_41_, lean_object* v_fixedHO_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_41_, v_fixedHO_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg___boxed(lean_object* v_t_44_, lean_object* v_fixedHO_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(v_t_44_, v_fixedHO_45_);
lean_dec(v_t_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_fixedHO_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_48_, v_fixedHO_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___boxed(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_fixedHO_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(v_motive_52_, v_t_53_, v_h_54_, v_fixedHO_55_);
lean_dec(v_t_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(lean_object* v_t_57_, lean_object* v_fixedNeutral_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_57_, v_fixedNeutral_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg___boxed(lean_object* v_t_60_, lean_object* v_fixedNeutral_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(v_t_60_, v_fixedNeutral_61_);
lean_dec(v_t_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_fixedNeutral_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_64_, v_fixedNeutral_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_fixedNeutral_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(v_motive_68_, v_t_69_, v_h_70_, v_fixedNeutral_71_);
lean_dec(v_t_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(lean_object* v_t_73_, lean_object* v_user_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_73_, v_user_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg___boxed(lean_object* v_t_76_, lean_object* v_user_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(v_t_76_, v_user_77_);
lean_dec(v_t_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(lean_object* v_motive_79_, lean_object* v_t_80_, lean_object* v_h_81_, lean_object* v_user_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_80_, v_user_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___boxed(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_user_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(v_motive_84_, v_t_85_, v_h_86_, v_user_87_);
lean_dec(v_t_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(lean_object* v_t_89_, lean_object* v_other_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_89_, v_other_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg___boxed(lean_object* v_t_92_, lean_object* v_other_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(v_t_92_, v_other_93_);
lean_dec(v_t_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(lean_object* v_motive_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_other_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_96_, v_other_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___boxed(lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_other_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(v_motive_100_, v_t_101_, v_h_102_, v_other_103_);
lean_dec(v_t_101_);
return v_res_104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(2u);
v___x_128_ = lean_nat_to_int(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_to_int(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(lean_object* v_x_131_, lean_object* v_prec_132_){
_start:
{
lean_object* v___y_134_; lean_object* v___y_141_; lean_object* v___y_148_; lean_object* v___y_155_; 
switch(lean_obj_tag(v_x_131_))
{
case 0:
{
uint8_t v_weak_161_; lean_object* v___y_163_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_weak_161_ = lean_ctor_get_uint8(v_x_131_, 0);
v___x_171_ = lean_unsigned_to_nat(1024u);
v___x_172_ = lean_nat_dec_le(v___x_171_, v_prec_132_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_163_ = v___x_173_;
goto v___jp_162_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_163_ = v___x_174_;
goto v___jp_162_;
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_164_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10));
v___x_165_ = l_Bool_repr___redArg(v_weak_161_);
v___x_166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
lean_inc(v___y_163_);
v___x_167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_167_, 0, v___y_163_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = 0;
v___x_169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*1, v___x_168_);
v___x_170_ = l_Repr_addAppParen(v___x_169_, v_prec_132_);
return v___x_170_;
}
}
case 1:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(1024u);
v___x_176_ = lean_nat_dec_le(v___x_175_, v_prec_132_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
v___x_177_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_134_ = v___x_177_;
goto v___jp_133_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_134_ = v___x_178_;
goto v___jp_133_;
}
}
case 2:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(1024u);
v___x_180_ = lean_nat_dec_le(v___x_179_, v_prec_132_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_141_ = v___x_181_;
goto v___jp_140_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_141_ = v___x_182_;
goto v___jp_140_;
}
}
case 3:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(1024u);
v___x_184_ = lean_nat_dec_le(v___x_183_, v_prec_132_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_148_ = v___x_185_;
goto v___jp_147_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_148_ = v___x_186_;
goto v___jp_147_;
}
}
default: 
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1024u);
v___x_188_ = lean_nat_dec_le(v___x_187_, v_prec_132_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_155_ = v___x_189_;
goto v___jp_154_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_155_ = v___x_190_;
goto v___jp_154_;
}
}
}
v___jp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_135_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1));
lean_inc(v___y_134_);
v___x_136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_136_, 0, v___y_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = 0;
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_137_);
v___x_139_ = l_Repr_addAppParen(v___x_138_, v_prec_132_);
return v___x_139_;
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_142_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3));
lean_inc(v___y_141_);
v___x_143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_143_, 0, v___y_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = 0;
v___x_145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set_uint8(v___x_145_, sizeof(void*)*1, v___x_144_);
v___x_146_ = l_Repr_addAppParen(v___x_145_, v_prec_132_);
return v___x_146_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_149_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5));
lean_inc(v___y_148_);
v___x_150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_150_, 0, v___y_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = 0;
v___x_152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_151_);
v___x_153_ = l_Repr_addAppParen(v___x_152_, v_prec_132_);
return v___x_153_;
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7));
lean_inc(v___y_155_);
v___x_157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_157_, 0, v___y_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = 0;
v___x_159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_158_);
v___x_160_ = l_Repr_addAppParen(v___x_159_, v_prec_132_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___boxed(lean_object* v_x_191_, lean_object* v_prec_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(v_x_191_, v_prec_192_);
lean_dec(v_prec_192_);
lean_dec(v_x_191_);
return v_res_193_;
}
}
uint8_t l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(lean_object* v_x_196_){
_start:
{
switch(lean_obj_tag(v_x_196_))
{
case 0:
{
uint8_t v_weak_197_; 
v_weak_197_ = lean_ctor_get_uint8(v_x_196_, 0);
if (v_weak_197_ == 0)
{
uint8_t v___x_198_; 
v___x_198_ = 1;
return v___x_198_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
case 2:
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
case 4:
{
uint8_t v___x_201_; 
v___x_201_ = 0;
return v___x_201_;
}
default: 
{
uint8_t v___x_202_; 
v___x_202_ = 1;
return v___x_202_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_196_ = stack[0].m_obj;
uint8_t v_res_203_;
v_res_203_ = l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(v_x_196_);
stack->m_num = v_res_203_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization___boxed(lean_object* v_x_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(v_x_204_);
lean_dec(v_x_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1));
v___x_211_ = l_Lean_MessageData_ofFormat(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4));
v___x_216_ = l_Lean_MessageData_ofFormat(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7));
v___x_221_ = l_Lean_MessageData_ofFormat(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10));
v___x_226_ = l_Lean_MessageData_ofFormat(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13));
v___x_231_ = l_Lean_MessageData_ofFormat(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16));
v___x_236_ = l_Lean_MessageData_ofFormat(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(lean_object* v_x_237_){
_start:
{
switch(lean_obj_tag(v_x_237_))
{
case 0:
{
uint8_t v_weak_238_; 
v_weak_238_ = lean_ctor_get_uint8(v_x_237_, 0);
if (v_weak_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
return v___x_239_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
return v___x_240_;
}
}
case 1:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8);
return v___x_241_;
}
case 2:
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11);
return v___x_242_;
}
case 3:
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14);
return v___x_243_;
}
default: 
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___boxed(lean_object* v_x_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(v_x_245_);
lean_dec(v_x_245_);
return v_res_246_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1(lean_object* v___f_265_, lean_object* v_x_266_){
_start:
{
lean_object* v_declName_267_; lean_object* v_paramsInfo_268_; uint8_t v_alreadySpecialized_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___y_274_; 
v_declName_267_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_declName_267_);
v_paramsInfo_268_ = lean_ctor_get(v_x_266_, 1);
lean_inc_ref(v_paramsInfo_268_);
v_alreadySpecialized_269_ = lean_ctor_get_uint8(v_x_266_, sizeof(void*)*2);
lean_dec_ref(v_x_266_);
v___x_270_ = l_Lean_MessageData_ofName(v_declName_267_);
v___x_271_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1, &l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
if (v_alreadySpecialized_269_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4));
v___y_274_ = v___x_285_;
goto v___jp_273_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5));
v___y_274_ = v___x_286_;
goto v___jp_273_;
}
v___jp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_inc_ref(v___y_274_);
v___x_275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_275_, 0, v___y_274_);
v___x_276_ = l_Lean_MessageData_ofFormat(v___x_275_);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_272_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3, &l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = lean_array_to_list(v_paramsInfo_268_);
v___x_281_ = lean_box(0);
v___x_282_ = l_List_mapTR_loop___redArg(v___f_265_, v___x_280_, v___x_281_);
v___x_283_ = l_Lean_MessageData_ofList(v___x_282_);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_279_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
return v___x_284_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSpecState(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
lean_object* v_ks_299_; lean_object* v_vs_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_324_; 
v_ks_299_ = lean_ctor_get(v_x_295_, 0);
v_vs_300_ = lean_ctor_get(v_x_295_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_295_);
if (v_isSharedCheck_324_ == 0)
{
v___x_302_ = v_x_295_;
v_isShared_303_ = v_isSharedCheck_324_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_vs_300_);
lean_inc(v_ks_299_);
lean_dec(v_x_295_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_324_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_array_get_size(v_ks_299_);
v___x_305_ = lean_nat_dec_lt(v_x_296_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec(v_x_296_);
v___x_306_ = lean_array_push(v_ks_299_, v_x_297_);
v___x_307_ = lean_array_push(v_vs_300_, v_x_298_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_307_);
lean_ctor_set(v___x_302_, 0, v___x_306_);
v___x_309_ = v___x_302_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
lean_object* v_k_x27_311_; uint8_t v___x_312_; 
v_k_x27_311_ = lean_array_fget_borrowed(v_ks_299_, v_x_296_);
v___x_312_ = lean_name_eq(v_x_297_, v_k_x27_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_314_; 
if (v_isShared_303_ == 0)
{
v___x_314_ = v___x_302_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_ks_299_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_vs_300_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_x_296_, v___x_315_);
lean_dec(v_x_296_);
v_x_295_ = v___x_314_;
v_x_296_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_319_ = lean_array_fset(v_ks_299_, v_x_296_, v_x_297_);
v___x_320_ = lean_array_fset(v_vs_300_, v_x_296_, v_x_298_);
lean_dec(v_x_296_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_320_);
lean_ctor_set(v___x_302_, 0, v___x_319_);
v___x_322_ = v___x_302_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_320_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_n_325_, lean_object* v_k_326_, lean_object* v_v_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_325_, v___x_328_, v_k_326_, v_v_327_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_330_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(lean_object* v_x_331_, size_t v_x_332_, size_t v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_331_) == 0)
{
lean_object* v_es_336_; size_t v___x_337_; size_t v___x_338_; lean_object* v_j_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_es_336_ = lean_ctor_get(v_x_331_, 0);
v___x_337_ = ((size_t)31ULL);
v___x_338_ = lean_usize_land(v_x_332_, v___x_337_);
v_j_339_ = lean_usize_to_nat(v___x_338_);
v___x_340_ = lean_array_get_size(v_es_336_);
v___x_341_ = lean_nat_dec_lt(v_j_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec(v_j_339_);
lean_dec(v_x_335_);
lean_dec(v_x_334_);
return v_x_331_;
}
else
{
lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_380_; 
lean_inc_ref(v_es_336_);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_331_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_x_331_, 0);
lean_dec(v_unused_381_);
v___x_343_ = v_x_331_;
v_isShared_344_ = v_isSharedCheck_380_;
goto v_resetjp_342_;
}
else
{
lean_dec(v_x_331_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_380_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_v_345_; lean_object* v___x_346_; lean_object* v_xs_x27_347_; lean_object* v___y_349_; 
v_v_345_ = lean_array_fget(v_es_336_, v_j_339_);
v___x_346_ = lean_box(0);
v_xs_x27_347_ = lean_array_fset(v_es_336_, v_j_339_, v___x_346_);
switch(lean_obj_tag(v_v_345_))
{
case 0:
{
lean_object* v_key_354_; lean_object* v_val_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_365_; 
v_key_354_ = lean_ctor_get(v_v_345_, 0);
v_val_355_ = lean_ctor_get(v_v_345_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_v_345_);
if (v_isSharedCheck_365_ == 0)
{
v___x_357_ = v_v_345_;
v_isShared_358_ = v_isSharedCheck_365_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_val_355_);
lean_inc(v_key_354_);
lean_dec(v_v_345_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_365_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
uint8_t v___x_359_; 
v___x_359_ = lean_name_eq(v_x_334_, v_key_354_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_del_object(v___x_357_);
v___x_360_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_354_, v_val_355_, v_x_334_, v_x_335_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
v___y_349_ = v___x_361_;
goto v___jp_348_;
}
else
{
lean_object* v___x_363_; 
lean_dec(v_val_355_);
lean_dec(v_key_354_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v_x_335_);
lean_ctor_set(v___x_357_, 0, v_x_334_);
v___x_363_ = v___x_357_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_x_334_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_x_335_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
v___y_349_ = v___x_363_;
goto v___jp_348_;
}
}
}
}
case 1:
{
lean_object* v_node_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_378_; 
v_node_366_ = lean_ctor_get(v_v_345_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v_v_345_);
if (v_isSharedCheck_378_ == 0)
{
v___x_368_ = v_v_345_;
v_isShared_369_ = v_isSharedCheck_378_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_node_366_);
lean_dec(v_v_345_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_378_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_370_ = ((size_t)5ULL);
v___x_371_ = lean_usize_shift_right(v_x_332_, v___x_370_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_add(v_x_333_, v___x_372_);
v___x_374_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_node_366_, v___x_371_, v___x_373_, v_x_334_, v_x_335_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_374_);
v___x_376_ = v___x_368_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v___y_349_ = v___x_376_;
goto v___jp_348_;
}
}
}
default: 
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_x_334_);
lean_ctor_set(v___x_379_, 1, v_x_335_);
v___y_349_ = v___x_379_;
goto v___jp_348_;
}
}
v___jp_348_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_array_fset(v_xs_x27_347_, v_j_339_, v___y_349_);
lean_dec(v_j_339_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_350_);
v___x_352_ = v___x_343_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_ks_382_; lean_object* v_vs_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_401_; 
v_ks_382_ = lean_ctor_get(v_x_331_, 0);
v_vs_383_ = lean_ctor_get(v_x_331_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_331_);
if (v_isSharedCheck_401_ == 0)
{
v___x_385_ = v_x_331_;
v_isShared_386_ = v_isSharedCheck_401_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_vs_383_);
lean_inc(v_ks_382_);
lean_dec(v_x_331_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_401_;
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
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_ks_382_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_vs_383_);
v___x_388_ = v_reuseFailAlloc_400_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v_newNode_389_; size_t v___x_390_; uint8_t v___x_391_; 
v_newNode_389_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v___x_388_, v_x_334_, v_x_335_);
v___x_390_ = ((size_t)7ULL);
v___x_391_ = lean_usize_dec_le(v___x_390_, v_x_333_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_392_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_389_);
v___x_393_ = lean_unsigned_to_nat(4u);
v___x_394_ = lean_nat_dec_lt(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
if (v___x_394_ == 0)
{
lean_object* v_ks_395_; lean_object* v_vs_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_ks_395_ = lean_ctor_get(v_newNode_389_, 0);
lean_inc_ref(v_ks_395_);
v_vs_396_ = lean_ctor_get(v_newNode_389_, 1);
lean_inc_ref(v_vs_396_);
lean_dec_ref(v_newNode_389_);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0);
v___x_399_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_x_333_, v_ks_395_, v_vs_396_, v___x_397_, v___x_398_);
lean_dec_ref(v_vs_396_);
lean_dec_ref(v_ks_395_);
return v___x_399_;
}
else
{
return v_newNode_389_;
}
}
else
{
return v_newNode_389_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_331_ = stack[0].m_obj;
size_t v_x_332_ = stack[1].m_num;
size_t v_x_333_ = stack[2].m_num;
lean_object* v_x_334_ = stack[3].m_obj;
lean_object* v_x_335_ = stack[4].m_obj;
lean_object* v_res_402_;
v_res_402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_331_, v_x_332_, v_x_333_, v_x_334_, v_x_335_);
stack->m_obj
 = v_res_402_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(size_t v_depth_403_, lean_object* v_keys_404_, lean_object* v_vals_405_, lean_object* v_i_406_, lean_object* v_entries_407_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_array_get_size(v_keys_404_);
v___x_409_ = lean_nat_dec_lt(v_i_406_, v___x_408_);
if (v___x_409_ == 0)
{
lean_dec(v_i_406_);
return v_entries_407_;
}
else
{
lean_object* v_k_410_; lean_object* v_v_411_; uint64_t v___y_413_; 
v_k_410_ = lean_array_fget_borrowed(v_keys_404_, v_i_406_);
v_v_411_ = lean_array_fget_borrowed(v_vals_405_, v_i_406_);
if (lean_obj_tag(v_k_410_) == 0)
{
uint64_t v___x_424_; 
v___x_424_ = 1723ULL;
v___y_413_ = v___x_424_;
goto v___jp_412_;
}
else
{
uint64_t v_hash_425_; 
v_hash_425_ = lean_ctor_get_uint64(v_k_410_, sizeof(void*)*2);
v___y_413_ = v_hash_425_;
goto v___jp_412_;
}
v___jp_412_:
{
size_t v_h_414_; size_t v___x_415_; lean_object* v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v_h_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_h_414_ = lean_uint64_to_usize(v___y_413_);
v___x_415_ = ((size_t)5ULL);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_sub(v_depth_403_, v___x_417_);
v___x_419_ = lean_usize_mul(v___x_415_, v___x_418_);
v_h_420_ = lean_usize_shift_right(v_h_414_, v___x_419_);
v___x_421_ = lean_nat_add(v_i_406_, v___x_416_);
lean_dec(v_i_406_);
lean_inc(v_v_411_);
lean_inc(v_k_410_);
v___x_422_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_entries_407_, v_h_420_, v_depth_403_, v_k_410_, v_v_411_);
v_i_406_ = v___x_421_;
v_entries_407_ = v___x_422_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_403_ = stack[0].m_num;
lean_object* v_keys_404_ = stack[1].m_obj;
lean_object* v_vals_405_ = stack[2].m_obj;
lean_object* v_i_406_ = stack[3].m_obj;
lean_object* v_entries_407_ = stack[4].m_obj;
lean_object* v_res_426_;
v_res_426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_403_, v_keys_404_, v_vals_405_, v_i_406_, v_entries_407_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_427_, lean_object* v_keys_428_, lean_object* v_vals_429_, lean_object* v_i_430_, lean_object* v_entries_431_){
_start:
{
size_t v_depth_boxed_432_; lean_object* v_res_433_; 
v_depth_boxed_432_ = lean_unbox_usize(v_depth_427_);
lean_dec(v_depth_427_);
v_res_433_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_boxed_432_, v_keys_428_, v_vals_429_, v_i_430_, v_entries_431_);
lean_dec_ref(v_vals_429_);
lean_dec_ref(v_keys_428_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
size_t v_x_397__boxed_439_; size_t v_x_398__boxed_440_; lean_object* v_res_441_; 
v_x_397__boxed_439_ = lean_unbox_usize(v_x_435_);
lean_dec(v_x_435_);
v_x_398__boxed_440_ = lean_unbox_usize(v_x_436_);
lean_dec(v_x_436_);
v_res_441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_434_, v_x_397__boxed_439_, v_x_398__boxed_440_, v_x_437_, v_x_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
uint64_t v___y_446_; 
if (lean_obj_tag(v_x_443_) == 0)
{
uint64_t v___x_450_; 
v___x_450_ = 1723ULL;
v___y_446_ = v___x_450_;
goto v___jp_445_;
}
else
{
uint64_t v_hash_451_; 
v_hash_451_ = lean_ctor_get_uint64(v_x_443_, sizeof(void*)*2);
v___y_446_ = v_hash_451_;
goto v___jp_445_;
}
v___jp_445_:
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_uint64_to_usize(v___y_446_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_442_, v___x_447_, v___x_448_, v_x_443_, v_x_444_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecState_addEntry(lean_object* v_s_452_, lean_object* v_e_453_){
_start:
{
lean_object* v_declName_454_; lean_object* v___x_455_; 
v_declName_454_ = lean_ctor_get(v_e_453_, 0);
lean_inc(v_declName_454_);
v___x_455_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_s_452_, v_declName_454_, v_e_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_x_457_, v_x_458_, v_x_459_);
return v___x_460_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(lean_object* v_00_u03b2_461_, lean_object* v_x_462_, size_t v_x_463_, size_t v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_462_, v_x_463_, v_x_464_, v_x_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_462_ = stack[1].m_obj;
size_t v_x_463_ = stack[2].m_num;
size_t v_x_464_ = stack[3].m_num;
lean_object* v_x_465_ = stack[4].m_obj;
lean_object* v_x_466_ = stack[5].m_obj;
lean_object* v_res_468_;
v_res_468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(lean_box(0), v_x_462_, v_x_463_, v_x_464_, v_x_465_, v_x_466_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
size_t v_x_679__boxed_475_; size_t v_x_680__boxed_476_; lean_object* v_res_477_; 
v_x_679__boxed_475_ = lean_unbox_usize(v_x_471_);
lean_dec(v_x_471_);
v_x_680__boxed_476_ = lean_unbox_usize(v_x_472_);
lean_dec(v_x_472_);
v_res_477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(v_00_u03b2_469_, v_x_470_, v_x_679__boxed_475_, v_x_680__boxed_476_, v_x_473_, v_x_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_478_, lean_object* v_n_479_, lean_object* v_k_480_, lean_object* v_v_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v_n_479_, v_k_480_, v_v_481_);
return v___x_482_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_483_, size_t v_depth_484_, lean_object* v_keys_485_, lean_object* v_vals_486_, lean_object* v_heq_487_, lean_object* v_i_488_, lean_object* v_entries_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_484_, v_keys_485_, v_vals_486_, v_i_488_, v_entries_489_);
return v___x_490_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_484_ = stack[1].m_num;
lean_object* v_keys_485_ = stack[2].m_obj;
lean_object* v_vals_486_ = stack[3].m_obj;
lean_object* v_i_488_ = stack[5].m_obj;
lean_object* v_entries_489_ = stack[6].m_obj;
lean_object* v_res_491_;
v_res_491_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(lean_box(0), v_depth_484_, v_keys_485_, v_vals_486_, lean_box(0), v_i_488_, v_entries_489_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_492_, lean_object* v_depth_493_, lean_object* v_keys_494_, lean_object* v_vals_495_, lean_object* v_heq_496_, lean_object* v_i_497_, lean_object* v_entries_498_){
_start:
{
size_t v_depth_boxed_499_; lean_object* v_res_500_; 
v_depth_boxed_499_ = lean_unbox_usize(v_depth_493_);
lean_dec(v_depth_493_);
v_res_500_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(v_00_u03b2_492_, v_depth_boxed_499_, v_keys_494_, v_vals_495_, v_heq_496_, v_i_497_, v_entries_498_);
lean_dec_ref(v_vals_495_);
lean_dec_ref(v_keys_494_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_501_, lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_x_502_, v_x_503_, v_x_504_, v_x_505_);
return v___x_506_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(lean_object* v_a_507_, lean_object* v_b_508_){
_start:
{
lean_object* v_declName_509_; lean_object* v_declName_510_; uint8_t v___x_511_; 
v_declName_509_ = lean_ctor_get(v_a_507_, 0);
v_declName_510_ = lean_ctor_get(v_b_508_, 0);
v___x_511_ = l_Lean_Name_quickLt(v_declName_509_, v_declName_510_);
return v___x_511_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_507_ = stack[0].m_obj;
lean_object* v_b_508_ = stack[1].m_obj;
uint8_t v_res_512_;
v_res_512_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(v_a_507_, v_b_508_);
stack->m_num = v_res_512_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed(lean_object* v_a_513_, lean_object* v_b_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(v_a_513_, v_b_514_);
lean_dec_ref(v_b_514_);
lean_dec_ref(v_a_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries(lean_object* v_entries_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_array_get_size(v_entries_518_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___y_526_; uint8_t v___x_530_; 
v___x_522_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0));
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_sub(v___x_519_, v___x_523_);
v___x_530_ = lean_nat_dec_le(v___x_520_, v___x_524_);
if (v___x_530_ == 0)
{
lean_inc(v___x_524_);
v___y_526_ = v___x_524_;
goto v___jp_525_;
}
else
{
v___y_526_ = v___x_520_;
goto v___jp_525_;
}
v___jp_525_:
{
uint8_t v___x_527_; 
v___x_527_ = lean_nat_dec_le(v___y_526_, v___x_524_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v___x_524_);
lean_inc(v___y_526_);
v___x_528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_522_, v___x_519_, v_entries_518_, v___y_526_, v___y_526_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_526_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_522_, v___x_519_, v_entries_518_, v___y_526_, v___x_524_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_524_);
return v___x_529_;
}
}
}
else
{
return v_entries_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(lean_object* v_entries_534_, lean_object* v_declName_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_array_get_size(v_entries_534_);
v___x_538_ = lean_nat_dec_lt(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_dec(v_declName_535_);
v___x_539_ = lean_box(0);
return v___x_539_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_sub(v___x_537_, v___x_540_);
v___x_542_ = lean_nat_dec_le(v___x_536_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
lean_dec(v___x_541_);
lean_dec(v_declName_535_);
v___x_543_ = lean_box(0);
return v___x_543_;
}
else
{
lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_545_ = 0;
v___x_546_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_546_, 0, v_declName_535_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*2, v___x_545_);
v___x_547_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0));
v___x_548_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1));
v___x_549_ = l_Array_binSearchAux___redArg(v___x_547_, v___x_548_, v_entries_534_, v___x_546_, v___x_536_, v___x_541_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___boxed(lean_object* v_entries_550_, lean_object* v_declName_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(v_entries_550_, v_declName_551_);
lean_dec_ref(v_entries_550_);
return v_res_552_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_declName_555_; lean_object* v_declName_556_; uint8_t v___x_557_; 
v_declName_555_ = lean_ctor_get(v___y_553_, 0);
v_declName_556_ = lean_ctor_get(v___y_554_, 0);
v___x_557_ = l_Lean_Name_quickLt(v_declName_555_, v_declName_556_);
return v___x_557_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_553_ = stack[0].m_obj;
lean_object* v___y_554_ = stack[1].m_obj;
uint8_t v_res_558_;
v_res_558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___y_553_, v___y_554_);
stack->m_num = v_res_558_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0___boxed(lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___y_559_, v___y_560_);
lean_dec_ref(v___y_560_);
lean_dec_ref(v___y_559_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_hi_563_, lean_object* v_pivot_564_, lean_object* v_as_565_, lean_object* v_i_566_, lean_object* v_k_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_nat_dec_lt(v_k_567_, v_hi_563_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_k_567_);
v___x_569_ = lean_array_fswap(v_as_565_, v_i_566_, v_hi_563_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_i_566_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v_declName_572_; lean_object* v_declName_573_; uint8_t v___x_574_; 
v___x_571_ = lean_array_fget_borrowed(v_as_565_, v_k_567_);
v_declName_572_ = lean_ctor_get(v___x_571_, 0);
v_declName_573_ = lean_ctor_get(v_pivot_564_, 0);
v___x_574_ = l_Lean_Name_quickLt(v_declName_572_, v_declName_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_k_567_, v___x_575_);
lean_dec(v_k_567_);
v_k_567_ = v___x_576_;
goto _start;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_array_fswap(v_as_565_, v_i_566_, v_k_567_);
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_i_566_, v___x_579_);
lean_dec(v_i_566_);
v___x_581_ = lean_nat_add(v_k_567_, v___x_579_);
lean_dec(v_k_567_);
v_as_565_ = v___x_578_;
v_i_566_ = v___x_580_;
v_k_567_ = v___x_581_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_hi_583_, lean_object* v_pivot_584_, lean_object* v_as_585_, lean_object* v_i_586_, lean_object* v_k_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_583_, v_pivot_584_, v_as_585_, v_i_586_, v_k_587_);
lean_dec_ref(v_pivot_584_);
lean_dec(v_hi_583_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(lean_object* v_n_589_, lean_object* v_as_590_, lean_object* v_lo_591_, lean_object* v_hi_592_){
_start:
{
lean_object* v___y_594_; uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_lt(v_lo_591_, v_hi_592_);
if (v___x_604_ == 0)
{
lean_dec(v_lo_591_);
return v_as_590_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_mid_607_; lean_object* v___y_609_; lean_object* v___y_615_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_605_ = lean_nat_add(v_lo_591_, v_hi_592_);
v___x_606_ = lean_unsigned_to_nat(1u);
v_mid_607_ = lean_nat_shiftr(v___x_605_, v___x_606_);
lean_dec(v___x_605_);
v___x_620_ = lean_array_fget_borrowed(v_as_590_, v_mid_607_);
v___x_621_ = lean_array_fget_borrowed(v_as_590_, v_lo_591_);
v___x_622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
v___y_615_ = v_as_590_;
goto v___jp_614_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_array_fswap(v_as_590_, v_lo_591_, v_mid_607_);
v___y_615_ = v___x_623_;
goto v___jp_614_;
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_array_fget_borrowed(v___y_609_, v_mid_607_);
v___x_611_ = lean_array_fget_borrowed(v___y_609_, v_hi_592_);
v___x_612_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_dec(v_mid_607_);
v___y_594_ = v___y_609_;
goto v___jp_593_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_array_fswap(v___y_609_, v_mid_607_, v_hi_592_);
lean_dec(v_mid_607_);
v___y_594_ = v___x_613_;
goto v___jp_593_;
}
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = lean_array_fget_borrowed(v___y_615_, v_hi_592_);
v___x_617_ = lean_array_fget_borrowed(v___y_615_, v_lo_591_);
v___x_618_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
v___y_609_ = v___y_615_;
goto v___jp_608_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_array_fswap(v___y_615_, v_lo_591_, v_hi_592_);
v___y_609_ = v___x_619_;
goto v___jp_608_;
}
}
}
v___jp_593_:
{
lean_object* v_pivot_595_; lean_object* v___x_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; uint8_t v___x_599_; 
v_pivot_595_ = lean_array_fget(v___y_594_, v_hi_592_);
lean_inc_n(v_lo_591_, 2);
v___x_596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_592_, v_pivot_595_, v___y_594_, v_lo_591_, v_lo_591_);
lean_dec(v_pivot_595_);
v_fst_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v___x_596_, 1);
lean_inc(v_snd_598_);
lean_dec_ref(v___x_596_);
v___x_599_ = lean_nat_dec_le(v_hi_592_, v_fst_597_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_589_, v_snd_598_, v_lo_591_, v_fst_597_);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_add(v_fst_597_, v___x_601_);
lean_dec(v_fst_597_);
v_as_590_ = v___x_600_;
v_lo_591_ = v___x_602_;
goto _start;
}
else
{
lean_dec(v_fst_597_);
lean_dec(v_lo_591_);
return v_snd_598_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_n_624_, lean_object* v_as_625_, lean_object* v_lo_626_, lean_object* v_hi_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_624_, v_as_625_, v_lo_626_, v_hi_627_);
lean_dec(v_hi_627_);
lean_dec(v_n_624_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_s_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_630_ = lean_array_mk(v_s_629_);
v___x_631_ = lean_array_get_size(v___x_630_);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_nat_dec_eq(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___y_637_; uint8_t v___x_641_; 
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_sub(v___x_631_, v___x_634_);
v___x_641_ = lean_nat_dec_le(v___x_632_, v___x_635_);
if (v___x_641_ == 0)
{
lean_inc(v___x_635_);
v___y_637_ = v___x_635_;
goto v___jp_636_;
}
else
{
v___y_637_ = v___x_632_;
goto v___jp_636_;
}
v___jp_636_:
{
uint8_t v___x_638_; 
v___x_638_ = lean_nat_dec_le(v___y_637_, v___x_635_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec(v___x_635_);
lean_inc(v___y_637_);
v___x_639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_631_, v___x_630_, v___y_637_, v___y_637_);
lean_dec(v___y_637_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_631_, v___x_630_, v___y_637_, v___x_635_);
lean_dec(v___x_635_);
return v___x_640_;
}
}
}
else
{
return v___x_630_;
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_keys_642_, lean_object* v_i_643_, lean_object* v_k_644_){
_start:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_array_get_size(v_keys_642_);
v___x_646_ = lean_nat_dec_lt(v_i_643_, v___x_645_);
if (v___x_646_ == 0)
{
lean_dec(v_i_643_);
return v___x_646_;
}
else
{
lean_object* v_k_x27_647_; uint8_t v___x_648_; 
v_k_x27_647_ = lean_array_fget_borrowed(v_keys_642_, v_i_643_);
v___x_648_ = lean_name_eq(v_k_644_, v_k_x27_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_i_643_, v___x_649_);
lean_dec(v_i_643_);
v_i_643_ = v___x_650_;
goto _start;
}
else
{
lean_dec(v_i_643_);
return v___x_646_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_642_ = stack[0].m_obj;
lean_object* v_i_643_ = stack[1].m_obj;
lean_object* v_k_644_ = stack[2].m_obj;
uint8_t v_res_652_;
v_res_652_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_642_, v_i_643_, v_k_644_);
stack->m_num = v_res_652_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_653_, lean_object* v_i_654_, lean_object* v_k_655_){
_start:
{
uint8_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_653_, v_i_654_, v_k_655_);
lean_dec(v_k_655_);
lean_dec_ref(v_keys_653_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_658_, size_t v_x_659_, lean_object* v_x_660_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v_es_661_; lean_object* v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v_j_665_; lean_object* v___x_666_; 
v_es_661_ = lean_ctor_get(v_x_658_, 0);
v___x_662_ = lean_box(2);
v___x_663_ = ((size_t)31ULL);
v___x_664_ = lean_usize_land(v_x_659_, v___x_663_);
v_j_665_ = lean_usize_to_nat(v___x_664_);
v___x_666_ = lean_array_get_borrowed(v___x_662_, v_es_661_, v_j_665_);
lean_dec(v_j_665_);
switch(lean_obj_tag(v___x_666_))
{
case 0:
{
lean_object* v_key_667_; uint8_t v___x_668_; 
v_key_667_ = lean_ctor_get(v___x_666_, 0);
v___x_668_ = lean_name_eq(v_x_660_, v_key_667_);
return v___x_668_;
}
case 1:
{
lean_object* v_node_669_; size_t v___x_670_; size_t v___x_671_; 
v_node_669_ = lean_ctor_get(v___x_666_, 0);
v___x_670_ = ((size_t)5ULL);
v___x_671_ = lean_usize_shift_right(v_x_659_, v___x_670_);
v_x_658_ = v_node_669_;
v_x_659_ = v___x_671_;
goto _start;
}
default: 
{
uint8_t v___x_673_; 
v___x_673_ = 0;
return v___x_673_;
}
}
}
else
{
lean_object* v_ks_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_ks_674_ = lean_ctor_get(v_x_658_, 0);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_ks_674_, v___x_675_, v_x_660_);
return v___x_676_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_658_ = stack[0].m_obj;
size_t v_x_659_ = stack[1].m_num;
lean_object* v_x_660_ = stack[2].m_obj;
uint8_t v_res_677_;
v_res_677_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_658_, v_x_659_, v_x_660_);
stack->m_num = v_res_677_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
size_t v_x_544__boxed_681_; uint8_t v_res_682_; lean_object* v_r_683_; 
v_x_544__boxed_681_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_res_682_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_678_, v_x_544__boxed_681_, v_x_680_);
lean_dec(v_x_680_);
lean_dec_ref(v_x_678_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
uint64_t v___y_687_; 
if (lean_obj_tag(v_x_685_) == 0)
{
uint64_t v___x_690_; 
v___x_690_ = 1723ULL;
v___y_687_ = v___x_690_;
goto v___jp_686_;
}
else
{
uint64_t v_hash_691_; 
v_hash_691_ = lean_ctor_get_uint64(v_x_685_, sizeof(void*)*2);
v___y_687_ = v_hash_691_;
goto v___jp_686_;
}
v___jp_686_:
{
size_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_uint64_to_usize(v___y_687_);
v___x_689_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_684_, v___x_688_, v_x_685_);
return v___x_689_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_684_ = stack[0].m_obj;
lean_object* v_x_685_ = stack[1].m_obj;
uint8_t v_res_692_;
v_res_692_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_684_, v_x_685_);
stack->m_num = v_res_692_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_693_, v_x_694_);
lean_dec(v_x_694_);
lean_dec_ref(v_x_693_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_x1_697_, lean_object* v_x2_698_){
_start:
{
lean_object* v_declName_699_; uint8_t v___x_700_; 
v_declName_699_ = lean_ctor_get(v_x2_698_, 0);
v___x_700_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x1_697_, v_declName_699_);
if (v___x_700_ == 0)
{
uint8_t v___x_701_; 
v___x_701_ = 1;
return v___x_701_;
}
else
{
uint8_t v___x_702_; 
v___x_702_ = 0;
return v___x_702_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_697_ = stack[0].m_obj;
lean_object* v_x2_698_ = stack[1].m_obj;
uint8_t v_res_703_;
v_res_703_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x1_697_, v_x2_698_);
stack->m_num = v_res_703_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_x1_704_, lean_object* v_x2_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x1_704_, v_x2_705_);
lean_dec_ref(v_x2_705_);
lean_dec_ref(v_x1_704_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_x_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x_710_);
lean_dec_ref(v_x_710_);
return v_res_711_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_));
v___x_741_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_742_;
v_res_742_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
stack->m_obj
 = v_res_742_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(lean_object* v_n_745_, lean_object* v_as_746_, lean_object* v_lo_747_, lean_object* v_hi_748_, lean_object* v_w_749_, lean_object* v_hlo_750_, lean_object* v_hhi_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_745_, v_as_746_, v_lo_747_, v_hi_748_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___boxed(lean_object* v_n_753_, lean_object* v_as_754_, lean_object* v_lo_755_, lean_object* v_hi_756_, lean_object* v_w_757_, lean_object* v_hlo_758_, lean_object* v_hhi_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(v_n_753_, v_as_754_, v_lo_755_, v_hi_756_, v_w_757_, v_hlo_758_, v_hhi_759_);
lean_dec(v_hi_756_);
lean_dec(v_n_753_);
return v_res_760_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_762_ = stack[1].m_obj;
lean_object* v_x_763_ = stack[2].m_obj;
uint8_t v_res_765_;
v_res_765_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(lean_box(0), v_x_762_, v_x_763_);
stack->m_num = v_res_765_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(v_00_u03b2_766_, v_x_767_, v_x_768_);
lean_dec(v_x_768_);
lean_dec_ref(v_x_767_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_n_771_, lean_object* v_lo_772_, lean_object* v_hi_773_, lean_object* v_hhi_774_, lean_object* v_pivot_775_, lean_object* v_as_776_, lean_object* v_i_777_, lean_object* v_k_778_, lean_object* v_ilo_779_, lean_object* v_ik_780_, lean_object* v_w_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_773_, v_pivot_775_, v_as_776_, v_i_777_, v_k_778_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_n_783_, lean_object* v_lo_784_, lean_object* v_hi_785_, lean_object* v_hhi_786_, lean_object* v_pivot_787_, lean_object* v_as_788_, lean_object* v_i_789_, lean_object* v_k_790_, lean_object* v_ilo_791_, lean_object* v_ik_792_, lean_object* v_w_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(v_n_783_, v_lo_784_, v_hi_785_, v_hhi_786_, v_pivot_787_, v_as_788_, v_i_789_, v_k_790_, v_ilo_791_, v_ik_792_, v_w_793_);
lean_dec_ref(v_pivot_787_);
lean_dec(v_hi_785_);
lean_dec(v_lo_784_);
lean_dec(v_n_783_);
return v_res_794_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, size_t v_x_797_, lean_object* v_x_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_796_ = stack[1].m_obj;
size_t v_x_797_ = stack[2].m_num;
lean_object* v_x_798_ = stack[3].m_obj;
uint8_t v_res_800_;
v_res_800_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(lean_box(0), v_x_796_, v_x_797_, v_x_798_);
stack->m_num = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
size_t v_x_800__boxed_805_; uint8_t v_res_806_; lean_object* v_r_807_; 
v_x_800__boxed_805_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_res_806_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_801_, v_x_802_, v_x_800__boxed_805_, v_x_804_);
lean_dec(v_x_804_);
lean_dec_ref(v_x_802_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03b2_808_, lean_object* v_keys_809_, lean_object* v_vals_810_, lean_object* v_heq_811_, lean_object* v_i_812_, lean_object* v_k_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_809_, v_i_812_, v_k_813_);
return v___x_814_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_809_ = stack[1].m_obj;
lean_object* v_vals_810_ = stack[2].m_obj;
lean_object* v_i_812_ = stack[4].m_obj;
lean_object* v_k_813_ = stack[5].m_obj;
uint8_t v_res_815_;
v_res_815_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_box(0), v_keys_809_, v_vals_810_, lean_box(0), v_i_812_, v_k_813_);
stack->m_num = v_res_815_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_816_, lean_object* v_keys_817_, lean_object* v_vals_818_, lean_object* v_heq_819_, lean_object* v_i_820_, lean_object* v_k_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03b2_816_, v_keys_817_, v_vals_818_, v_heq_819_, v_i_820_, v_k_821_);
lean_dec(v_k_821_);
lean_dec_ref(v_vals_818_);
lean_dec_ref(v_keys_817_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(lean_object* v_env_824_, lean_object* v_type_825_){
_start:
{
if (lean_obj_tag(v_type_825_) == 7)
{
lean_object* v_body_826_; 
v_body_826_ = lean_ctor_get(v_type_825_, 2);
v_type_825_ = v_body_826_;
goto _start;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Expr_getAppFn(v_type_825_);
if (lean_obj_tag(v___x_828_) == 4)
{
lean_object* v_declName_829_; uint8_t v___x_830_; 
v_declName_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_declName_829_);
lean_dec_ref_known(v___x_828_, 2);
v___x_830_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_824_, v_declName_829_);
return v___x_830_;
}
else
{
uint8_t v___x_831_; 
lean_dec_ref(v___x_828_);
lean_dec_ref(v_env_824_);
v___x_831_ = 0;
return v___x_831_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_824_ = stack[0].m_obj;
lean_object* v_type_825_ = stack[1].m_obj;
uint8_t v_res_832_;
v_res_832_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_824_, v_type_825_);
stack->m_num = v_res_832_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType___boxed(lean_object* v_env_833_, lean_object* v_type_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_833_, v_type_834_);
lean_dec_ref(v_type_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(lean_object* v_env_837_, lean_object* v_type_838_){
_start:
{
if (lean_obj_tag(v_type_838_) == 7)
{
lean_object* v_body_839_; 
v_body_839_ = lean_ctor_get(v_type_838_, 2);
v_type_838_ = v_body_839_;
goto _start;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Expr_getAppFn(v_type_838_);
if (lean_obj_tag(v___x_841_) == 4)
{
lean_object* v_declName_842_; uint8_t v___x_843_; 
v_declName_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_declName_842_);
lean_dec_ref_known(v___x_841_, 2);
v___x_843_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_837_, v_declName_842_);
return v___x_843_;
}
else
{
uint8_t v___x_844_; 
lean_dec_ref(v___x_841_);
lean_dec_ref(v_env_837_);
v___x_844_ = 0;
return v___x_844_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_837_ = stack[0].m_obj;
lean_object* v_type_838_ = stack[1].m_obj;
uint8_t v_res_845_;
v_res_845_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_837_, v_type_838_);
stack->m_num = v_res_845_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType___boxed(lean_object* v_env_846_, lean_object* v_type_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_846_, v_type_847_);
lean_dec_ref(v_type_847_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(lean_object* v_upperBound_853_, lean_object* v___x_854_, lean_object* v_param_855_, lean_object* v_paramsInfo_856_, lean_object* v_a_857_, lean_object* v_b_858_){
_start:
{
lean_object* v_a_860_; uint8_t v___x_864_; 
v___x_864_ = lean_nat_dec_lt(v_a_857_, v_upperBound_853_);
if (v___x_864_ == 0)
{
lean_dec(v_a_857_);
lean_inc_ref(v_b_858_);
return v_b_858_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_875_; lean_object* v___x_878_; 
v___x_865_ = lean_box(0);
v___x_866_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0));
v___x_875_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default));
v___x_878_ = lean_array_get_borrowed(v___x_875_, v_paramsInfo_856_, v_a_857_);
switch(lean_obj_tag(v___x_878_))
{
case 0:
{
uint8_t v_weak_879_; 
v_weak_879_ = lean_ctor_get_uint8(v___x_878_, 0);
if (v_weak_879_ == 0)
{
goto v___jp_867_;
}
else
{
goto v___jp_876_;
}
}
case 2:
{
goto v___jp_876_;
}
case 4:
{
goto v___jp_876_;
}
default: 
{
goto v___jp_867_;
}
}
v___jp_867_:
{
lean_object* v___x_868_; lean_object* v_type_869_; lean_object* v_fvarId_870_; uint8_t v___x_871_; 
v___x_868_ = lean_array_fget_borrowed(v___x_854_, v_a_857_);
v_type_869_ = lean_ctor_get(v___x_868_, 2);
v_fvarId_870_ = lean_ctor_get(v_param_855_, 0);
v___x_871_ = l_Lean_Expr_containsFVar(v_type_869_, v_fvarId_870_);
if (v___x_871_ == 0)
{
v_a_860_ = v___x_866_;
goto v___jp_859_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec(v_a_857_);
v___x_872_ = lean_box(v___x_864_);
v___x_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_865_);
return v___x_874_;
}
}
v___jp_876_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_array_get_borrowed(v___x_875_, v_paramsInfo_856_, v_a_857_);
if (lean_obj_tag(v___x_877_) == 0)
{
goto v___jp_867_;
}
else
{
v_a_860_ = v___x_866_;
goto v___jp_859_;
}
}
}
v___jp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_add(v_a_857_, v___x_861_);
lean_dec(v_a_857_);
v_a_857_ = v___x_862_;
v_b_858_ = v_a_860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___boxed(lean_object* v_upperBound_880_, lean_object* v___x_881_, lean_object* v_param_882_, lean_object* v_paramsInfo_883_, lean_object* v_a_884_, lean_object* v_b_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v_upperBound_880_, v___x_881_, v_param_882_, v_paramsInfo_883_, v_a_884_, v_b_885_);
lean_dec_ref(v_b_885_);
lean_dec_ref(v_paramsInfo_883_);
lean_dec_ref(v_param_882_);
lean_dec_ref(v___x_881_);
lean_dec(v_upperBound_880_);
return v_res_886_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_887_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(lean_object* v_decl_888_, lean_object* v_paramsInfo_889_, lean_object* v_j_890_){
_start:
{
lean_object* v_toSignature_891_; lean_object* v_params_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_param_898_; lean_object* v___x_899_; lean_object* v_fst_900_; 
v_toSignature_891_ = lean_ctor_get(v_decl_888_, 0);
v_params_892_ = lean_ctor_get(v_toSignature_891_, 3);
v___x_893_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0, &l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_nat_add(v_j_890_, v___x_894_);
v___x_896_ = lean_array_get_size(v_params_892_);
v___x_897_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0));
v_param_898_ = lean_array_get_borrowed(v___x_893_, v_params_892_, v_j_890_);
v___x_899_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_896_, v_params_892_, v_param_898_, v_paramsInfo_889_, v___x_895_, v___x_897_);
v_fst_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_fst_900_);
lean_dec_ref(v___x_899_);
if (lean_obj_tag(v_fst_900_) == 0)
{
uint8_t v___x_901_; 
v___x_901_ = 0;
return v___x_901_;
}
else
{
lean_object* v_val_902_; uint8_t v___x_903_; 
v_val_902_ = lean_ctor_get(v_fst_900_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v_fst_900_, 1);
v___x_903_ = lean_unbox(v_val_902_);
lean_dec(v_val_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_888_ = stack[0].m_obj;
lean_object* v_paramsInfo_889_ = stack[1].m_obj;
lean_object* v_j_890_ = stack[2].m_obj;
uint8_t v_res_904_;
v_res_904_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v_decl_888_, v_paramsInfo_889_, v_j_890_);
stack->m_num = v_res_904_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___boxed(lean_object* v_decl_905_, lean_object* v_paramsInfo_906_, lean_object* v_j_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v_decl_905_, v_paramsInfo_906_, v_j_907_);
lean_dec(v_j_907_);
lean_dec_ref(v_paramsInfo_906_);
lean_dec_ref(v_decl_905_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(lean_object* v_upperBound_910_, lean_object* v___x_911_, lean_object* v_param_912_, lean_object* v_paramsInfo_913_, lean_object* v_inst_914_, lean_object* v_R_915_, lean_object* v_a_916_, lean_object* v_b_917_, lean_object* v_c_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v_upperBound_910_, v___x_911_, v_param_912_, v_paramsInfo_913_, v_a_916_, v_b_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___boxed(lean_object* v_upperBound_920_, lean_object* v___x_921_, lean_object* v_param_922_, lean_object* v_paramsInfo_923_, lean_object* v_inst_924_, lean_object* v_R_925_, lean_object* v_a_926_, lean_object* v_b_927_, lean_object* v_c_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(v_upperBound_920_, v___x_921_, v_param_922_, v_paramsInfo_923_, v_inst_924_, v_R_925_, v_a_926_, v_b_927_, v_c_928_);
lean_dec_ref(v_b_927_);
lean_dec_ref(v_paramsInfo_923_);
lean_dec_ref(v_param_922_);
lean_dec_ref(v___x_921_);
lean_dec(v_upperBound_920_);
return v_res_929_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0(void){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_instMonadEIO___redArg();
return v___x_930_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(lean_object* v_msg_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_toApplicative_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_974_; 
v___x_939_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0, &l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0);
v___x_940_ = l_StateRefT_x27_instMonad___redArg(v___x_939_);
v_toApplicative_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v___x_940_, 1);
lean_dec(v_unused_975_);
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_974_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_toApplicative_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_974_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_toFunctor_945_; lean_object* v_toSeq_946_; lean_object* v_toSeqLeft_947_; lean_object* v_toSeqRight_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_972_; 
v_toFunctor_945_ = lean_ctor_get(v_toApplicative_941_, 0);
v_toSeq_946_ = lean_ctor_get(v_toApplicative_941_, 2);
v_toSeqLeft_947_ = lean_ctor_get(v_toApplicative_941_, 3);
v_toSeqRight_948_ = lean_ctor_get(v_toApplicative_941_, 4);
v_isSharedCheck_972_ = !lean_is_exclusive(v_toApplicative_941_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_toApplicative_941_, 1);
lean_dec(v_unused_973_);
v___x_950_ = v_toApplicative_941_;
v_isShared_951_ = v_isSharedCheck_972_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_toSeqRight_948_);
lean_inc(v_toSeqLeft_947_);
lean_inc(v_toSeq_946_);
lean_inc(v_toFunctor_945_);
lean_dec(v_toApplicative_941_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_972_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___f_952_; lean_object* v___f_953_; lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___f_959_; lean_object* v___x_961_; 
v___f_952_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1));
v___f_953_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2));
lean_inc_ref(v_toFunctor_945_);
v___f_954_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_954_, 0, v_toFunctor_945_);
v___f_955_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_955_, 0, v_toFunctor_945_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___f_954_);
lean_ctor_set(v___x_956_, 1, v___f_955_);
v___f_957_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_957_, 0, v_toSeqRight_948_);
v___f_958_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_958_, 0, v_toSeqLeft_947_);
v___f_959_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_959_, 0, v_toSeq_946_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v___f_957_);
lean_ctor_set(v___x_950_, 3, v___f_958_);
lean_ctor_set(v___x_950_, 2, v___f_959_);
lean_ctor_set(v___x_950_, 1, v___f_952_);
lean_ctor_set(v___x_950_, 0, v___x_956_);
v___x_961_ = v___x_950_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___f_952_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v___f_959_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v___f_958_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v___f_957_);
v___x_961_ = v_reuseFailAlloc_971_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___f_953_);
lean_ctor_set(v___x_943_, 0, v___x_961_);
v___x_963_ = v___x_943_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___f_953_);
v___x_963_ = v_reuseFailAlloc_970_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___f_967_; lean_object* v___x_9164__overap_968_; lean_object* v___x_969_; 
v___x_964_ = l_StateRefT_x27_instMonad___redArg(v___x_963_);
v___x_965_ = lean_box(0);
v___x_966_ = l_instInhabitedOfMonad___redArg(v___x_964_, v___x_965_);
v___f_967_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_967_, 0, v___x_966_);
v___x_9164__overap_968_ = lean_panic_fn_borrowed(v___f_967_, v_msg_933_);
lean_dec_ref(v___f_967_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
v___x_969_ = lean_apply_5(v___x_9164__overap_968_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, lean_box(0));
return v___x_969_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_933_ = stack[0].m_obj;
lean_object* v___y_934_ = stack[1].m_obj;
lean_object* v___y_935_ = stack[2].m_obj;
lean_object* v___y_936_ = stack[3].m_obj;
lean_object* v___y_937_ = stack[4].m_obj;
lean_object* v_res_976_;
v_res_976_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v_msg_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___boxed(lean_object* v_msg_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v_msg_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_983_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(lean_object* v_alreadySpecialized_984_, size_t v_sz_985_, size_t v_i_986_, lean_object* v_bs_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_lt(v_i_986_, v_sz_985_);
if (v___x_988_ == 0)
{
return v_bs_987_;
}
else
{
lean_object* v_v_989_; lean_object* v_toSignature_990_; lean_object* v_name_991_; lean_object* v_params_992_; lean_object* v___x_993_; lean_object* v_bs_x27_994_; uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v_v_989_ = lean_array_uget_borrowed(v_bs_987_, v_i_986_);
v_toSignature_990_ = lean_ctor_get(v_v_989_, 0);
v_name_991_ = lean_ctor_get(v_toSignature_990_, 0);
lean_inc(v_name_991_);
v_params_992_ = lean_ctor_get(v_toSignature_990_, 3);
lean_inc_ref(v_params_992_);
v___x_993_ = lean_unsigned_to_nat(0u);
v_bs_x27_994_ = lean_array_uset(v_bs_987_, v_i_986_, v___x_993_);
v___x_995_ = 0;
v___x_996_ = lean_usize_to_nat(v_i_986_);
v___x_997_ = lean_array_get_size(v_params_992_);
lean_dec_ref(v_params_992_);
v___x_998_ = lean_box(4);
v___x_999_ = lean_mk_array(v___x_997_, v___x_998_);
v___x_1000_ = lean_box(v___x_995_);
v___x_1001_ = lean_array_get(v___x_1000_, v_alreadySpecialized_984_, v___x_996_);
lean_dec(v___x_996_);
lean_dec(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1002_, 0, v_name_991_);
lean_ctor_set(v___x_1002_, 1, v___x_999_);
v___x_1003_ = lean_unbox(v___x_1001_);
lean_dec(v___x_1001_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*2, v___x_1003_);
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_add(v_i_986_, v___x_1004_);
v___x_1006_ = lean_array_uset(v_bs_x27_994_, v_i_986_, v___x_1002_);
v_i_986_ = v___x_1005_;
v_bs_987_ = v___x_1006_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_alreadySpecialized_984_ = stack[0].m_obj;
size_t v_sz_985_ = stack[1].m_num;
size_t v_i_986_ = stack[2].m_num;
lean_object* v_bs_987_ = stack[3].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_984_, v_sz_985_, v_i_986_, v_bs_987_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg___boxed(lean_object* v_alreadySpecialized_1009_, lean_object* v_sz_1010_, lean_object* v_i_1011_, lean_object* v_bs_1012_){
_start:
{
size_t v_sz_boxed_1013_; size_t v_i_boxed_1014_; lean_object* v_res_1015_; 
v_sz_boxed_1013_ = lean_unbox_usize(v_sz_1010_);
lean_dec(v_sz_1010_);
v_i_boxed_1014_ = lean_unbox_usize(v_i_1011_);
lean_dec(v_i_1011_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1009_, v_sz_boxed_1013_, v_i_boxed_1014_, v_bs_1012_);
lean_dec_ref(v_alreadySpecialized_1009_);
return v_res_1015_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(lean_object* v_b_1016_, lean_object* v_info_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_array_push(v_b_1016_, v_info_1017_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_1016_ = stack[0].m_obj;
lean_object* v_info_1017_ = stack[1].m_obj;
lean_object* v___y_1018_ = stack[2].m_obj;
lean_object* v___y_1019_ = stack[3].m_obj;
lean_object* v___y_1020_ = stack[4].m_obj;
lean_object* v___y_1021_ = stack[5].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1016_, v_info_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0___boxed(lean_object* v_b_1027_, lean_object* v_info_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1027_, v_info_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1(lean_object* v_a_1035_, lean_object* v_as_1036_, size_t v_i_1037_, size_t v_stop_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1037_, v_stop_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1036_, v_i_1037_);
v___x_1041_ = lean_nat_dec_eq(v_a_1035_, v___x_1040_);
if (v___x_1041_ == 0)
{
size_t v___x_1042_; size_t v___x_1043_; 
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_add(v_i_1037_, v___x_1042_);
v_i_1037_ = v___x_1043_;
goto _start;
}
else
{
return v___x_1041_;
}
}
else
{
uint8_t v___x_1045_; 
v___x_1045_ = 0;
return v___x_1045_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1035_ = stack[0].m_obj;
lean_object* v_as_1036_ = stack[1].m_obj;
size_t v_i_1037_ = stack[2].m_num;
size_t v_stop_1038_ = stack[3].m_num;
uint8_t v_res_1046_;
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1(v_a_1035_, v_as_1036_, v_i_1037_, v_stop_1038_);
stack->m_num = v_res_1046_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1___boxed(lean_object* v_a_1047_, lean_object* v_as_1048_, lean_object* v_i_1049_, lean_object* v_stop_1050_){
_start:
{
size_t v_i_boxed_1051_; size_t v_stop_boxed_1052_; uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_i_boxed_1051_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_stop_boxed_1052_ = lean_unbox_usize(v_stop_1050_);
lean_dec(v_stop_1050_);
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1(v_a_1047_, v_as_1048_, v_i_boxed_1051_, v_stop_boxed_1052_);
lean_dec_ref(v_as_1048_);
lean_dec(v_a_1047_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(lean_object* v_as_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = lean_array_get_size(v_as_1055_);
v___x_1059_ = lean_nat_dec_lt(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
return v___x_1059_;
}
else
{
if (v___x_1059_ == 0)
{
return v___x_1059_;
}
else
{
size_t v___x_1060_; size_t v___x_1061_; uint8_t v___x_1062_; 
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = lean_usize_of_nat(v___x_1058_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1(v_a_1056_, v_as_1055_, v___x_1060_, v___x_1061_);
return v___x_1062_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1055_ = stack[0].m_obj;
lean_object* v_a_1056_ = stack[1].m_obj;
uint8_t v_res_1063_;
v_res_1063_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v_as_1055_, v_a_1056_);
stack->m_num = v_res_1063_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___boxed(lean_object* v_as_1064_, lean_object* v_a_1065_){
_start:
{
uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v_as_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_as_1064_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(lean_object* v_upperBound_1070_, lean_object* v___x_1071_, lean_object* v_autoSpecialize_1072_, lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v_a_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___y_1083_; uint8_t v___x_1105_; 
v___x_1105_ = lean_nat_dec_lt(v_a_1075_, v_upperBound_1070_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_dec(v_a_1075_);
lean_dec(v___x_1074_);
lean_dec(v___x_1073_);
lean_dec_ref(v_autoSpecialize_1072_);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_b_1076_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_env_1109_; lean_object* v_type_1110_; lean_object* v___x_1111_; 
v___x_1107_ = lean_array_fget_borrowed(v___x_1071_, v_a_1075_);
v___x_1108_ = lean_st_ref_get(v___y_1080_);
v_env_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_env_1109_);
lean_dec(v___x_1108_);
v_type_1110_ = lean_ctor_get(v___x_1107_, 2);
lean_inc_ref(v_type_1110_);
v___x_1111_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_1110_, v___y_1080_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; uint8_t v___y_1123_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___closed__0));
v___x_1137_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v___x_1136_, v_a_1075_);
v___y_1123_ = v___x_1137_;
goto v___jp_1122_;
}
else
{
lean_object* v_val_1138_; uint8_t v___x_1139_; 
v_val_1138_ = lean_ctor_get(v___x_1074_, 0);
v___x_1139_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v_val_1138_, v_a_1075_);
v___y_1123_ = v___x_1139_;
goto v___jp_1122_;
}
v___jp_1113_:
{
lean_object* v___x_1114_; lean_object* v_env_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1114_ = lean_st_ref_get(v___y_1080_);
v_env_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_env_1115_);
lean_dec(v___x_1114_);
v___x_1116_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_1115_, v_type_1110_);
v___x_1117_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1117_, 0, v___x_1116_);
v___x_1118_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1076_, v___x_1117_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
v___y_1083_ = v___x_1118_;
goto v___jp_1082_;
}
v___jp_1119_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_box(4);
v___x_1121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1076_, v___x_1120_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
v___y_1083_ = v___x_1121_;
goto v___jp_1082_;
}
v___jp_1122_:
{
if (v___y_1123_ == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_1109_, v_type_1110_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; 
lean_inc_ref(v_type_1110_);
v___x_1125_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_1110_);
if (v___x_1125_ == 0)
{
if (lean_obj_tag(v_a_1112_) == 0)
{
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
lean_inc_ref(v_autoSpecialize_1072_);
lean_inc(v___x_1074_);
lean_inc(v___x_1073_);
v___x_1126_ = lean_apply_2(v_autoSpecialize_1072_, v___x_1073_, v___x_1074_);
v___x_1127_ = lean_unbox(v___x_1126_);
if (v___x_1127_ == 0)
{
goto v___jp_1119_;
}
else
{
if (lean_obj_tag(v_type_1110_) == 7)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_box(1);
v___x_1129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1076_, v___x_1128_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
v___y_1083_ = v___x_1129_;
goto v___jp_1082_;
}
else
{
goto v___jp_1119_;
}
}
}
else
{
goto v___jp_1113_;
}
}
else
{
lean_dec_ref_known(v_a_1112_, 1);
goto v___jp_1113_;
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_a_1112_);
v___x_1130_ = lean_box(2);
v___x_1131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1076_, v___x_1130_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
v___y_1083_ = v___x_1131_;
goto v___jp_1082_;
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec(v_a_1112_);
v___x_1132_ = lean_box(4);
v___x_1133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1076_, v___x_1132_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
v___y_1083_ = v___x_1133_;
goto v___jp_1082_;
}
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v_a_1112_);
lean_dec_ref(v_env_1109_);
v___x_1134_ = lean_box(3);
v___x_1135_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1076_, v___x_1134_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
v___y_1083_ = v___x_1135_;
goto v___jp_1082_;
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_env_1109_);
lean_dec_ref(v_b_1076_);
lean_dec(v_a_1075_);
lean_dec(v___x_1074_);
lean_dec(v___x_1073_);
lean_dec_ref(v_autoSpecialize_1072_);
v_a_1140_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1111_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1111_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
v___jp_1082_:
{
if (lean_obj_tag(v___y_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1096_; 
v_a_1084_ = lean_ctor_get(v___y_1083_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___y_1083_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1086_ = v___y_1083_;
v_isShared_1087_ = v_isSharedCheck_1096_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___y_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1096_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
if (lean_obj_tag(v_a_1084_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; 
lean_dec(v_a_1075_);
lean_dec(v___x_1074_);
lean_dec(v___x_1073_);
lean_dec_ref(v_autoSpecialize_1072_);
v_a_1088_ = lean_ctor_get(v_a_1084_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v_a_1084_, 1);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v_a_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_del_object(v___x_1086_);
v_a_1092_ = lean_ctor_get(v_a_1084_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_a_1084_, 1);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_a_1075_, v___x_1093_);
lean_dec(v_a_1075_);
v_a_1075_ = v___x_1094_;
v_b_1076_ = v_a_1092_;
goto _start;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_a_1075_);
lean_dec(v___x_1074_);
lean_dec(v___x_1073_);
lean_dec_ref(v_autoSpecialize_1072_);
v_a_1097_ = lean_ctor_get(v___y_1083_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___y_1083_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___y_1083_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___y_1083_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1070_ = stack[0].m_obj;
lean_object* v___x_1071_ = stack[1].m_obj;
lean_object* v_autoSpecialize_1072_ = stack[2].m_obj;
lean_object* v___x_1073_ = stack[3].m_obj;
lean_object* v___x_1074_ = stack[4].m_obj;
lean_object* v_a_1075_ = stack[5].m_obj;
lean_object* v_b_1076_ = stack[6].m_obj;
lean_object* v___y_1077_ = stack[7].m_obj;
lean_object* v___y_1078_ = stack[8].m_obj;
lean_object* v___y_1079_ = stack[9].m_obj;
lean_object* v___y_1080_ = stack[10].m_obj;
lean_object* v_res_1148_;
v_res_1148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(v_upperBound_1070_, v___x_1071_, v_autoSpecialize_1072_, v___x_1073_, v___x_1074_, v_a_1075_, v_b_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
stack->m_obj
 = v_res_1148_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___boxed(lean_object* v_upperBound_1149_, lean_object* v___x_1150_, lean_object* v_autoSpecialize_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v_a_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(v_upperBound_1149_, v___x_1150_, v_autoSpecialize_1151_, v___x_1152_, v___x_1153_, v_a_1154_, v_b_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v___x_1150_);
lean_dec(v_upperBound_1149_);
return v_res_1161_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(lean_object* v_autoSpecialize_1162_, lean_object* v_as_1163_, size_t v_sz_1164_, size_t v_i_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_a_1173_; uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_lt(v_i_1165_, v_sz_1164_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
lean_dec_ref(v_autoSpecialize_1162_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_b_1166_);
return v___x_1178_;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1180_; lean_object* v_toSignature_1181_; lean_object* v_env_1182_; lean_object* v_name_1183_; lean_object* v_params_1184_; uint8_t v___x_1185_; 
v_a_1179_ = lean_array_uget_borrowed(v_as_1163_, v_i_1165_);
v___x_1180_ = lean_st_ref_get(v___y_1170_);
v_toSignature_1181_ = lean_ctor_get(v_a_1179_, 0);
v_env_1182_ = lean_ctor_get(v___x_1180_, 0);
lean_inc_ref(v_env_1182_);
lean_dec(v___x_1180_);
v_name_1183_ = lean_ctor_get(v_toSignature_1181_, 0);
v_params_1184_ = lean_ctor_get(v_toSignature_1181_, 3);
lean_inc(v_name_1183_);
v___x_1185_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1182_, v_name_1183_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v_env_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1186_ = lean_st_ref_get(v___y_1170_);
v_env_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc_ref(v_env_1187_);
lean_dec(v___x_1186_);
v___x_1188_ = lean_array_get_size(v_params_1184_);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
lean_inc_n(v_name_1183_, 2);
v___x_1191_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_1187_, v_name_1183_);
lean_inc_ref(v_autoSpecialize_1162_);
v___x_1192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(v___x_1188_, v_params_1184_, v_autoSpecialize_1162_, v_name_1183_, v___x_1191_, v___x_1189_, v___x_1190_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1194_ = lean_array_push(v_b_1166_, v_a_1193_);
v_a_1173_ = v___x_1194_;
goto v___jp_1172_;
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v_b_1166_);
lean_dec_ref(v_autoSpecialize_1162_);
v_a_1195_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1192_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1192_);
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
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1203_ = lean_array_get_size(v_params_1184_);
v___x_1204_ = lean_box(4);
v___x_1205_ = lean_mk_array(v___x_1203_, v___x_1204_);
v___x_1206_ = lean_array_push(v_b_1166_, v___x_1205_);
v_a_1173_ = v___x_1206_;
goto v___jp_1172_;
}
}
v___jp_1172_:
{
size_t v___x_1174_; size_t v___x_1175_; 
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1165_, v___x_1174_);
v_i_1165_ = v___x_1175_;
v_b_1166_ = v_a_1173_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_autoSpecialize_1162_ = stack[0].m_obj;
lean_object* v_as_1163_ = stack[1].m_obj;
size_t v_sz_1164_ = stack[2].m_num;
size_t v_i_1165_ = stack[3].m_num;
lean_object* v_b_1166_ = stack[4].m_obj;
lean_object* v___y_1167_ = stack[5].m_obj;
lean_object* v___y_1168_ = stack[6].m_obj;
lean_object* v___y_1169_ = stack[7].m_obj;
lean_object* v___y_1170_ = stack[8].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1162_, v_as_1163_, v_sz_1164_, v_i_1165_, v_b_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3___boxed(lean_object* v_autoSpecialize_1208_, lean_object* v_as_1209_, lean_object* v_sz_1210_, lean_object* v_i_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
size_t v_sz_boxed_1218_; size_t v_i_boxed_1219_; lean_object* v_res_1220_; 
v_sz_boxed_1218_ = lean_unbox_usize(v_sz_1210_);
lean_dec(v_sz_1210_);
v_i_boxed_1219_ = lean_unbox_usize(v_i_1211_);
lean_dec(v_i_1211_);
v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1208_, v_as_1209_, v_sz_boxed_1218_, v_i_boxed_1219_, v_b_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v_as_1209_);
return v_res_1220_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(lean_object* v_as_1221_, size_t v_i_1222_, size_t v_stop_1223_){
_start:
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_usize_dec_eq(v_i_1222_, v_stop_1223_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = 1;
v___x_1230_ = lean_array_uget_borrowed(v_as_1221_, v_i_1222_);
switch(lean_obj_tag(v___x_1230_))
{
case 0:
{
uint8_t v_weak_1231_; 
v_weak_1231_ = lean_ctor_get_uint8(v___x_1230_, 0);
if (v_weak_1231_ == 0)
{
return v___x_1229_;
}
else
{
goto v___jp_1224_;
}
}
case 2:
{
goto v___jp_1224_;
}
case 4:
{
goto v___jp_1224_;
}
default: 
{
return v___x_1229_;
}
}
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = 0;
return v___x_1232_;
}
v___jp_1224_:
{
size_t v___x_1225_; size_t v___x_1226_; 
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = lean_usize_add(v_i_1222_, v___x_1225_);
v_i_1222_ = v___x_1226_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1221_ = stack[0].m_obj;
size_t v_i_1222_ = stack[1].m_num;
size_t v_stop_1223_ = stack[2].m_num;
uint8_t v_res_1233_;
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_as_1221_, v_i_1222_, v_stop_1223_);
stack->m_num = v_res_1233_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0___boxed(lean_object* v_as_1234_, lean_object* v_i_1235_, lean_object* v_stop_1236_){
_start:
{
size_t v_i_boxed_1237_; size_t v_stop_boxed_1238_; uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_i_boxed_1237_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_stop_boxed_1238_ = lean_unbox_usize(v_stop_1236_);
lean_dec(v_stop_1236_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_as_1234_, v_i_boxed_1237_, v_stop_boxed_1238_);
lean_dec_ref(v_as_1234_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(lean_object* v_as_1241_, size_t v_i_1242_, size_t v_stop_1243_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_eq(v_i_1242_, v_stop_1243_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1249_ = lean_array_uget_borrowed(v_as_1241_, v_i_1242_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_array_get_size(v___x_1249_);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
goto v___jp_1244_;
}
else
{
if (v___x_1252_ == 0)
{
goto v___jp_1244_;
}
else
{
size_t v___x_1253_; size_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = lean_usize_of_nat(v___x_1251_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v___x_1249_, v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
goto v___jp_1244_;
}
else
{
return v___x_1255_;
}
}
}
}
else
{
uint8_t v___x_1256_; 
v___x_1256_ = 0;
return v___x_1256_;
}
v___jp_1244_:
{
size_t v___x_1245_; size_t v___x_1246_; 
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_add(v_i_1242_, v___x_1245_);
v_i_1242_ = v___x_1246_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1241_ = stack[0].m_obj;
size_t v_i_1242_ = stack[1].m_num;
size_t v_stop_1243_ = stack[2].m_num;
uint8_t v_res_1257_;
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_as_1241_, v_i_1242_, v_stop_1243_);
stack->m_num = v_res_1257_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5___boxed(lean_object* v_as_1258_, lean_object* v_i_1259_, lean_object* v_stop_1260_){
_start:
{
size_t v_i_boxed_1261_; size_t v_stop_boxed_1262_; uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_i_boxed_1261_ = lean_unbox_usize(v_i_1259_);
lean_dec(v_i_1259_);
v_stop_boxed_1262_ = lean_unbox_usize(v_stop_1260_);
lean_dec(v_stop_1260_);
v_res_1263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_as_1258_, v_i_boxed_1261_, v_stop_boxed_1262_);
lean_dec_ref(v_as_1258_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(lean_object* v_as_1265_, lean_object* v_bs_1266_, lean_object* v_i_1267_, lean_object* v_cs_1268_){
_start:
{
lean_object* v___y_1270_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_array_get_size(v_as_1265_);
v___x_1276_ = lean_nat_dec_lt(v_i_1267_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec(v_i_1267_);
return v_cs_1268_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_array_get_size(v_bs_1266_);
v___x_1278_ = lean_nat_dec_lt(v_i_1267_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_dec(v_i_1267_);
return v_cs_1268_;
}
else
{
lean_object* v_a_1279_; lean_object* v_b_1280_; uint8_t v___x_1281_; 
v_a_1279_ = lean_array_fget_borrowed(v_as_1265_, v_i_1267_);
v_b_1280_ = lean_array_fget_borrowed(v_bs_1266_, v_i_1267_);
v___x_1281_ = lean_unbox(v_b_1280_);
if (v___x_1281_ == 0)
{
if (lean_obj_tag(v_a_1279_) == 3)
{
v___y_1270_ = v_a_1279_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_box(4);
v___y_1270_ = v___x_1282_;
goto v___jp_1269_;
}
}
else
{
lean_inc(v_a_1279_);
v___y_1270_ = v_a_1279_;
goto v___jp_1269_;
}
}
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_i_1267_, v___x_1271_);
lean_dec(v_i_1267_);
v___x_1273_ = lean_array_push(v_cs_1268_, v___y_1270_);
v_i_1267_ = v___x_1272_;
v_cs_1268_ = v___x_1273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6___boxed(lean_object* v_as_1283_, lean_object* v_bs_1284_, lean_object* v_i_1285_, lean_object* v_cs_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v_as_1283_, v_bs_1284_, v_i_1285_, v_cs_1286_);
lean_dec_ref(v_bs_1284_);
lean_dec_ref(v_as_1283_);
return v_res_1287_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(lean_object* v_upperBound_1288_, lean_object* v___x_1289_, lean_object* v_a_1290_, lean_object* v_b_1291_){
_start:
{
lean_object* v_a_1294_; uint8_t v___x_1298_; 
v___x_1298_ = lean_nat_dec_lt(v_a_1290_, v_upperBound_1288_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_dec(v_a_1290_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_b_1291_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default));
v___x_1301_ = lean_array_get_borrowed(v___x_1300_, v_b_1291_, v_a_1290_);
if (lean_obj_tag(v___x_1301_) == 2)
{
uint8_t v___x_1302_; 
v___x_1302_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v___x_1289_, v_b_1291_, v_a_1290_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_box(4);
v___x_1304_ = lean_array_set(v_b_1291_, v_a_1290_, v___x_1303_);
v_a_1294_ = v___x_1304_;
goto v___jp_1293_;
}
else
{
v_a_1294_ = v_b_1291_;
goto v___jp_1293_;
}
}
else
{
v_a_1294_ = v_b_1291_;
goto v___jp_1293_;
}
}
v___jp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_add(v_a_1290_, v___x_1295_);
lean_dec(v_a_1290_);
v_a_1290_ = v___x_1296_;
v_b_1291_ = v_a_1294_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1288_ = stack[0].m_obj;
lean_object* v___x_1289_ = stack[1].m_obj;
lean_object* v_a_1290_ = stack[2].m_obj;
lean_object* v_b_1291_ = stack[3].m_obj;
lean_object* v_res_1305_;
v_res_1305_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1288_, v___x_1289_, v_a_1290_, v_b_1291_);
stack->m_obj
 = v_res_1305_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg___boxed(lean_object* v_upperBound_1306_, lean_object* v___x_1307_, lean_object* v_a_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1306_, v___x_1307_, v_a_1308_, v_b_1309_);
lean_dec_ref(v___x_1307_);
lean_dec(v_upperBound_1306_);
return v_res_1311_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Array_instInhabited___redArg();
return v___x_1312_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3));
v___x_1317_ = lean_unsigned_to_nat(43u);
v___x_1318_ = lean_unsigned_to_nat(236u);
v___x_1319_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2));
v___x_1320_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1));
v___x_1321_ = l_mkPanicMessageWithDecl(v___x_1320_, v___x_1319_, v___x_1318_, v___x_1317_, v___x_1316_);
return v___x_1321_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(lean_object* v_upperBound_1322_, lean_object* v_decls_1323_, lean_object* v_alreadySpecialized_1324_, lean_object* v___x_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_a_1335_; uint8_t v___x_1339_; 
v___x_1339_ = lean_nat_dec_lt(v_a_1327_, v_upperBound_1322_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_dec(v_a_1327_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_b_1328_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; lean_object* v_toSignature_1342_; lean_object* v_name_1343_; lean_object* v___x_1344_; 
v___x_1341_ = lean_array_fget_borrowed(v_decls_1323_, v_a_1327_);
v_toSignature_1342_ = lean_ctor_get(v___x_1341_, 0);
v_name_1343_ = lean_ctor_get(v_toSignature_1342_, 0);
v___x_1344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1325_, v_name_1343_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = 0;
v___x_1347_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0);
v___x_1348_ = lean_array_get_borrowed(v___x_1347_, v_a_1326_, v_a_1327_);
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1351_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v___x_1348_, v_val_1345_, v___x_1349_, v___x_1350_);
lean_dec(v_val_1345_);
v___x_1352_ = lean_array_get_size(v___x_1351_);
v___x_1353_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v___x_1352_, v___x_1341_, v___x_1349_, v___x_1351_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1355_ = lean_box(v___x_1346_);
v___x_1356_ = lean_array_get(v___x_1355_, v_alreadySpecialized_1324_, v_a_1327_);
lean_dec(v___x_1355_);
lean_inc(v_name_1343_);
v___x_1357_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1357_, 0, v_name_1343_);
lean_ctor_set(v___x_1357_, 1, v_a_1354_);
v___x_1358_ = lean_unbox(v___x_1356_);
lean_dec(v___x_1356_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*2, v___x_1358_);
v___x_1359_ = lean_array_push(v_b_1328_, v___x_1357_);
v_a_1335_ = v___x_1359_;
goto v___jp_1334_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v_b_1328_);
lean_dec(v_a_1327_);
v_a_1360_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1353_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1353_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v___x_1344_);
v___x_1368_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4);
v___x_1369_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v___x_1368_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec_ref_known(v___x_1369_, 1);
v_a_1335_ = v_b_1328_;
goto v___jp_1334_;
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_b_1328_);
lean_dec(v_a_1327_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
v___jp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v_a_1327_, v___x_1336_);
lean_dec(v_a_1327_);
v_a_1327_ = v___x_1337_;
v_b_1328_ = v_a_1335_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1322_ = stack[0].m_obj;
lean_object* v_decls_1323_ = stack[1].m_obj;
lean_object* v_alreadySpecialized_1324_ = stack[2].m_obj;
lean_object* v___x_1325_ = stack[3].m_obj;
lean_object* v_a_1326_ = stack[4].m_obj;
lean_object* v_a_1327_ = stack[5].m_obj;
lean_object* v_b_1328_ = stack[6].m_obj;
lean_object* v___y_1329_ = stack[7].m_obj;
lean_object* v___y_1330_ = stack[8].m_obj;
lean_object* v___y_1331_ = stack[9].m_obj;
lean_object* v___y_1332_ = stack[10].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1322_, v_decls_1323_, v_alreadySpecialized_1324_, v___x_1325_, v_a_1326_, v_a_1327_, v_b_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___boxed(lean_object* v_upperBound_1379_, lean_object* v_decls_1380_, lean_object* v_alreadySpecialized_1381_, lean_object* v___x_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_b_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1379_, v_decls_1380_, v_alreadySpecialized_1381_, v___x_1382_, v_a_1383_, v_a_1384_, v_b_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec_ref(v_a_1383_);
lean_dec(v___x_1382_);
lean_dec_ref(v_alreadySpecialized_1381_);
lean_dec_ref(v_decls_1380_);
lean_dec(v_upperBound_1379_);
return v_res_1391_;
}
}
lean_object* l_Lean_Compiler_LCNF_computeSpecEntries(lean_object* v_decls_1394_, lean_object* v_autoSpecialize_1395_, lean_object* v_alreadySpecialized_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v_declsInfo_1403_; size_t v_sz_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v_declsInfo_1403_ = ((lean_object*)(l_Lean_Compiler_LCNF_computeSpecEntries___closed__0));
v_sz_1404_ = lean_array_size(v_decls_1394_);
v___x_1405_ = ((size_t)0ULL);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1395_, v_decls_1394_, v_sz_1404_, v___x_1405_, v_declsInfo_1403_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1424_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1424_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1424_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = lean_array_get_size(v_a_1407_);
v___x_1417_ = lean_nat_dec_lt(v___x_1402_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_dec(v_a_1407_);
goto v___jp_1411_;
}
else
{
if (v___x_1417_ == 0)
{
lean_dec(v_a_1407_);
goto v___jp_1411_;
}
else
{
size_t v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = lean_usize_of_nat(v___x_1416_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_a_1407_, v___x_1405_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_dec(v_a_1407_);
goto v___jp_1411_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_del_object(v___x_1409_);
v___x_1420_ = lean_array_get_size(v_decls_1394_);
v___x_1421_ = lean_mk_empty_array_with_capacity(v___x_1420_);
lean_inc_ref(v_decls_1394_);
v___x_1422_ = l_Lean_Compiler_LCNF_mkFixedParamsMap(v_decls_1394_);
v___x_1423_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v___x_1420_, v_decls_1394_, v_alreadySpecialized_1396_, v___x_1422_, v_a_1407_, v___x_1402_, v___x_1421_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1407_);
lean_dec(v___x_1422_);
lean_dec_ref(v_decls_1394_);
return v___x_1423_;
}
}
}
v___jp_1411_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1396_, v_sz_1404_, v___x_1405_, v_decls_1394_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1412_);
v___x_1414_ = v___x_1409_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_decls_1394_);
v_a_1425_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1406_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1406_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_computeSpecEntries_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1394_ = stack[0].m_obj;
lean_object* v_autoSpecialize_1395_ = stack[1].m_obj;
lean_object* v_alreadySpecialized_1396_ = stack[2].m_obj;
lean_object* v_a_1397_ = stack[3].m_obj;
lean_object* v_a_1398_ = stack[4].m_obj;
lean_object* v_a_1399_ = stack[5].m_obj;
lean_object* v_a_1400_ = stack[6].m_obj;
lean_object* v_res_1433_;
v_res_1433_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1394_, v_autoSpecialize_1395_, v_alreadySpecialized_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
stack->m_obj
 = v_res_1433_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries___boxed(lean_object* v_decls_1434_, lean_object* v_autoSpecialize_1435_, lean_object* v_alreadySpecialized_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1434_, v_autoSpecialize_1435_, v_alreadySpecialized_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_alreadySpecialized_1436_);
return v_res_1442_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(lean_object* v_upperBound_1443_, lean_object* v___x_1444_, lean_object* v_autoSpecialize_1445_, lean_object* v___x_1446_, lean_object* v___x_1447_, lean_object* v_inst_1448_, lean_object* v_R_1449_, lean_object* v_a_1450_, lean_object* v_b_1451_, lean_object* v_c_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(v_upperBound_1443_, v___x_1444_, v_autoSpecialize_1445_, v___x_1446_, v___x_1447_, v_a_1450_, v_b_1451_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1443_ = stack[0].m_obj;
lean_object* v___x_1444_ = stack[1].m_obj;
lean_object* v_autoSpecialize_1445_ = stack[2].m_obj;
lean_object* v___x_1446_ = stack[3].m_obj;
lean_object* v___x_1447_ = stack[4].m_obj;
lean_object* v_a_1450_ = stack[7].m_obj;
lean_object* v_b_1451_ = stack[8].m_obj;
lean_object* v___y_1453_ = stack[10].m_obj;
lean_object* v___y_1454_ = stack[11].m_obj;
lean_object* v___y_1455_ = stack[12].m_obj;
lean_object* v___y_1456_ = stack[13].m_obj;
lean_object* v_res_1459_;
v_res_1459_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_upperBound_1443_, v___x_1444_, v_autoSpecialize_1445_, v___x_1446_, v___x_1447_, lean_box(0), lean_box(0), v_a_1450_, v_b_1451_, lean_box(0), v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
stack->m_obj
 = v_res_1459_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___boxed(lean_object* v_upperBound_1460_, lean_object* v___x_1461_, lean_object* v_autoSpecialize_1462_, lean_object* v___x_1463_, lean_object* v___x_1464_, lean_object* v_inst_1465_, lean_object* v_R_1466_, lean_object* v_a_1467_, lean_object* v_b_1468_, lean_object* v_c_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_upperBound_1460_, v___x_1461_, v_autoSpecialize_1462_, v___x_1463_, v___x_1464_, v_inst_1465_, v_R_1466_, v_a_1467_, v_b_1468_, v_c_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec_ref(v___x_1461_);
lean_dec(v_upperBound_1460_);
return v_res_1475_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(lean_object* v_alreadySpecialized_1476_, lean_object* v_as_1477_, size_t v_sz_1478_, size_t v_i_1479_, lean_object* v_bs_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1476_, v_sz_1478_, v_i_1479_, v_bs_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_alreadySpecialized_1476_ = stack[0].m_obj;
lean_object* v_as_1477_ = stack[1].m_obj;
size_t v_sz_1478_ = stack[2].m_num;
size_t v_i_1479_ = stack[3].m_num;
lean_object* v_bs_1480_ = stack[4].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(v_alreadySpecialized_1476_, v_as_1477_, v_sz_1478_, v_i_1479_, v_bs_1480_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___boxed(lean_object* v_alreadySpecialized_1483_, lean_object* v_as_1484_, lean_object* v_sz_1485_, lean_object* v_i_1486_, lean_object* v_bs_1487_){
_start:
{
size_t v_sz_boxed_1488_; size_t v_i_boxed_1489_; lean_object* v_res_1490_; 
v_sz_boxed_1488_ = lean_unbox_usize(v_sz_1485_);
lean_dec(v_sz_1485_);
v_i_boxed_1489_ = lean_unbox_usize(v_i_1486_);
lean_dec(v_i_1486_);
v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(v_alreadySpecialized_1483_, v_as_1484_, v_sz_boxed_1488_, v_i_boxed_1489_, v_bs_1487_);
lean_dec_ref(v_as_1484_);
lean_dec_ref(v_alreadySpecialized_1483_);
return v_res_1490_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(lean_object* v_upperBound_1491_, lean_object* v___x_1492_, lean_object* v_inst_1493_, lean_object* v_R_1494_, lean_object* v_a_1495_, lean_object* v_b_1496_, lean_object* v_c_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1491_, v___x_1492_, v_a_1495_, v_b_1496_);
return v___x_1503_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1491_ = stack[0].m_obj;
lean_object* v___x_1492_ = stack[1].m_obj;
lean_object* v_a_1495_ = stack[4].m_obj;
lean_object* v_b_1496_ = stack[5].m_obj;
lean_object* v___y_1498_ = stack[7].m_obj;
lean_object* v___y_1499_ = stack[8].m_obj;
lean_object* v___y_1500_ = stack[9].m_obj;
lean_object* v___y_1501_ = stack[10].m_obj;
lean_object* v_res_1504_;
v_res_1504_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(v_upperBound_1491_, v___x_1492_, lean_box(0), lean_box(0), v_a_1495_, v_b_1496_, lean_box(0), v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
stack->m_obj
 = v_res_1504_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___boxed(lean_object* v_upperBound_1505_, lean_object* v___x_1506_, lean_object* v_inst_1507_, lean_object* v_R_1508_, lean_object* v_a_1509_, lean_object* v_b_1510_, lean_object* v_c_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(v_upperBound_1505_, v___x_1506_, v_inst_1507_, v_R_1508_, v_a_1509_, v_b_1510_, v_c_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v___x_1506_);
lean_dec(v_upperBound_1505_);
return v_res_1517_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(lean_object* v_upperBound_1518_, lean_object* v_decls_1519_, lean_object* v_alreadySpecialized_1520_, lean_object* v___x_1521_, lean_object* v_a_1522_, lean_object* v_inst_1523_, lean_object* v_R_1524_, lean_object* v_a_1525_, lean_object* v_b_1526_, lean_object* v_c_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1518_, v_decls_1519_, v_alreadySpecialized_1520_, v___x_1521_, v_a_1522_, v_a_1525_, v_b_1526_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1518_ = stack[0].m_obj;
lean_object* v_decls_1519_ = stack[1].m_obj;
lean_object* v_alreadySpecialized_1520_ = stack[2].m_obj;
lean_object* v___x_1521_ = stack[3].m_obj;
lean_object* v_a_1522_ = stack[4].m_obj;
lean_object* v_a_1525_ = stack[7].m_obj;
lean_object* v_b_1526_ = stack[8].m_obj;
lean_object* v___y_1528_ = stack[10].m_obj;
lean_object* v___y_1529_ = stack[11].m_obj;
lean_object* v___y_1530_ = stack[12].m_obj;
lean_object* v___y_1531_ = stack[13].m_obj;
lean_object* v_res_1534_;
v_res_1534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(v_upperBound_1518_, v_decls_1519_, v_alreadySpecialized_1520_, v___x_1521_, v_a_1522_, lean_box(0), lean_box(0), v_a_1525_, v_b_1526_, lean_box(0), v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
stack->m_obj
 = v_res_1534_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___boxed(lean_object* v_upperBound_1535_, lean_object* v_decls_1536_, lean_object* v_alreadySpecialized_1537_, lean_object* v___x_1538_, lean_object* v_a_1539_, lean_object* v_inst_1540_, lean_object* v_R_1541_, lean_object* v_a_1542_, lean_object* v_b_1543_, lean_object* v_c_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(v_upperBound_1535_, v_decls_1536_, v_alreadySpecialized_1537_, v___x_1538_, v_a_1539_, v_inst_1540_, v_R_1541_, v_a_1542_, v_b_1543_, v_c_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v_a_1539_);
lean_dec(v___x_1538_);
lean_dec_ref(v_alreadySpecialized_1537_);
lean_dec_ref(v_decls_1536_);
lean_dec(v_upperBound_1535_);
return v_res_1550_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1554_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
lean_ctor_set(v___x_1556_, 2, v___x_1555_);
lean_ctor_set(v___x_1556_, 3, v___x_1555_);
lean_ctor_set(v___x_1556_, 4, v___x_1554_);
lean_ctor_set(v___x_1556_, 5, v___x_1554_);
lean_ctor_set(v___x_1556_, 6, v___x_1554_);
lean_ctor_set(v___x_1556_, 7, v___x_1554_);
lean_ctor_set(v___x_1556_, 8, v___x_1554_);
lean_ctor_set(v___x_1556_, 9, v___x_1554_);
lean_ctor_set(v___x_1556_, 10, v___x_1554_);
lean_ctor_set(v___x_1556_, 11, v___x_1553_);
return v___x_1556_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1557_; double v___x_1558_; 
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = lean_float_of_nat(v___x_1557_);
return v___x_1558_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(lean_object* v_cls_1562_, lean_object* v_msg_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_ref_1569_; lean_object* v___x_1570_; lean_object* v_env_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_ref_1569_ = lean_ctor_get(v___y_1566_, 2);
v___x_1570_ = lean_st_ref_get(v___y_1567_);
v_env_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_ref(v_env_1571_);
lean_dec(v___x_1570_);
v___x_1572_ = lean_st_ref_get(v___y_1565_);
v___x_1573_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1564_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1633_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1633_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1633_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_lctx_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1631_; 
v_lctx_1578_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v___x_1572_, 1);
lean_dec(v_unused_1632_);
v___x_1580_ = v___x_1572_;
v_isShared_1581_ = v_isSharedCheck_1631_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_lctx_1578_);
lean_dec(v___x_1572_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1631_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1582_ = lean_unbox(v_a_1574_);
lean_dec(v_a_1574_);
v___x_1583_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1578_, v___x_1582_);
lean_dec_ref(v_lctx_1578_);
v___x_1584_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1566_);
v___x_1585_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1);
v___x_1586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1586_, 0, v_env_1571_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
lean_ctor_set(v___x_1586_, 2, v___x_1583_);
lean_ctor_set(v___x_1586_, 3, v___x_1584_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 3);
lean_ctor_set(v___x_1580_, 1, v_msg_1563_);
lean_ctor_set(v___x_1580_, 0, v___x_1586_);
v___x_1588_ = v___x_1580_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_msg_1563_);
v___x_1588_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v_traceState_1590_; lean_object* v_env_1591_; lean_object* v_nextMacroScope_1592_; lean_object* v_ngen_1593_; lean_object* v_auxDeclNGen_1594_; lean_object* v_cache_1595_; lean_object* v_recordedDeps_1596_; lean_object* v_messages_1597_; lean_object* v_infoState_1598_; lean_object* v_snapshotTasks_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1629_; 
v___x_1589_ = lean_st_ref_take(v___y_1567_);
v_traceState_1590_ = lean_ctor_get(v___x_1589_, 4);
v_env_1591_ = lean_ctor_get(v___x_1589_, 0);
v_nextMacroScope_1592_ = lean_ctor_get(v___x_1589_, 1);
v_ngen_1593_ = lean_ctor_get(v___x_1589_, 2);
v_auxDeclNGen_1594_ = lean_ctor_get(v___x_1589_, 3);
v_cache_1595_ = lean_ctor_get(v___x_1589_, 5);
v_recordedDeps_1596_ = lean_ctor_get(v___x_1589_, 6);
v_messages_1597_ = lean_ctor_get(v___x_1589_, 7);
v_infoState_1598_ = lean_ctor_get(v___x_1589_, 8);
v_snapshotTasks_1599_ = lean_ctor_get(v___x_1589_, 9);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1601_ = v___x_1589_;
v_isShared_1602_ = v_isSharedCheck_1629_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_snapshotTasks_1599_);
lean_inc(v_infoState_1598_);
lean_inc(v_messages_1597_);
lean_inc(v_recordedDeps_1596_);
lean_inc(v_cache_1595_);
lean_inc(v_traceState_1590_);
lean_inc(v_auxDeclNGen_1594_);
lean_inc(v_ngen_1593_);
lean_inc(v_nextMacroScope_1592_);
lean_inc(v_env_1591_);
lean_dec(v___x_1589_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1629_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
uint64_t v_tid_1603_; lean_object* v_traces_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1628_; 
v_tid_1603_ = lean_ctor_get_uint64(v_traceState_1590_, sizeof(void*)*1);
v_traces_1604_ = lean_ctor_get(v_traceState_1590_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_traceState_1590_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1606_ = v_traceState_1590_;
v_isShared_1607_ = v_isSharedCheck_1628_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_traces_1604_);
lean_dec(v_traceState_1590_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1628_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; double v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1608_ = lean_box(0);
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2);
v___x_1611_ = 0;
v___x_1612_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3));
v___x_1613_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1613_, 0, v_cls_1562_);
lean_ctor_set(v___x_1613_, 1, v___x_1609_);
lean_ctor_set(v___x_1613_, 2, v___x_1612_);
lean_ctor_set_float(v___x_1613_, sizeof(void*)*3, v___x_1610_);
lean_ctor_set_float(v___x_1613_, sizeof(void*)*3 + 8, v___x_1610_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 16, v___x_1611_);
v___x_1614_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4));
v___x_1615_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1588_);
lean_ctor_set(v___x_1615_, 2, v___x_1614_);
lean_inc(v_ref_1569_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_ref_1569_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_PersistentArray_push___redArg(v_traces_1604_, v___x_1616_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1617_);
v___x_1619_ = v___x_1606_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1617_);
lean_ctor_set_uint64(v_reuseFailAlloc_1627_, sizeof(void*)*1, v_tid_1603_);
v___x_1619_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 4, v___x_1619_);
v___x_1621_ = v___x_1601_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_env_1591_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_nextMacroScope_1592_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_ngen_1593_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_auxDeclNGen_1594_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1626_, 5, v_cache_1595_);
lean_ctor_set(v_reuseFailAlloc_1626_, 6, v_recordedDeps_1596_);
lean_ctor_set(v_reuseFailAlloc_1626_, 7, v_messages_1597_);
lean_ctor_set(v_reuseFailAlloc_1626_, 8, v_infoState_1598_);
lean_ctor_set(v_reuseFailAlloc_1626_, 9, v_snapshotTasks_1599_);
v___x_1621_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = lean_st_ref_put(v___y_1567_, v___x_1621_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1608_);
v___x_1624_ = v___x_1576_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1608_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
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
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v___x_1572_);
lean_dec_ref(v_env_1571_);
lean_dec_ref(v_msg_1563_);
lean_dec(v_cls_1562_);
v_a_1634_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1573_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1573_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
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
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1562_ = stack[0].m_obj;
lean_object* v_msg_1563_ = stack[1].m_obj;
lean_object* v___y_1564_ = stack[2].m_obj;
lean_object* v___y_1565_ = stack[3].m_obj;
lean_object* v___y_1566_ = stack[4].m_obj;
lean_object* v___y_1567_ = stack[5].m_obj;
lean_object* v_res_1642_;
v_res_1642_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v_cls_1562_, v_msg_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
stack->m_obj
 = v_res_1642_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___boxed(lean_object* v_cls_1643_, lean_object* v_msg_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v_cls_1643_, v_msg_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1650_;
}
}
uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(lean_object* v_xs_1651_, lean_object* v_ys_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v_zero_1654_; uint8_t v_isZero_1655_; 
v_zero_1654_ = lean_unsigned_to_nat(0u);
v_isZero_1655_ = lean_nat_dec_eq(v_x_1653_, v_zero_1654_);
if (v_isZero_1655_ == 1)
{
lean_dec(v_x_1653_);
return v_isZero_1655_;
}
else
{
lean_object* v_one_1656_; lean_object* v_n_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_one_1656_ = lean_unsigned_to_nat(1u);
v_n_1657_ = lean_nat_sub(v_x_1653_, v_one_1656_);
lean_dec(v_x_1653_);
v___x_1658_ = lean_array_fget_borrowed(v_xs_1651_, v_n_1657_);
v___x_1659_ = lean_array_fget_borrowed(v_ys_1652_, v_n_1657_);
v___x_1660_ = lean_nat_dec_eq(v___x_1658_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_dec(v_n_1657_);
return v___x_1660_;
}
else
{
v_x_1653_ = v_n_1657_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1651_ = stack[0].m_obj;
lean_object* v_ys_1652_ = stack[1].m_obj;
lean_object* v_x_1653_ = stack[2].m_obj;
uint8_t v_res_1662_;
v_res_1662_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1651_, v_ys_1652_, v_x_1653_);
stack->m_num = v_res_1662_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg___boxed(lean_object* v_xs_1663_, lean_object* v_ys_1664_, lean_object* v_x_1665_){
_start:
{
uint8_t v_res_1666_; lean_object* v_r_1667_; 
v_res_1666_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1663_, v_ys_1664_, v_x_1665_);
lean_dec_ref(v_ys_1664_);
lean_dec_ref(v_xs_1663_);
v_r_1667_ = lean_box(v_res_1666_);
return v_r_1667_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
if (lean_obj_tag(v_x_1668_) == 0)
{
if (lean_obj_tag(v_x_1669_) == 0)
{
uint8_t v___x_1670_; 
v___x_1670_ = 1;
return v___x_1670_;
}
else
{
uint8_t v___x_1671_; 
v___x_1671_ = 0;
return v___x_1671_;
}
}
else
{
if (lean_obj_tag(v_x_1669_) == 0)
{
uint8_t v___x_1672_; 
v___x_1672_ = 0;
return v___x_1672_;
}
else
{
lean_object* v_val_1673_; lean_object* v_val_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v_val_1673_ = lean_ctor_get(v_x_1668_, 0);
v_val_1674_ = lean_ctor_get(v_x_1669_, 0);
v___x_1675_ = lean_array_get_size(v_val_1673_);
v___x_1676_ = lean_array_get_size(v_val_1674_);
v___x_1677_ = lean_nat_dec_eq(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
return v___x_1677_;
}
else
{
uint8_t v___x_1678_; 
v___x_1678_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_val_1673_, v_val_1674_, v___x_1675_);
return v___x_1678_;
}
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1668_ = stack[0].m_obj;
lean_object* v_x_1669_ = stack[1].m_obj;
uint8_t v_res_1679_;
v_res_1679_ = l_instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_x_1668_, v_x_1669_);
stack->m_num = v_res_1679_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0___boxed(lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
uint8_t v_res_1682_; lean_object* v_r_1683_; 
v_res_1682_ = l_instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_x_1680_, v_x_1681_);
lean_dec(v_x_1681_);
lean_dec(v_x_1680_);
v_r_1683_ = lean_box(v_res_1682_);
return v_r_1683_;
}
}
uint8_t l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(lean_object* v_x_1686_, lean_object* v_specArgs_x3f_1687_){
_start:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0));
v___x_1689_ = l_instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_specArgs_x3f_1687_, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_saveSpecEntries___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1686_ = stack[0].m_obj;
lean_object* v_specArgs_x3f_1687_ = stack[1].m_obj;
uint8_t v_res_1690_;
v_res_1690_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(v_x_1686_, v_specArgs_x3f_1687_);
stack->m_num = v_res_1690_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed(lean_object* v_x_1691_, lean_object* v_specArgs_x3f_1692_){
_start:
{
uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_res_1693_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(v_x_1691_, v_specArgs_x3f_1692_);
lean_dec(v_specArgs_x3f_1692_);
lean_dec(v_x_1691_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
if (lean_obj_tag(v_a_1695_) == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = l_List_reverse___redArg(v_a_1696_);
return v___x_1697_;
}
else
{
lean_object* v_head_1698_; lean_object* v_tail_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1716_; 
v_head_1698_ = lean_ctor_get(v_a_1695_, 0);
v_tail_1699_ = lean_ctor_get(v_a_1695_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_a_1695_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1701_ = v_a_1695_;
v_isShared_1702_ = v_isSharedCheck_1716_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_tail_1699_);
lean_inc(v_head_1698_);
lean_dec(v_a_1695_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1716_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___y_1704_; 
switch(lean_obj_tag(v_head_1698_))
{
case 0:
{
uint8_t v_weak_1709_; 
v_weak_1709_ = lean_ctor_get_uint8(v_head_1698_, 0);
lean_dec_ref_known(v_head_1698_, 0);
if (v_weak_1709_ == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
v___y_1704_ = v___x_1710_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
v___y_1704_ = v___x_1711_;
goto v___jp_1703_;
}
}
case 1:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8);
v___y_1704_ = v___x_1712_;
goto v___jp_1703_;
}
case 2:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11);
v___y_1704_ = v___x_1713_;
goto v___jp_1703_;
}
case 3:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14);
v___y_1704_ = v___x_1714_;
goto v___jp_1703_;
}
default: 
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17);
v___y_1704_ = v___x_1715_;
goto v___jp_1703_;
}
}
v___jp_1703_:
{
lean_object* v___x_1706_; 
lean_inc_ref(v___y_1704_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v_a_1696_);
lean_ctor_set(v___x_1701_, 0, v___y_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___y_1704_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_a_1696_);
v___x_1706_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
v_a_1695_ = v_tail_1699_;
v_a_1696_ = v___x_1706_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___lam__0(lean_object* v___x_1717_, lean_object* v_a_1718_, lean_object* v_s_1719_){
_start:
{
lean_object* v_addEntryFn_1720_; lean_object* v_importedEntries_1721_; lean_object* v_state_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1730_; 
v_addEntryFn_1720_ = lean_ctor_get(v___x_1717_, 3);
lean_inc(v_addEntryFn_1720_);
lean_dec_ref(v___x_1717_);
v_importedEntries_1721_ = lean_ctor_get(v_s_1719_, 0);
v_state_1722_ = lean_ctor_get(v_s_1719_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_s_1719_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1724_ = v_s_1719_;
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_state_1722_);
lean_inc(v_importedEntries_1721_);
lean_dec(v_s_1719_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_state_1726_; lean_object* v___x_1728_; 
v_state_1726_ = lean_apply_2(v_addEntryFn_1720_, v_state_1722_, v_a_1718_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v_state_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_importedEntries_1721_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_state_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0);
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
return v___x_1734_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4));
v___x_1745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6));
v___x_1746_ = l_Lean_Name_append(v___x_1745_, v___x_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8));
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
return v___x_1749_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(lean_object* v_as_1750_, size_t v_sz_1751_, size_t v_i_1752_, lean_object* v_b_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_a_1760_; uint8_t v___x_1764_; 
v___x_1764_ = lean_usize_dec_lt(v_i_1752_, v_sz_1751_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_b_1753_);
return v___x_1765_;
}
else
{
lean_object* v_a_1766_; lean_object* v_declName_1767_; lean_object* v_paramsInfo_1768_; lean_object* v___x_1769_; lean_object* v_nextMacroScope_1771_; lean_object* v_ngen_1772_; lean_object* v_auxDeclNGen_1773_; lean_object* v_traceState_1774_; lean_object* v_recordedDeps_1775_; lean_object* v_messages_1776_; lean_object* v_infoState_1777_; lean_object* v_snapshotTasks_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v_a_1766_ = lean_array_uget_borrowed(v_as_1750_, v_i_1752_);
v_declName_1767_ = lean_ctor_get(v_a_1766_, 0);
v_paramsInfo_1768_ = lean_ctor_get(v_a_1766_, 1);
v___x_1769_ = lean_box(0);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_array_get_size(v_paramsInfo_1768_);
v___x_1786_ = lean_nat_dec_lt(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
v_a_1760_ = v___x_1769_;
goto v___jp_1759_;
}
else
{
if (v___x_1786_ == 0)
{
v_a_1760_ = v___x_1769_;
goto v___jp_1759_;
}
else
{
size_t v___x_1787_; size_t v___x_1788_; uint8_t v___x_1789_; lean_object* v___y_1791_; 
v___x_1787_ = ((size_t)0ULL);
v___x_1788_ = lean_usize_of_nat(v___x_1785_);
v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_paramsInfo_1768_, v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
v_a_1760_ = v___x_1769_;
goto v___jp_1759_;
}
else
{
lean_object* v_toCold_1811_; lean_object* v_options_1812_; uint8_t v_hasTrace_1813_; 
v_toCold_1811_ = lean_ctor_get(v___y_1756_, 0);
v_options_1812_ = lean_ctor_get(v_toCold_1811_, 2);
v_hasTrace_1813_ = lean_ctor_get_uint8(v_options_1812_, sizeof(void*)*1);
if (v_hasTrace_1813_ == 0)
{
v___y_1791_ = v___y_1757_;
goto v___jp_1790_;
}
else
{
lean_object* v_inheritedTraceOptions_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_inheritedTraceOptions_1814_ = lean_ctor_get(v_toCold_1811_, 11);
v___x_1815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4));
v___x_1816_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7);
v___x_1817_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1814_, v_options_1812_, v___x_1816_);
if (v___x_1817_ == 0)
{
v___y_1791_ = v___y_1757_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_inc(v_declName_1767_);
v___x_1818_ = l_Lean_MessageData_ofName(v_declName_1767_);
v___x_1819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
lean_inc_ref(v_paramsInfo_1768_);
v___x_1821_ = lean_array_to_list(v_paramsInfo_1768_);
v___x_1822_ = lean_box(0);
v___x_1823_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(v___x_1821_, v___x_1822_);
v___x_1824_ = l_Lean_MessageData_ofList(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1820_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v___x_1815_, v___x_1825_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_dec_ref_known(v___x_1826_, 1);
v___y_1791_ = v___y_1757_;
goto v___jp_1790_;
}
else
{
return v___x_1826_;
}
}
}
}
v___jp_1790_:
{
lean_object* v___x_1792_; lean_object* v_env_1793_; lean_object* v_nextMacroScope_1794_; lean_object* v_ngen_1795_; lean_object* v_auxDeclNGen_1796_; lean_object* v_traceState_1797_; lean_object* v_recordedDeps_1798_; lean_object* v_messages_1799_; lean_object* v_infoState_1800_; lean_object* v_snapshotTasks_1801_; lean_object* v___x_1802_; lean_object* v_toEnvExtension_1803_; lean_object* v_asyncMode_1804_; uint8_t v_logWrites_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; 
v___x_1792_ = lean_st_ref_take(v___y_1791_);
v_env_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc_ref(v_env_1793_);
v_nextMacroScope_1794_ = lean_ctor_get(v___x_1792_, 1);
lean_inc(v_nextMacroScope_1794_);
v_ngen_1795_ = lean_ctor_get(v___x_1792_, 2);
lean_inc_ref(v_ngen_1795_);
v_auxDeclNGen_1796_ = lean_ctor_get(v___x_1792_, 3);
lean_inc_ref(v_auxDeclNGen_1796_);
v_traceState_1797_ = lean_ctor_get(v___x_1792_, 4);
lean_inc_ref(v_traceState_1797_);
v_recordedDeps_1798_ = lean_ctor_get(v___x_1792_, 6);
lean_inc_ref(v_recordedDeps_1798_);
v_messages_1799_ = lean_ctor_get(v___x_1792_, 7);
lean_inc_ref(v_messages_1799_);
v_infoState_1800_ = lean_ctor_get(v___x_1792_, 8);
lean_inc_ref(v_infoState_1800_);
v_snapshotTasks_1801_ = lean_ctor_get(v___x_1792_, 9);
lean_inc_ref(v_snapshotTasks_1801_);
lean_dec(v___x_1792_);
v___x_1802_ = l_Lean_Compiler_LCNF_specExtension;
v_toEnvExtension_1803_ = lean_ctor_get(v___x_1802_, 0);
v_asyncMode_1804_ = lean_ctor_get(v_toEnvExtension_1803_, 2);
v_logWrites_1805_ = lean_ctor_get_uint8(v_toEnvExtension_1803_, sizeof(void*)*6);
lean_inc(v_a_1766_);
v___f_1806_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_1806_, 0, v___x_1802_);
lean_closure_set(v___f_1806_, 1, v_a_1766_);
v___x_1807_ = lean_box(0);
if (v_logWrites_1805_ == 0)
{
lean_object* v___x_1808_; 
lean_inc_ref(v_toEnvExtension_1803_);
v___x_1808_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1803_, v_env_1793_, v___f_1806_, v_asyncMode_1804_, v___x_1807_, v___x_1789_);
v_nextMacroScope_1771_ = v_nextMacroScope_1794_;
v_ngen_1772_ = v_ngen_1795_;
v_auxDeclNGen_1773_ = v_auxDeclNGen_1796_;
v_traceState_1774_ = v_traceState_1797_;
v_recordedDeps_1775_ = v_recordedDeps_1798_;
v_messages_1776_ = v_messages_1799_;
v_infoState_1777_ = v_infoState_1800_;
v_snapshotTasks_1778_ = v_snapshotTasks_1801_;
v___y_1779_ = v___y_1791_;
v___y_1780_ = v___x_1808_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_inc_ref_n(v_toEnvExtension_1803_, 2);
v___x_1809_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1803_, v_env_1793_);
lean_dec_ref(v_env_1793_);
v___x_1810_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1803_, v___x_1809_, v___f_1806_, v_asyncMode_1804_, v___x_1807_, v___x_1789_);
v_nextMacroScope_1771_ = v_nextMacroScope_1794_;
v_ngen_1772_ = v_ngen_1795_;
v_auxDeclNGen_1773_ = v_auxDeclNGen_1796_;
v_traceState_1774_ = v_traceState_1797_;
v_recordedDeps_1775_ = v_recordedDeps_1798_;
v_messages_1776_ = v_messages_1799_;
v_infoState_1777_ = v_infoState_1800_;
v_snapshotTasks_1778_ = v_snapshotTasks_1801_;
v___y_1779_ = v___y_1791_;
v___y_1780_ = v___x_1810_;
goto v___jp_1770_;
}
}
}
}
v___jp_1770_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1);
v___x_1782_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1782_, 0, v___y_1780_);
lean_ctor_set(v___x_1782_, 1, v_nextMacroScope_1771_);
lean_ctor_set(v___x_1782_, 2, v_ngen_1772_);
lean_ctor_set(v___x_1782_, 3, v_auxDeclNGen_1773_);
lean_ctor_set(v___x_1782_, 4, v_traceState_1774_);
lean_ctor_set(v___x_1782_, 5, v___x_1781_);
lean_ctor_set(v___x_1782_, 6, v_recordedDeps_1775_);
lean_ctor_set(v___x_1782_, 7, v_messages_1776_);
lean_ctor_set(v___x_1782_, 8, v_infoState_1777_);
lean_ctor_set(v___x_1782_, 9, v_snapshotTasks_1778_);
v___x_1783_ = lean_st_ref_put(v___y_1779_, v___x_1782_);
v_a_1760_ = v___x_1769_;
goto v___jp_1759_;
}
}
v___jp_1759_:
{
size_t v___x_1761_; size_t v___x_1762_; 
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1752_, v___x_1761_);
v_i_1752_ = v___x_1762_;
v_b_1753_ = v_a_1760_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1750_ = stack[0].m_obj;
size_t v_sz_1751_ = stack[1].m_num;
size_t v_i_1752_ = stack[2].m_num;
lean_object* v_b_1753_ = stack[3].m_obj;
lean_object* v___y_1754_ = stack[4].m_obj;
lean_object* v___y_1755_ = stack[5].m_obj;
lean_object* v___y_1756_ = stack[6].m_obj;
lean_object* v___y_1757_ = stack[7].m_obj;
lean_object* v_res_1827_;
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_as_1750_, v_sz_1751_, v_i_1752_, v_b_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
stack->m_obj
 = v_res_1827_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___boxed(lean_object* v_as_1828_, lean_object* v_sz_1829_, lean_object* v_i_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
size_t v_sz_boxed_1837_; size_t v_i_boxed_1838_; lean_object* v_res_1839_; 
v_sz_boxed_1837_ = lean_unbox_usize(v_sz_1829_);
lean_dec(v_sz_1829_);
v_i_boxed_1838_ = lean_unbox_usize(v_i_1830_);
lean_dec(v_i_1830_);
v_res_1839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_as_1828_, v_sz_boxed_1837_, v_i_boxed_1838_, v_b_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_as_1828_);
return v_res_1839_;
}
}
lean_object* l_Lean_Compiler_LCNF_saveSpecEntries(lean_object* v_decls_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v___f_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___f_1847_ = ((lean_object*)(l_Lean_Compiler_LCNF_saveSpecEntries___closed__0));
v___x_1848_ = lean_array_get_size(v_decls_1841_);
v___x_1849_ = 0;
v___x_1850_ = lean_box(v___x_1849_);
v___x_1851_ = lean_mk_array(v___x_1848_, v___x_1850_);
v___x_1852_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1841_, v___f_1847_, v___x_1851_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec_ref(v___x_1851_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; size_t v_sz_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = lean_box(0);
v_sz_1855_ = lean_array_size(v_a_1853_);
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_a_1853_, v_sz_1855_, v___x_1856_, v___x_1854_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1853_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v___x_1857_, 0);
lean_dec(v_unused_1865_);
v___x_1859_ = v___x_1857_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_dec(v___x_1857_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1854_);
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1854_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
return v___x_1857_;
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1852_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1852_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_saveSpecEntries_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1841_ = stack[0].m_obj;
lean_object* v_a_1842_ = stack[1].m_obj;
lean_object* v_a_1843_ = stack[2].m_obj;
lean_object* v_a_1844_ = stack[3].m_obj;
lean_object* v_a_1845_ = stack[4].m_obj;
lean_object* v_res_1874_;
v_res_1874_ = l_Lean_Compiler_LCNF_saveSpecEntries(v_decls_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
stack->m_obj
 = v_res_1874_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___boxed(lean_object* v_decls_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Compiler_LCNF_saveSpecEntries(v_decls_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
return v_res_1881_;
}
}
uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(lean_object* v_xs_1882_, lean_object* v_ys_1883_, lean_object* v_hsz_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
uint8_t v___x_1887_; 
v___x_1887_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1882_, v_ys_1883_, v_x_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1882_ = stack[0].m_obj;
lean_object* v_ys_1883_ = stack[1].m_obj;
lean_object* v_x_1885_ = stack[3].m_obj;
uint8_t v_res_1888_;
v_res_1888_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(v_xs_1882_, v_ys_1883_, lean_box(0), v_x_1885_, lean_box(0));
stack->m_num = v_res_1888_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___boxed(lean_object* v_xs_1889_, lean_object* v_ys_1890_, lean_object* v_hsz_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
uint8_t v_res_1894_; lean_object* v_r_1895_; 
v_res_1894_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(v_xs_1889_, v_ys_1890_, v_hsz_1891_, v_x_1892_, v_x_1893_);
lean_dec_ref(v_ys_1890_);
lean_dec_ref(v_xs_1889_);
v_r_1895_ = lean_box(v_res_1894_);
return v_r_1895_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(lean_object* v_as_1896_, lean_object* v_k_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v_m_1902_; lean_object* v_a_1903_; uint8_t v___x_1904_; 
v___x_1900_ = lean_nat_add(v_x_1898_, v_x_1899_);
v___x_1901_ = lean_unsigned_to_nat(1u);
v_m_1902_ = lean_nat_shiftr(v___x_1900_, v___x_1901_);
lean_dec(v___x_1900_);
v_a_1903_ = lean_array_fget_borrowed(v_as_1896_, v_m_1902_);
v___x_1904_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_a_1903_, v_k_1897_);
if (v___x_1904_ == 0)
{
uint8_t v___x_1905_; 
lean_dec(v_x_1899_);
v___x_1905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_k_1897_, v_a_1903_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
lean_dec(v_m_1902_);
lean_dec(v_x_1898_);
lean_inc(v_a_1903_);
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_a_1903_);
return v___x_1906_;
}
else
{
lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_nat_dec_eq(v_m_1902_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = lean_nat_sub(v_m_1902_, v___x_1901_);
lean_dec(v_m_1902_);
v___x_1910_ = lean_nat_dec_lt(v___x_1909_, v_x_1898_);
if (v___x_1910_ == 0)
{
v_x_1899_ = v___x_1909_;
goto _start;
}
else
{
lean_object* v___x_1912_; 
lean_dec(v___x_1909_);
lean_dec(v_x_1898_);
v___x_1912_ = lean_box(0);
return v___x_1912_;
}
}
else
{
lean_object* v___x_1913_; 
lean_dec(v_m_1902_);
lean_dec(v_x_1898_);
v___x_1913_ = lean_box(0);
return v___x_1913_;
}
}
}
else
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
lean_dec(v_x_1898_);
v___x_1914_ = lean_nat_add(v_m_1902_, v___x_1901_);
lean_dec(v_m_1902_);
v___x_1915_ = lean_nat_dec_le(v___x_1914_, v_x_1899_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
lean_dec(v___x_1914_);
lean_dec(v_x_1899_);
v___x_1916_ = lean_box(0);
return v___x_1916_;
}
else
{
v_x_1898_ = v___x_1914_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg___boxed(lean_object* v_as_1918_, lean_object* v_k_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v_as_1918_, v_k_1919_, v_x_1920_, v_x_1921_);
lean_dec_ref(v_k_1919_);
lean_dec_ref(v_as_1918_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1923_, lean_object* v_vals_1924_, lean_object* v_i_1925_, lean_object* v_k_1926_){
_start:
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_array_get_size(v_keys_1923_);
v___x_1928_ = lean_nat_dec_lt(v_i_1925_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
lean_dec(v_i_1925_);
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
else
{
lean_object* v_k_x27_1930_; uint8_t v___x_1931_; 
v_k_x27_1930_ = lean_array_fget_borrowed(v_keys_1923_, v_i_1925_);
v___x_1931_ = lean_name_eq(v_k_1926_, v_k_x27_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_unsigned_to_nat(1u);
v___x_1933_ = lean_nat_add(v_i_1925_, v___x_1932_);
lean_dec(v_i_1925_);
v_i_1925_ = v___x_1933_;
goto _start;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_array_fget_borrowed(v_vals_1924_, v_i_1925_);
lean_dec(v_i_1925_);
lean_inc(v___x_1935_);
v___x_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1937_, lean_object* v_vals_1938_, lean_object* v_i_1939_, lean_object* v_k_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1937_, v_vals_1938_, v_i_1939_, v_k_1940_);
lean_dec(v_k_1940_);
lean_dec_ref(v_vals_1938_);
lean_dec_ref(v_keys_1937_);
return v_res_1941_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_1942_, size_t v_x_1943_, lean_object* v_x_1944_){
_start:
{
if (lean_obj_tag(v_x_1942_) == 0)
{
lean_object* v_es_1945_; lean_object* v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; lean_object* v_j_1949_; lean_object* v___x_1950_; 
v_es_1945_ = lean_ctor_get(v_x_1942_, 0);
v___x_1946_ = lean_box(2);
v___x_1947_ = ((size_t)31ULL);
v___x_1948_ = lean_usize_land(v_x_1943_, v___x_1947_);
v_j_1949_ = lean_usize_to_nat(v___x_1948_);
v___x_1950_ = lean_array_get_borrowed(v___x_1946_, v_es_1945_, v_j_1949_);
lean_dec(v_j_1949_);
switch(lean_obj_tag(v___x_1950_))
{
case 0:
{
lean_object* v_key_1951_; lean_object* v_val_1952_; uint8_t v___x_1953_; 
v_key_1951_ = lean_ctor_get(v___x_1950_, 0);
v_val_1952_ = lean_ctor_get(v___x_1950_, 1);
v___x_1953_ = lean_name_eq(v_x_1944_, v_key_1951_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_box(0);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; 
lean_inc(v_val_1952_);
v___x_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1955_, 0, v_val_1952_);
return v___x_1955_;
}
}
case 1:
{
lean_object* v_node_1956_; size_t v___x_1957_; size_t v___x_1958_; 
v_node_1956_ = lean_ctor_get(v___x_1950_, 0);
v___x_1957_ = ((size_t)5ULL);
v___x_1958_ = lean_usize_shift_right(v_x_1943_, v___x_1957_);
v_x_1942_ = v_node_1956_;
v_x_1943_ = v___x_1958_;
goto _start;
}
default: 
{
lean_object* v___x_1960_; 
v___x_1960_ = lean_box(0);
return v___x_1960_;
}
}
}
else
{
lean_object* v_ks_1961_; lean_object* v_vs_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_ks_1961_ = lean_ctor_get(v_x_1942_, 0);
v_vs_1962_ = lean_ctor_get(v_x_1942_, 1);
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1961_, v_vs_1962_, v___x_1963_, v_x_1944_);
return v___x_1964_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1942_ = stack[0].m_obj;
size_t v_x_1943_ = stack[1].m_num;
lean_object* v_x_1944_ = stack[2].m_obj;
lean_object* v_res_1965_;
v_res_1965_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1942_, v_x_1943_, v_x_1944_);
stack->m_obj
 = v_res_1965_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_){
_start:
{
size_t v_x_447__boxed_1969_; lean_object* v_res_1970_; 
v_x_447__boxed_1969_ = lean_unbox_usize(v_x_1967_);
lean_dec(v_x_1967_);
v_res_1970_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1966_, v_x_447__boxed_1969_, v_x_1968_);
lean_dec(v_x_1968_);
lean_dec_ref(v_x_1966_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
uint64_t v___y_1974_; 
if (lean_obj_tag(v_x_1972_) == 0)
{
uint64_t v___x_1977_; 
v___x_1977_ = 1723ULL;
v___y_1974_ = v___x_1977_;
goto v___jp_1973_;
}
else
{
uint64_t v_hash_1978_; 
v_hash_1978_ = lean_ctor_get_uint64(v_x_1972_, sizeof(void*)*2);
v___y_1974_ = v_hash_1978_;
goto v___jp_1973_;
}
v___jp_1973_:
{
size_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_uint64_to_usize(v___y_1974_);
v___x_1976_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1971_, v___x_1975_, v_x_1972_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg___boxed(lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_1979_, v_x_1980_);
lean_dec(v_x_1980_);
lean_dec_ref(v_x_1979_);
return v_res_1981_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v___x_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(lean_object* v_env_1985_, lean_object* v_declName_1986_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1997_; 
v___x_1987_ = lean_obj_once(&l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0, &l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0);
v___x_1988_ = l_Lean_Compiler_LCNF_specExtension;
v___x_1997_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1985_, v_declName_1986_);
if (lean_obj_tag(v___x_1997_) == 0)
{
goto v___jp_1989_;
}
else
{
lean_object* v_val_1998_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_val_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_2012_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1987_, v___x_1988_, v_env_1985_, v_val_1998_);
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_array_get_size(v___x_2012_);
v___x_2015_ = lean_nat_dec_lt(v___x_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_dec_ref(v___x_2012_);
goto v___jp_1999_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = lean_unsigned_to_nat(1u);
v___x_2017_ = lean_nat_sub(v___x_2014_, v___x_2016_);
v___x_2018_ = lean_nat_dec_le(v___x_2013_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_dec(v___x_2017_);
lean_dec_ref(v___x_2012_);
goto v___jp_1999_;
}
else
{
lean_object* v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_2020_ = 0;
lean_inc(v_declName_1986_);
v___x_2021_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2021_, 0, v_declName_1986_);
lean_ctor_set(v___x_2021_, 1, v___x_2019_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*2, v___x_2020_);
v___x_2022_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_2012_, v___x_2021_, v___x_2013_, v___x_2017_);
lean_dec_ref_known(v___x_2021_, 2);
lean_dec_ref(v___x_2012_);
if (lean_obj_tag(v___x_2022_) == 0)
{
goto v___jp_1999_;
}
else
{
lean_dec(v_val_1998_);
lean_dec(v_declName_1986_);
lean_dec_ref(v_env_1985_);
return v___x_2022_;
}
}
}
v___jp_1999_:
{
uint8_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2000_ = 0;
v___x_2001_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1987_, v___x_1988_, v_env_1985_, v_val_1998_, v___x_2000_);
lean_dec(v_val_1998_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = lean_array_get_size(v___x_2001_);
v___x_2004_ = lean_nat_dec_lt(v___x_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v___x_2001_);
goto v___jp_1989_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_nat_sub(v___x_2003_, v___x_2005_);
v___x_2007_ = lean_nat_dec_le(v___x_2002_, v___x_2006_);
if (v___x_2007_ == 0)
{
lean_dec(v___x_2006_);
lean_dec_ref(v___x_2001_);
goto v___jp_1989_;
}
else
{
lean_object* v___x_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_2009_ = 0;
lean_inc(v_declName_1986_);
v___x_2010_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2010_, 0, v_declName_1986_);
lean_ctor_set(v___x_2010_, 1, v___x_2008_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*2, v___x_2009_);
v___x_2011_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_2001_, v___x_2010_, v___x_2002_, v___x_2006_);
lean_dec_ref_known(v___x_2010_, 2);
lean_dec_ref(v___x_2001_);
if (lean_obj_tag(v___x_2011_) == 0)
{
goto v___jp_1989_;
}
else
{
lean_dec(v_declName_1986_);
lean_dec_ref(v_env_1985_);
return v___x_2011_;
}
}
}
}
}
v___jp_1989_:
{
lean_object* v_toEnvExtension_1990_; lean_object* v_asyncMode_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v_snd_1995_; lean_object* v___x_1996_; 
v_toEnvExtension_1990_ = lean_ctor_get(v___x_1988_, 0);
v_asyncMode_1991_ = lean_ctor_get(v_toEnvExtension_1990_, 2);
v___x_1992_ = lean_box(0);
v___x_1993_ = 0;
v___x_1994_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1987_, v___x_1988_, v_env_1985_, v_asyncMode_1991_, v___x_1992_, v___x_1993_);
v_snd_1995_ = lean_ctor_get(v___x_1994_, 1);
lean_inc(v_snd_1995_);
lean_dec(v___x_1994_);
v___x_1996_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_snd_1995_, v_declName_1986_);
lean_dec(v_declName_1986_);
lean_dec(v_snd_1995_);
return v___x_1996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(lean_object* v_00_u03b2_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_2024_, v_x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(v_00_u03b2_2027_, v_x_2028_, v_x_2029_);
lean_dec(v_x_2029_);
lean_dec_ref(v_x_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(lean_object* v_as_2031_, lean_object* v_k_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v_as_2031_, v_k_2032_, v_x_2033_, v_x_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___boxed(lean_object* v_as_2037_, lean_object* v_k_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(v_as_2037_, v_k_2038_, v_x_2039_, v_x_2040_, v_x_2041_);
lean_dec_ref(v_k_2038_);
lean_dec_ref(v_as_2037_);
return v_res_2042_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2043_, lean_object* v_x_2044_, size_t v_x_2045_, lean_object* v_x_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_2044_, v_x_2045_, v_x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2044_ = stack[1].m_obj;
size_t v_x_2045_ = stack[2].m_num;
lean_object* v_x_2046_ = stack[3].m_obj;
lean_object* v_res_2048_;
v_res_2048_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(lean_box(0), v_x_2044_, v_x_2045_, v_x_2046_);
stack->m_obj
 = v_res_2048_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
size_t v_x_692__boxed_2053_; lean_object* v_res_2054_; 
v_x_692__boxed_2053_ = lean_unbox_usize(v_x_2051_);
lean_dec(v_x_2051_);
v_res_2054_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(v_00_u03b2_2049_, v_x_2050_, v_x_692__boxed_2053_, v_x_2052_);
lean_dec(v_x_2052_);
lean_dec_ref(v_x_2050_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2055_, lean_object* v_keys_2056_, lean_object* v_vals_2057_, lean_object* v_heq_2058_, lean_object* v_i_2059_, lean_object* v_k_2060_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2056_, v_vals_2057_, v_i_2059_, v_k_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2062_, lean_object* v_keys_2063_, lean_object* v_vals_2064_, lean_object* v_heq_2065_, lean_object* v_i_2066_, lean_object* v_k_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2062_, v_keys_2063_, v_vals_2064_, v_heq_2065_, v_i_2066_, v_k_2067_);
lean_dec(v_k_2067_);
lean_dec_ref(v_vals_2064_);
lean_dec_ref(v_keys_2063_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0(lean_object* v_declName_2069_, lean_object* v_toPure_2070_, lean_object* v_____do__lift_2071_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_2071_, v_declName_2069_);
v___x_2073_ = lean_apply_2(v_toPure_2070_, lean_box(0), v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_declName_2076_){
_start:
{
lean_object* v_toApplicative_2077_; lean_object* v_toBind_2078_; lean_object* v_getEnv_2079_; lean_object* v_toPure_2080_; lean_object* v___f_2081_; lean_object* v___x_2082_; 
v_toApplicative_2077_ = lean_ctor_get(v_inst_2074_, 0);
lean_inc_ref(v_toApplicative_2077_);
v_toBind_2078_ = lean_ctor_get(v_inst_2074_, 1);
lean_inc(v_toBind_2078_);
lean_dec_ref(v_inst_2074_);
v_getEnv_2079_ = lean_ctor_get(v_inst_2075_, 0);
lean_inc(v_getEnv_2079_);
lean_dec_ref(v_inst_2075_);
v_toPure_2080_ = lean_ctor_get(v_toApplicative_2077_, 1);
lean_inc(v_toPure_2080_);
lean_dec_ref(v_toApplicative_2077_);
v___f_2081_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2081_, 0, v_declName_2076_);
lean_closure_set(v___f_2081_, 1, v_toPure_2080_);
v___x_2082_ = lean_apply_4(v_toBind_2078_, lean_box(0), lean_box(0), v_getEnv_2079_, v___f_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f(lean_object* v_m_2083_, lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_declName_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(v_inst_2084_, v_inst_2085_, v_declName_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0(lean_object* v_declName_2088_, lean_object* v_toPure_2089_, lean_object* v_____do__lift_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_2090_, v_declName_2088_);
if (lean_obj_tag(v___x_2091_) == 0)
{
uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = 0;
v___x_2093_ = lean_box(v___x_2092_);
v___x_2094_ = lean_apply_2(v_toPure_2089_, lean_box(0), v___x_2093_);
return v___x_2094_;
}
else
{
uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec_ref_known(v___x_2091_, 1);
v___x_2095_ = 1;
v___x_2096_ = lean_box(v___x_2095_);
v___x_2097_ = lean_apply_2(v_toPure_2089_, lean_box(0), v___x_2096_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg(lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_declName_2100_){
_start:
{
lean_object* v_toApplicative_2101_; lean_object* v_toBind_2102_; lean_object* v_getEnv_2103_; lean_object* v_toPure_2104_; lean_object* v___f_2105_; lean_object* v___x_2106_; 
v_toApplicative_2101_ = lean_ctor_get(v_inst_2098_, 0);
lean_inc_ref(v_toApplicative_2101_);
v_toBind_2102_ = lean_ctor_get(v_inst_2098_, 1);
lean_inc(v_toBind_2102_);
lean_dec_ref(v_inst_2098_);
v_getEnv_2103_ = lean_ctor_get(v_inst_2099_, 0);
lean_inc(v_getEnv_2103_);
lean_dec_ref(v_inst_2099_);
v_toPure_2104_ = lean_ctor_get(v_toApplicative_2101_, 1);
lean_inc(v_toPure_2104_);
lean_dec_ref(v_toApplicative_2101_);
v___f_2105_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2105_, 0, v_declName_2100_);
lean_closure_set(v___f_2105_, 1, v_toPure_2104_);
v___x_2106_ = lean_apply_4(v_toBind_2102_, lean_box(0), lean_box(0), v_getEnv_2103_, v___f_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate(lean_object* v_m_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_declName_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Compiler_LCNF_isSpecCandidate___redArg(v_inst_2108_, v_inst_2109_, v_declName_2110_);
return v___x_2111_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4));
v___x_2177_ = 0;
v___x_2178_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_));
v___x_2179_ = l_Lean_registerTraceClass(v___x_2176_, v___x_2177_, v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2180_;
v_res_2180_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2180_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2____boxed(lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
return v_res_2182_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_SpecInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedSpecState_default = _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedSpecState_default);
l_Lean_Compiler_LCNF_instInhabitedSpecState = _init_l_Lean_Compiler_LCNF_instInhabitedSpecState();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedSpecState);
res = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_specExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_specExtension);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_SpecInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_SpecInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
}
#ifdef __cplusplus
}
#endif
