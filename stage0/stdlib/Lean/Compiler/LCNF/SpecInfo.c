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
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Compiler_hasNospecializeAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getSpecializationArgs_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Compiler_hasWeakSpecializeAttribute(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0;
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value)}};
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_computeSpecEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_computeSpecEntries___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_computeSpecEntries___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 178, 200, 12, 6, 8, 169, 47)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(239, 10, 5, 245, 97, 204, 194, 190)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_saveSpecEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_saveSpecEntries___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
default: 
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx(v_x_7_);
lean_dec(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(lean_object* v_t_9_, lean_object* v_k_10_){
_start:
{
if (lean_obj_tag(v_t_9_) == 0)
{
uint8_t v_weak_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_weak_11_ = lean_ctor_get_uint8(v_t_9_, 0);
v___x_12_ = lean_box(v_weak_11_);
v___x_13_ = lean_apply_1(v_k_10_, v___x_12_);
return v___x_13_;
}
else
{
return v_k_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg___boxed(lean_object* v_t_14_, lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_14_, v_k_15_);
lean_dec(v_t_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___boxed(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_t_25_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(lean_object* v_t_29_, lean_object* v_fixedInst_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_29_, v_fixedInst_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg___boxed(lean_object* v_t_32_, lean_object* v_fixedInst_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(v_t_32_, v_fixedInst_33_);
lean_dec(v_t_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_fixedInst_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_36_, v_fixedInst_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___boxed(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_fixedInst_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(v_motive_40_, v_t_41_, v_h_42_, v_fixedInst_43_);
lean_dec(v_t_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(lean_object* v_t_45_, lean_object* v_fixedHO_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_45_, v_fixedHO_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg___boxed(lean_object* v_t_48_, lean_object* v_fixedHO_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(v_t_48_, v_fixedHO_49_);
lean_dec(v_t_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_fixedHO_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_52_, v_fixedHO_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_fixedHO_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(v_motive_56_, v_t_57_, v_h_58_, v_fixedHO_59_);
lean_dec(v_t_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(lean_object* v_t_61_, lean_object* v_fixedNeutral_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_61_, v_fixedNeutral_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg___boxed(lean_object* v_t_64_, lean_object* v_fixedNeutral_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(v_t_64_, v_fixedNeutral_65_);
lean_dec(v_t_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_fixedNeutral_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_68_, v_fixedNeutral_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_fixedNeutral_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(v_motive_72_, v_t_73_, v_h_74_, v_fixedNeutral_75_);
lean_dec(v_t_73_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(lean_object* v_t_77_, lean_object* v_user_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_77_, v_user_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg___boxed(lean_object* v_t_80_, lean_object* v_user_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(v_t_80_, v_user_81_);
lean_dec(v_t_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_user_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_84_, v_user_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_user_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(v_motive_88_, v_t_89_, v_h_90_, v_user_91_);
lean_dec(v_t_89_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(lean_object* v_t_93_, lean_object* v_other_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_93_, v_other_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg___boxed(lean_object* v_t_96_, lean_object* v_other_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(v_t_96_, v_other_97_);
lean_dec(v_t_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_other_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_100_, v_other_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___boxed(lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_other_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(v_motive_104_, v_t_105_, v_h_106_, v_other_107_);
lean_dec(v_t_105_);
return v_res_108_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(2u);
v___x_132_ = lean_nat_to_int(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_to_int(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(lean_object* v_x_135_, lean_object* v_prec_136_){
_start:
{
lean_object* v___y_138_; lean_object* v___y_145_; lean_object* v___y_152_; lean_object* v___y_159_; 
switch(lean_obj_tag(v_x_135_))
{
case 0:
{
uint8_t v_weak_165_; lean_object* v___y_167_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_weak_165_ = lean_ctor_get_uint8(v_x_135_, 0);
v___x_175_ = lean_unsigned_to_nat(1024u);
v___x_176_ = lean_nat_dec_le(v___x_175_, v_prec_136_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
v___x_177_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_167_ = v___x_177_;
goto v___jp_166_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_167_ = v___x_178_;
goto v___jp_166_;
}
v___jp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_168_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10));
v___x_169_ = l_Bool_repr___redArg(v_weak_165_);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
lean_inc(v___y_167_);
v___x_171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_171_, 0, v___y_167_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = 0;
v___x_173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*1, v___x_172_);
v___x_174_ = l_Repr_addAppParen(v___x_173_, v_prec_136_);
return v___x_174_;
}
}
case 1:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(1024u);
v___x_180_ = lean_nat_dec_le(v___x_179_, v_prec_136_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_138_ = v___x_181_;
goto v___jp_137_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_138_ = v___x_182_;
goto v___jp_137_;
}
}
case 2:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(1024u);
v___x_184_ = lean_nat_dec_le(v___x_183_, v_prec_136_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_145_ = v___x_185_;
goto v___jp_144_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_145_ = v___x_186_;
goto v___jp_144_;
}
}
case 3:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1024u);
v___x_188_ = lean_nat_dec_le(v___x_187_, v_prec_136_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_152_ = v___x_189_;
goto v___jp_151_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_152_ = v___x_190_;
goto v___jp_151_;
}
}
default: 
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(1024u);
v___x_192_ = lean_nat_dec_le(v___x_191_, v_prec_136_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
v___y_159_ = v___x_193_;
goto v___jp_158_;
}
else
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12, &l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once, _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
v___y_159_ = v___x_194_;
goto v___jp_158_;
}
}
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1));
lean_inc(v___y_138_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = l_Repr_addAppParen(v___x_142_, v_prec_136_);
return v___x_143_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_146_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3));
lean_inc(v___y_145_);
v___x_147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_147_, 0, v___y_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = 0;
v___x_149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = l_Repr_addAppParen(v___x_149_, v_prec_136_);
return v___x_150_;
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5));
lean_inc(v___y_152_);
v___x_154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_154_, 0, v___y_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = 0;
v___x_156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_155_);
v___x_157_ = l_Repr_addAppParen(v___x_156_, v_prec_136_);
return v___x_157_;
}
v___jp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_160_ = ((lean_object*)(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7));
lean_inc(v___y_159_);
v___x_161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_161_, 0, v___y_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = 0;
v___x_163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_162_);
v___x_164_ = l_Repr_addAppParen(v___x_163_, v_prec_136_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___boxed(lean_object* v_x_195_, lean_object* v_prec_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(v_x_195_, v_prec_196_);
lean_dec(v_prec_196_);
lean_dec(v_x_195_);
return v_res_197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(lean_object* v_x_200_){
_start:
{
switch(lean_obj_tag(v_x_200_))
{
case 0:
{
uint8_t v_weak_201_; 
v_weak_201_ = lean_ctor_get_uint8(v_x_200_, 0);
if (v_weak_201_ == 0)
{
uint8_t v___x_202_; 
v___x_202_ = 1;
return v___x_202_;
}
else
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
}
case 2:
{
uint8_t v___x_204_; 
v___x_204_ = 0;
return v___x_204_;
}
case 4:
{
uint8_t v___x_205_; 
v___x_205_ = 0;
return v___x_205_;
}
default: 
{
uint8_t v___x_206_; 
v___x_206_ = 1;
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization___boxed(lean_object* v_x_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(v_x_207_);
lean_dec(v_x_207_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1));
v___x_214_ = l_Lean_MessageData_ofFormat(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4));
v___x_219_ = l_Lean_MessageData_ofFormat(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7));
v___x_224_ = l_Lean_MessageData_ofFormat(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10));
v___x_229_ = l_Lean_MessageData_ofFormat(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13));
v___x_234_ = l_Lean_MessageData_ofFormat(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16));
v___x_239_ = l_Lean_MessageData_ofFormat(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(lean_object* v_x_240_){
_start:
{
switch(lean_obj_tag(v_x_240_))
{
case 0:
{
uint8_t v_weak_241_; 
v_weak_241_ = lean_ctor_get_uint8(v_x_240_, 0);
if (v_weak_241_ == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
return v___x_242_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
return v___x_243_;
}
}
case 1:
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8);
return v___x_244_;
}
case 2:
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11);
return v___x_245_;
}
case 3:
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14);
return v___x_246_;
}
default: 
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17);
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___boxed(lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(v_x_248_);
lean_dec(v_x_248_);
return v_res_249_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2));
v___x_265_ = l_Lean_stringToMessageData(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1(lean_object* v___f_268_, lean_object* v_x_269_){
_start:
{
lean_object* v_declName_270_; lean_object* v_paramsInfo_271_; uint8_t v_alreadySpecialized_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___y_277_; 
v_declName_270_ = lean_ctor_get(v_x_269_, 0);
lean_inc(v_declName_270_);
v_paramsInfo_271_ = lean_ctor_get(v_x_269_, 1);
lean_inc_ref(v_paramsInfo_271_);
v_alreadySpecialized_272_ = lean_ctor_get_uint8(v_x_269_, sizeof(void*)*2);
lean_dec_ref(v_x_269_);
v___x_273_ = l_Lean_MessageData_ofName(v_declName_270_);
v___x_274_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1, &l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
if (v_alreadySpecialized_272_ == 0)
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4));
v___y_277_ = v___x_288_;
goto v___jp_276_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5));
v___y_277_ = v___x_289_;
goto v___jp_276_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc_ref(v___y_277_);
v___x_278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_278_, 0, v___y_277_);
v___x_279_ = l_Lean_MessageData_ofFormat(v___x_278_);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_275_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3, &l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_array_to_list(v_paramsInfo_271_);
v___x_284_ = lean_box(0);
v___x_285_ = l_List_mapTR_loop___redArg(v___f_268_, v___x_283_, v___x_284_);
v___x_286_ = l_Lean_MessageData_ofList(v___x_285_);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_282_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default(void){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSpecState(void){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
lean_object* v_ks_302_; lean_object* v_vs_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_327_; 
v_ks_302_ = lean_ctor_get(v_x_298_, 0);
v_vs_303_ = lean_ctor_get(v_x_298_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_327_ == 0)
{
v___x_305_ = v_x_298_;
v_isShared_306_ = v_isSharedCheck_327_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_vs_303_);
lean_inc(v_ks_302_);
lean_dec(v_x_298_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_327_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_array_get_size(v_ks_302_);
v___x_308_ = lean_nat_dec_lt(v_x_299_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec(v_x_299_);
v___x_309_ = lean_array_push(v_ks_302_, v_x_300_);
v___x_310_ = lean_array_push(v_vs_303_, v_x_301_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_310_);
lean_ctor_set(v___x_305_, 0, v___x_309_);
v___x_312_ = v___x_305_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v_k_x27_314_; uint8_t v___x_315_; 
v_k_x27_314_ = lean_array_fget_borrowed(v_ks_302_, v_x_299_);
v___x_315_ = lean_name_eq(v_x_300_, v_k_x27_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_317_; 
if (v_isShared_306_ == 0)
{
v___x_317_ = v___x_305_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_ks_302_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_vs_303_);
v___x_317_ = v_reuseFailAlloc_321_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_x_299_, v___x_318_);
lean_dec(v_x_299_);
v_x_298_ = v___x_317_;
v_x_299_ = v___x_319_;
goto _start;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_array_fset(v_ks_302_, v_x_299_, v_x_300_);
v___x_323_ = lean_array_fset(v_vs_303_, v_x_299_, v_x_301_);
lean_dec(v_x_299_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_323_);
lean_ctor_set(v___x_305_, 0, v___x_322_);
v___x_325_ = v___x_305_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_n_328_, lean_object* v_k_329_, lean_object* v_v_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_328_, v___x_331_, v_k_329_, v_v_330_);
return v___x_332_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_333_; uint64_t v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(1723u);
v___x_334_ = lean_uint64_of_nat(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(lean_object* v_x_336_, size_t v_x_337_, size_t v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v_es_341_; size_t v___x_342_; size_t v___x_343_; lean_object* v_j_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_es_341_ = lean_ctor_get(v_x_336_, 0);
v___x_342_ = ((size_t)31ULL);
v___x_343_ = lean_usize_land(v_x_337_, v___x_342_);
v_j_344_ = lean_usize_to_nat(v___x_343_);
v___x_345_ = lean_array_get_size(v_es_341_);
v___x_346_ = lean_nat_dec_lt(v_j_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_dec(v_j_344_);
lean_dec(v_x_340_);
lean_dec(v_x_339_);
return v_x_336_;
}
else
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_385_; 
lean_inc_ref(v_es_341_);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_x_336_, 0);
lean_dec(v_unused_386_);
v___x_348_ = v_x_336_;
v_isShared_349_ = v_isSharedCheck_385_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_x_336_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_385_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_v_350_; lean_object* v___x_351_; lean_object* v_xs_x27_352_; lean_object* v___y_354_; 
v_v_350_ = lean_array_fget(v_es_341_, v_j_344_);
v___x_351_ = lean_box(0);
v_xs_x27_352_ = lean_array_fset(v_es_341_, v_j_344_, v___x_351_);
switch(lean_obj_tag(v_v_350_))
{
case 0:
{
lean_object* v_key_359_; lean_object* v_val_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_370_; 
v_key_359_ = lean_ctor_get(v_v_350_, 0);
v_val_360_ = lean_ctor_get(v_v_350_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_v_350_);
if (v_isSharedCheck_370_ == 0)
{
v___x_362_ = v_v_350_;
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_val_360_);
lean_inc(v_key_359_);
lean_dec(v_v_350_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
uint8_t v___x_364_; 
v___x_364_ = lean_name_eq(v_x_339_, v_key_359_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_del_object(v___x_362_);
v___x_365_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_359_, v_val_360_, v_x_339_, v_x_340_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
v___y_354_ = v___x_366_;
goto v___jp_353_;
}
else
{
lean_object* v___x_368_; 
lean_dec(v_val_360_);
lean_dec(v_key_359_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_x_340_);
lean_ctor_set(v___x_362_, 0, v_x_339_);
v___x_368_ = v___x_362_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_x_339_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_x_340_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
v___y_354_ = v___x_368_;
goto v___jp_353_;
}
}
}
}
case 1:
{
lean_object* v_node_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_383_; 
v_node_371_ = lean_ctor_get(v_v_350_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_v_350_);
if (v_isSharedCheck_383_ == 0)
{
v___x_373_ = v_v_350_;
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_node_371_);
lean_dec(v_v_350_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_375_ = ((size_t)5ULL);
v___x_376_ = lean_usize_shift_right(v_x_337_, v___x_375_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_x_338_, v___x_377_);
v___x_379_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_node_371_, v___x_376_, v___x_378_, v_x_339_, v_x_340_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_379_);
v___x_381_ = v___x_373_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
v___y_354_ = v___x_381_;
goto v___jp_353_;
}
}
}
default: 
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_x_339_);
lean_ctor_set(v___x_384_, 1, v_x_340_);
v___y_354_ = v___x_384_;
goto v___jp_353_;
}
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = lean_array_fset(v_xs_x27_352_, v_j_344_, v___y_354_);
lean_dec(v_j_344_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_355_);
v___x_357_ = v___x_348_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
else
{
lean_object* v_ks_387_; lean_object* v_vs_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_408_; 
v_ks_387_ = lean_ctor_get(v_x_336_, 0);
v_vs_388_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_408_ == 0)
{
v___x_390_ = v_x_336_;
v_isShared_391_ = v_isSharedCheck_408_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_vs_388_);
lean_inc(v_ks_387_);
lean_dec(v_x_336_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_408_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_ks_387_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_vs_388_);
v___x_393_ = v_reuseFailAlloc_407_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v_newNode_394_; uint8_t v___y_396_; size_t v___x_402_; uint8_t v___x_403_; 
v_newNode_394_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v___x_393_, v_x_339_, v_x_340_);
v___x_402_ = ((size_t)7ULL);
v___x_403_ = lean_usize_dec_le(v___x_402_, v_x_338_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_394_);
v___x_405_ = lean_unsigned_to_nat(4u);
v___x_406_ = lean_nat_dec_lt(v___x_404_, v___x_405_);
lean_dec(v___x_404_);
v___y_396_ = v___x_406_;
goto v___jp_395_;
}
else
{
v___y_396_ = v___x_403_;
goto v___jp_395_;
}
v___jp_395_:
{
if (v___y_396_ == 0)
{
lean_object* v_ks_397_; lean_object* v_vs_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_ks_397_ = lean_ctor_get(v_newNode_394_, 0);
lean_inc_ref(v_ks_397_);
v_vs_398_ = lean_ctor_get(v_newNode_394_, 1);
lean_inc_ref(v_vs_398_);
lean_dec_ref(v_newNode_394_);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0);
v___x_401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_x_338_, v_ks_397_, v_vs_398_, v___x_399_, v___x_400_);
lean_dec_ref(v_vs_398_);
lean_dec_ref(v_ks_397_);
return v___x_401_;
}
else
{
return v_newNode_394_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(size_t v_depth_409_, lean_object* v_keys_410_, lean_object* v_vals_411_, lean_object* v_i_412_, lean_object* v_entries_413_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_array_get_size(v_keys_410_);
v___x_415_ = lean_nat_dec_lt(v_i_412_, v___x_414_);
if (v___x_415_ == 0)
{
lean_dec(v_i_412_);
return v_entries_413_;
}
else
{
lean_object* v_k_416_; lean_object* v_v_417_; uint64_t v___y_419_; 
v_k_416_ = lean_array_fget_borrowed(v_keys_410_, v_i_412_);
v_v_417_ = lean_array_fget_borrowed(v_vals_411_, v_i_412_);
if (lean_obj_tag(v_k_416_) == 0)
{
uint64_t v___x_430_; 
v___x_430_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_419_ = v___x_430_;
goto v___jp_418_;
}
else
{
uint64_t v_hash_431_; 
v_hash_431_ = lean_ctor_get_uint64(v_k_416_, sizeof(void*)*2);
v___y_419_ = v_hash_431_;
goto v___jp_418_;
}
v___jp_418_:
{
size_t v_h_420_; size_t v___x_421_; lean_object* v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v_h_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_h_420_ = lean_uint64_to_usize(v___y_419_);
v___x_421_ = ((size_t)5ULL);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_sub(v_depth_409_, v___x_423_);
v___x_425_ = lean_usize_mul(v___x_421_, v___x_424_);
v_h_426_ = lean_usize_shift_right(v_h_420_, v___x_425_);
v___x_427_ = lean_nat_add(v_i_412_, v___x_422_);
lean_dec(v_i_412_);
lean_inc(v_v_417_);
lean_inc(v_k_416_);
v___x_428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_entries_413_, v_h_426_, v_depth_409_, v_k_416_, v_v_417_);
v_i_412_ = v___x_427_;
v_entries_413_ = v___x_428_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_432_, lean_object* v_keys_433_, lean_object* v_vals_434_, lean_object* v_i_435_, lean_object* v_entries_436_){
_start:
{
size_t v_depth_boxed_437_; lean_object* v_res_438_; 
v_depth_boxed_437_ = lean_unbox_usize(v_depth_432_);
lean_dec(v_depth_432_);
v_res_438_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_boxed_437_, v_keys_433_, v_vals_434_, v_i_435_, v_entries_436_);
lean_dec_ref(v_vals_434_);
lean_dec_ref(v_keys_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
size_t v_x_365__boxed_444_; size_t v_x_366__boxed_445_; lean_object* v_res_446_; 
v_x_365__boxed_444_ = lean_unbox_usize(v_x_440_);
lean_dec(v_x_440_);
v_x_366__boxed_445_ = lean_unbox_usize(v_x_441_);
lean_dec(v_x_441_);
v_res_446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_439_, v_x_365__boxed_444_, v_x_366__boxed_445_, v_x_442_, v_x_443_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
uint64_t v___y_451_; 
if (lean_obj_tag(v_x_448_) == 0)
{
uint64_t v___x_455_; 
v___x_455_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_451_ = v___x_455_;
goto v___jp_450_;
}
else
{
uint64_t v_hash_456_; 
v_hash_456_ = lean_ctor_get_uint64(v_x_448_, sizeof(void*)*2);
v___y_451_ = v_hash_456_;
goto v___jp_450_;
}
v___jp_450_:
{
size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_uint64_to_usize(v___y_451_);
v___x_453_ = ((size_t)1ULL);
v___x_454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_447_, v___x_452_, v___x_453_, v_x_448_, v_x_449_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecState_addEntry(lean_object* v_s_457_, lean_object* v_e_458_){
_start:
{
lean_object* v_declName_459_; lean_object* v___x_460_; 
v_declName_459_ = lean_ctor_get(v_e_458_, 0);
lean_inc(v_declName_459_);
v___x_460_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_s_457_, v_declName_459_, v_e_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0(lean_object* v_00_u03b2_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_x_462_, v_x_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, size_t v_x_468_, size_t v_x_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_467_, v_x_468_, v_x_469_, v_x_470_, v_x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
size_t v_x_556__boxed_479_; size_t v_x_557__boxed_480_; lean_object* v_res_481_; 
v_x_556__boxed_479_ = lean_unbox_usize(v_x_475_);
lean_dec(v_x_475_);
v_x_557__boxed_480_ = lean_unbox_usize(v_x_476_);
lean_dec(v_x_476_);
v_res_481_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(v_00_u03b2_473_, v_x_474_, v_x_556__boxed_479_, v_x_557__boxed_480_, v_x_477_, v_x_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_482_, lean_object* v_n_483_, lean_object* v_k_484_, lean_object* v_v_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v_n_483_, v_k_484_, v_v_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_487_, size_t v_depth_488_, lean_object* v_keys_489_, lean_object* v_vals_490_, lean_object* v_heq_491_, lean_object* v_i_492_, lean_object* v_entries_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_488_, v_keys_489_, v_vals_490_, v_i_492_, v_entries_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_495_, lean_object* v_depth_496_, lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_heq_499_, lean_object* v_i_500_, lean_object* v_entries_501_){
_start:
{
size_t v_depth_boxed_502_; lean_object* v_res_503_; 
v_depth_boxed_502_ = lean_unbox_usize(v_depth_496_);
lean_dec(v_depth_496_);
v_res_503_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(v_00_u03b2_495_, v_depth_boxed_502_, v_keys_497_, v_vals_498_, v_heq_499_, v_i_500_, v_entries_501_);
lean_dec_ref(v_vals_498_);
lean_dec_ref(v_keys_497_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_x_505_, v_x_506_, v_x_507_, v_x_508_);
return v___x_509_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(lean_object* v_a_510_, lean_object* v_b_511_){
_start:
{
lean_object* v_declName_512_; lean_object* v_declName_513_; uint8_t v___x_514_; 
v_declName_512_ = lean_ctor_get(v_a_510_, 0);
v_declName_513_ = lean_ctor_get(v_b_511_, 0);
v___x_514_ = l_Lean_Name_quickLt(v_declName_512_, v_declName_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed(lean_object* v_a_515_, lean_object* v_b_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(v_a_515_, v_b_516_);
lean_dec_ref(v_b_516_);
lean_dec_ref(v_a_515_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries(lean_object* v_entries_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_array_get_size(v_entries_520_);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_nat_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___y_528_; uint8_t v___x_532_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0));
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_sub(v___x_521_, v___x_525_);
v___x_532_ = lean_nat_dec_le(v___x_522_, v___x_526_);
if (v___x_532_ == 0)
{
lean_inc(v___x_526_);
v___y_528_ = v___x_526_;
goto v___jp_527_;
}
else
{
v___y_528_ = v___x_522_;
goto v___jp_527_;
}
v___jp_527_:
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_le(v___y_528_, v___x_526_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
lean_dec(v___x_526_);
lean_inc(v___y_528_);
v___x_530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_524_, v___x_521_, v_entries_520_, v___y_528_, v___y_528_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_528_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_524_, v___x_521_, v_entries_520_, v___y_528_, v___x_526_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_526_);
return v___x_531_;
}
}
}
else
{
return v_entries_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(lean_object* v_entries_536_, lean_object* v_declName_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_array_get_size(v_entries_536_);
v___x_540_ = lean_nat_dec_lt(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_dec(v_declName_537_);
v___x_541_ = lean_box(0);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_sub(v___x_539_, v___x_542_);
v___x_544_ = lean_nat_dec_le(v___x_538_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
lean_dec(v___x_543_);
lean_dec(v_declName_537_);
v___x_545_ = lean_box(0);
return v___x_545_;
}
else
{
lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_546_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_547_ = 0;
v___x_548_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_548_, 0, v_declName_537_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*2, v___x_547_);
v___x_549_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0));
v___x_550_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1));
v___x_551_ = l_Array_binSearchAux___redArg(v___x_549_, v___x_550_, v_entries_536_, v___x_548_, v___x_538_, v___x_543_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___boxed(lean_object* v_entries_552_, lean_object* v_declName_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(v_entries_552_, v_declName_553_);
lean_dec_ref(v_entries_552_);
return v_res_554_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_declName_557_; lean_object* v_declName_558_; uint8_t v___x_559_; 
v_declName_557_ = lean_ctor_get(v___y_555_, 0);
v_declName_558_ = lean_ctor_get(v___y_556_, 0);
v___x_559_ = l_Lean_Name_quickLt(v_declName_557_, v_declName_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0___boxed(lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___y_560_, v___y_561_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v___y_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_hi_564_, lean_object* v_pivot_565_, lean_object* v_as_566_, lean_object* v_i_567_, lean_object* v_k_568_){
_start:
{
uint8_t v___x_569_; 
v___x_569_ = lean_nat_dec_lt(v_k_568_, v_hi_564_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_k_568_);
v___x_570_ = lean_array_fswap(v_as_566_, v_i_567_, v_hi_564_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_i_567_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v_declName_573_; lean_object* v_declName_574_; uint8_t v___x_575_; 
v___x_572_ = lean_array_fget_borrowed(v_as_566_, v_k_568_);
v_declName_573_ = lean_ctor_get(v___x_572_, 0);
v_declName_574_ = lean_ctor_get(v_pivot_565_, 0);
v___x_575_ = l_Lean_Name_quickLt(v_declName_573_, v_declName_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_k_568_, v___x_576_);
lean_dec(v_k_568_);
v_k_568_ = v___x_577_;
goto _start;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = lean_array_fswap(v_as_566_, v_i_567_, v_k_568_);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v_i_567_, v___x_580_);
lean_dec(v_i_567_);
v___x_582_ = lean_nat_add(v_k_568_, v___x_580_);
lean_dec(v_k_568_);
v_as_566_ = v___x_579_;
v_i_567_ = v___x_581_;
v_k_568_ = v___x_582_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_hi_584_, lean_object* v_pivot_585_, lean_object* v_as_586_, lean_object* v_i_587_, lean_object* v_k_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_584_, v_pivot_585_, v_as_586_, v_i_587_, v_k_588_);
lean_dec_ref(v_pivot_585_);
lean_dec(v_hi_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(lean_object* v_n_590_, lean_object* v_as_591_, lean_object* v_lo_592_, lean_object* v_hi_593_){
_start:
{
lean_object* v___y_595_; uint8_t v___x_605_; 
v___x_605_ = lean_nat_dec_lt(v_lo_592_, v_hi_593_);
if (v___x_605_ == 0)
{
lean_dec(v_lo_592_);
return v_as_591_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_mid_608_; lean_object* v___y_610_; lean_object* v___y_616_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_606_ = lean_nat_add(v_lo_592_, v_hi_593_);
v___x_607_ = lean_unsigned_to_nat(1u);
v_mid_608_ = lean_nat_shiftr(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___x_621_ = lean_array_fget_borrowed(v_as_591_, v_mid_608_);
v___x_622_ = lean_array_fget_borrowed(v_as_591_, v_lo_592_);
v___x_623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
v___y_616_ = v_as_591_;
goto v___jp_615_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_array_fswap(v_as_591_, v_lo_592_, v_mid_608_);
v___y_616_ = v___x_624_;
goto v___jp_615_;
}
v___jp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_array_fget_borrowed(v___y_610_, v_mid_608_);
v___x_612_ = lean_array_fget_borrowed(v___y_610_, v_hi_593_);
v___x_613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec(v_mid_608_);
v___y_595_ = v___y_610_;
goto v___jp_594_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_array_fswap(v___y_610_, v_mid_608_, v_hi_593_);
lean_dec(v_mid_608_);
v___y_595_ = v___x_614_;
goto v___jp_594_;
}
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = lean_array_fget_borrowed(v___y_616_, v_hi_593_);
v___x_618_ = lean_array_fget_borrowed(v___y_616_, v_lo_592_);
v___x_619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
v___y_610_ = v___y_616_;
goto v___jp_609_;
}
else
{
lean_object* v___x_620_; 
v___x_620_ = lean_array_fswap(v___y_616_, v_lo_592_, v_hi_593_);
v___y_610_ = v___x_620_;
goto v___jp_609_;
}
}
}
v___jp_594_:
{
lean_object* v_pivot_596_; lean_object* v___x_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; uint8_t v___x_600_; 
v_pivot_596_ = lean_array_fget(v___y_595_, v_hi_593_);
lean_inc_n(v_lo_592_, 2);
v___x_597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_593_, v_pivot_596_, v___y_595_, v_lo_592_, v_lo_592_);
lean_dec(v_pivot_596_);
v_fst_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_fst_598_);
v_snd_599_ = lean_ctor_get(v___x_597_, 1);
lean_inc(v_snd_599_);
lean_dec_ref(v___x_597_);
v___x_600_ = lean_nat_dec_le(v_hi_593_, v_fst_598_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_590_, v_snd_599_, v_lo_592_, v_fst_598_);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_fst_598_, v___x_602_);
lean_dec(v_fst_598_);
v_as_591_ = v___x_601_;
v_lo_592_ = v___x_603_;
goto _start;
}
else
{
lean_dec(v_fst_598_);
lean_dec(v_lo_592_);
return v_snd_599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_n_625_, lean_object* v_as_626_, lean_object* v_lo_627_, lean_object* v_hi_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_625_, v_as_626_, v_lo_627_, v_hi_628_);
lean_dec(v_hi_628_);
lean_dec(v_n_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_s_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_631_ = lean_array_mk(v_s_630_);
v___x_632_ = lean_array_get_size(v___x_631_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_nat_dec_eq(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___y_638_; uint8_t v___x_642_; 
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_sub(v___x_632_, v___x_635_);
v___x_642_ = lean_nat_dec_le(v___x_633_, v___x_636_);
if (v___x_642_ == 0)
{
lean_inc(v___x_636_);
v___y_638_ = v___x_636_;
goto v___jp_637_;
}
else
{
v___y_638_ = v___x_633_;
goto v___jp_637_;
}
v___jp_637_:
{
uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_le(v___y_638_, v___x_636_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec(v___x_636_);
lean_inc(v___y_638_);
v___x_640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_632_, v___x_631_, v___y_638_, v___y_638_);
lean_dec(v___y_638_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_632_, v___x_631_, v___y_638_, v___x_636_);
lean_dec(v___x_636_);
return v___x_641_;
}
}
}
else
{
return v___x_631_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_keys_643_, lean_object* v_i_644_, lean_object* v_k_645_){
_start:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_array_get_size(v_keys_643_);
v___x_647_ = lean_nat_dec_lt(v_i_644_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec(v_i_644_);
return v___x_647_;
}
else
{
lean_object* v_k_x27_648_; uint8_t v___x_649_; 
v_k_x27_648_ = lean_array_fget_borrowed(v_keys_643_, v_i_644_);
v___x_649_ = lean_name_eq(v_k_645_, v_k_x27_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_nat_add(v_i_644_, v___x_650_);
lean_dec(v_i_644_);
v_i_644_ = v___x_651_;
goto _start;
}
else
{
lean_dec(v_i_644_);
return v___x_649_;
}
}
}
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_658_, size_t v_x_659_, lean_object* v_x_660_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
size_t v_x_466__boxed_680_; uint8_t v_res_681_; lean_object* v_r_682_; 
v_x_466__boxed_680_ = lean_unbox_usize(v_x_678_);
lean_dec(v_x_678_);
v_res_681_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_677_, v_x_466__boxed_680_, v_x_679_);
lean_dec(v_x_679_);
lean_dec_ref(v_x_677_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint64_t v___y_686_; 
if (lean_obj_tag(v_x_684_) == 0)
{
uint64_t v___x_689_; 
v___x_689_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_686_ = v___x_689_;
goto v___jp_685_;
}
else
{
uint64_t v_hash_690_; 
v_hash_690_ = lean_ctor_get_uint64(v_x_684_, sizeof(void*)*2);
v___y_686_ = v_hash_690_;
goto v___jp_685_;
}
v___jp_685_:
{
size_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_uint64_to_usize(v___y_686_);
v___x_688_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_683_, v___x_687_, v_x_684_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_691_, v_x_692_);
lean_dec(v_x_692_);
lean_dec_ref(v_x_691_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_x1_695_, lean_object* v_x2_696_){
_start:
{
lean_object* v_declName_697_; uint8_t v___x_698_; 
v_declName_697_ = lean_ctor_get(v_x2_696_, 0);
v___x_698_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x1_695_, v_declName_697_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
v___x_699_ = 1;
return v___x_699_;
}
else
{
uint8_t v___x_700_; 
v___x_700_ = 0;
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_x1_701_, lean_object* v_x2_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x1_701_, v_x2_702_);
lean_dec_ref(v_x2_702_);
lean_dec_ref(v_x1_701_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_x_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_x_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x_707_);
lean_dec_ref(v_x_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_));
v___x_737_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(lean_object* v_n_740_, lean_object* v_as_741_, lean_object* v_lo_742_, lean_object* v_hi_743_, lean_object* v_w_744_, lean_object* v_hlo_745_, lean_object* v_hhi_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_740_, v_as_741_, v_lo_742_, v_hi_743_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___boxed(lean_object* v_n_748_, lean_object* v_as_749_, lean_object* v_lo_750_, lean_object* v_hi_751_, lean_object* v_w_752_, lean_object* v_hlo_753_, lean_object* v_hhi_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(v_n_748_, v_as_749_, v_lo_750_, v_hi_751_, v_w_752_, v_hlo_753_, v_hhi_754_);
lean_dec(v_hi_751_);
lean_dec(v_n_748_);
return v_res_755_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_757_, v_x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(v_00_u03b2_760_, v_x_761_, v_x_762_);
lean_dec(v_x_762_);
lean_dec_ref(v_x_761_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_n_765_, lean_object* v_lo_766_, lean_object* v_hi_767_, lean_object* v_hhi_768_, lean_object* v_pivot_769_, lean_object* v_as_770_, lean_object* v_i_771_, lean_object* v_k_772_, lean_object* v_ilo_773_, lean_object* v_ik_774_, lean_object* v_w_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_767_, v_pivot_769_, v_as_770_, v_i_771_, v_k_772_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_n_777_, lean_object* v_lo_778_, lean_object* v_hi_779_, lean_object* v_hhi_780_, lean_object* v_pivot_781_, lean_object* v_as_782_, lean_object* v_i_783_, lean_object* v_k_784_, lean_object* v_ilo_785_, lean_object* v_ik_786_, lean_object* v_w_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(v_n_777_, v_lo_778_, v_hi_779_, v_hhi_780_, v_pivot_781_, v_as_782_, v_i_783_, v_k_784_, v_ilo_785_, v_ik_786_, v_w_787_);
lean_dec_ref(v_pivot_781_);
lean_dec(v_hi_779_);
lean_dec(v_lo_778_);
lean_dec(v_n_777_);
return v_res_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_789_, lean_object* v_x_790_, size_t v_x_791_, lean_object* v_x_792_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_790_, v_x_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
size_t v_x_644__boxed_798_; uint8_t v_res_799_; lean_object* v_r_800_; 
v_x_644__boxed_798_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_res_799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_794_, v_x_795_, v_x_644__boxed_798_, v_x_797_);
lean_dec(v_x_797_);
lean_dec_ref(v_x_795_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03b2_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_heq_804_, lean_object* v_i_805_, lean_object* v_k_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_802_, v_i_805_, v_k_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_808_, lean_object* v_keys_809_, lean_object* v_vals_810_, lean_object* v_heq_811_, lean_object* v_i_812_, lean_object* v_k_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03b2_808_, v_keys_809_, v_vals_810_, v_heq_811_, v_i_812_, v_k_813_);
lean_dec(v_k_813_);
lean_dec_ref(v_vals_810_);
lean_dec_ref(v_keys_809_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(lean_object* v_env_816_, lean_object* v_type_817_){
_start:
{
if (lean_obj_tag(v_type_817_) == 7)
{
lean_object* v_body_818_; 
v_body_818_ = lean_ctor_get(v_type_817_, 2);
v_type_817_ = v_body_818_;
goto _start;
}
else
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Expr_getAppFn(v_type_817_);
if (lean_obj_tag(v___x_820_) == 4)
{
lean_object* v_declName_821_; uint8_t v___x_822_; 
v_declName_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_declName_821_);
lean_dec_ref_known(v___x_820_, 2);
v___x_822_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_816_, v_declName_821_);
return v___x_822_;
}
else
{
uint8_t v___x_823_; 
lean_dec_ref(v___x_820_);
lean_dec_ref(v_env_816_);
v___x_823_ = 0;
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType___boxed(lean_object* v_env_824_, lean_object* v_type_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_824_, v_type_825_);
lean_dec_ref(v_type_825_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(lean_object* v_env_828_, lean_object* v_type_829_){
_start:
{
if (lean_obj_tag(v_type_829_) == 7)
{
lean_object* v_body_830_; 
v_body_830_ = lean_ctor_get(v_type_829_, 2);
v_type_829_ = v_body_830_;
goto _start;
}
else
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Expr_getAppFn(v_type_829_);
if (lean_obj_tag(v___x_832_) == 4)
{
lean_object* v_declName_833_; uint8_t v___x_834_; 
v_declName_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_declName_833_);
lean_dec_ref_known(v___x_832_, 2);
v___x_834_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_828_, v_declName_833_);
return v___x_834_;
}
else
{
uint8_t v___x_835_; 
lean_dec_ref(v___x_832_);
lean_dec_ref(v_env_828_);
v___x_835_ = 0;
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType___boxed(lean_object* v_env_836_, lean_object* v_type_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_836_, v_type_837_);
lean_dec_ref(v_type_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(lean_object* v___x_843_, lean_object* v_param_844_, lean_object* v_paramsInfo_845_, lean_object* v_upperBound_846_, lean_object* v_a_847_, lean_object* v_b_848_){
_start:
{
lean_object* v_a_850_; uint8_t v___x_854_; 
v___x_854_ = lean_nat_dec_lt(v_a_847_, v_upperBound_846_);
if (v___x_854_ == 0)
{
lean_dec(v_a_847_);
lean_inc_ref(v_b_848_);
return v_b_848_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_865_; lean_object* v___x_868_; 
v___x_855_ = lean_box(0);
v___x_856_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0));
v___x_865_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default));
v___x_868_ = lean_array_get_borrowed(v___x_865_, v_paramsInfo_845_, v_a_847_);
switch(lean_obj_tag(v___x_868_))
{
case 0:
{
uint8_t v_weak_869_; 
v_weak_869_ = lean_ctor_get_uint8(v___x_868_, 0);
if (v_weak_869_ == 0)
{
goto v___jp_857_;
}
else
{
goto v___jp_866_;
}
}
case 2:
{
goto v___jp_866_;
}
case 4:
{
goto v___jp_866_;
}
default: 
{
goto v___jp_857_;
}
}
v___jp_857_:
{
lean_object* v___x_858_; lean_object* v_type_859_; lean_object* v_fvarId_860_; uint8_t v___x_861_; 
v___x_858_ = lean_array_fget_borrowed(v___x_843_, v_a_847_);
v_type_859_ = lean_ctor_get(v___x_858_, 2);
v_fvarId_860_ = lean_ctor_get(v_param_844_, 0);
v___x_861_ = l_Lean_Expr_containsFVar(v_type_859_, v_fvarId_860_);
if (v___x_861_ == 0)
{
v_a_850_ = v___x_856_;
goto v___jp_849_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_a_847_);
v___x_862_ = lean_box(v___x_861_);
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_855_);
return v___x_864_;
}
}
v___jp_866_:
{
lean_object* v___x_867_; 
v___x_867_ = lean_array_get_borrowed(v___x_865_, v_paramsInfo_845_, v_a_847_);
if (lean_obj_tag(v___x_867_) == 0)
{
goto v___jp_857_;
}
else
{
v_a_850_ = v___x_856_;
goto v___jp_849_;
}
}
}
v___jp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_add(v_a_847_, v___x_851_);
lean_dec(v_a_847_);
v_a_847_ = v___x_852_;
v_b_848_ = v_a_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___boxed(lean_object* v___x_870_, lean_object* v_param_871_, lean_object* v_paramsInfo_872_, lean_object* v_upperBound_873_, lean_object* v_a_874_, lean_object* v_b_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_870_, v_param_871_, v_paramsInfo_872_, v_upperBound_873_, v_a_874_, v_b_875_);
lean_dec_ref(v_b_875_);
lean_dec(v_upperBound_873_);
lean_dec_ref(v_paramsInfo_872_);
lean_dec_ref(v_param_871_);
lean_dec_ref(v___x_870_);
return v_res_876_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0(void){
_start:
{
uint8_t v___x_877_; lean_object* v___x_878_; 
v___x_877_ = 0;
v___x_878_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(lean_object* v_decl_879_, lean_object* v_paramsInfo_880_, lean_object* v_j_881_){
_start:
{
lean_object* v_toSignature_882_; lean_object* v_params_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_param_889_; lean_object* v___x_890_; lean_object* v_fst_891_; 
v_toSignature_882_ = lean_ctor_get(v_decl_879_, 0);
v_params_883_ = lean_ctor_get(v_toSignature_882_, 3);
v___x_884_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0, &l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0);
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_nat_add(v_j_881_, v___x_885_);
v___x_887_ = lean_array_get_size(v_params_883_);
v___x_888_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0));
v_param_889_ = lean_array_get_borrowed(v___x_884_, v_params_883_, v_j_881_);
v___x_890_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v_params_883_, v_param_889_, v_paramsInfo_880_, v___x_887_, v___x_886_, v___x_888_);
v_fst_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_fst_891_);
lean_dec_ref(v___x_890_);
if (lean_obj_tag(v_fst_891_) == 0)
{
uint8_t v___x_892_; 
v___x_892_ = 0;
return v___x_892_;
}
else
{
lean_object* v_val_893_; uint8_t v___x_894_; 
v_val_893_ = lean_ctor_get(v_fst_891_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_fst_891_, 1);
v___x_894_ = lean_unbox(v_val_893_);
lean_dec(v_val_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___boxed(lean_object* v_decl_895_, lean_object* v_paramsInfo_896_, lean_object* v_j_897_){
_start:
{
uint8_t v_res_898_; lean_object* v_r_899_; 
v_res_898_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v_decl_895_, v_paramsInfo_896_, v_j_897_);
lean_dec(v_j_897_);
lean_dec_ref(v_paramsInfo_896_);
lean_dec_ref(v_decl_895_);
v_r_899_ = lean_box(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(lean_object* v___x_900_, lean_object* v_param_901_, lean_object* v_paramsInfo_902_, lean_object* v_upperBound_903_, lean_object* v_inst_904_, lean_object* v_R_905_, lean_object* v_a_906_, lean_object* v_b_907_, lean_object* v_c_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_900_, v_param_901_, v_paramsInfo_902_, v_upperBound_903_, v_a_906_, v_b_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___boxed(lean_object* v___x_910_, lean_object* v_param_911_, lean_object* v_paramsInfo_912_, lean_object* v_upperBound_913_, lean_object* v_inst_914_, lean_object* v_R_915_, lean_object* v_a_916_, lean_object* v_b_917_, lean_object* v_c_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(v___x_910_, v_param_911_, v_paramsInfo_912_, v_upperBound_913_, v_inst_914_, v_R_915_, v_a_916_, v_b_917_, v_c_918_);
lean_dec_ref(v_b_917_);
lean_dec(v_upperBound_913_);
lean_dec_ref(v_paramsInfo_912_);
lean_dec_ref(v_param_911_);
lean_dec_ref(v___x_910_);
return v_res_919_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0(void){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_instMonadEIO(lean_box(0));
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(lean_object* v_msg_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_toApplicative_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_964_; 
v___x_929_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0, &l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0);
v___x_930_ = l_StateRefT_x27_instMonad___redArg(v___x_929_);
v_toApplicative_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___x_930_, 1);
lean_dec(v_unused_965_);
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_964_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_toApplicative_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_964_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_toFunctor_935_; lean_object* v_toSeq_936_; lean_object* v_toSeqLeft_937_; lean_object* v_toSeqRight_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_962_; 
v_toFunctor_935_ = lean_ctor_get(v_toApplicative_931_, 0);
v_toSeq_936_ = lean_ctor_get(v_toApplicative_931_, 2);
v_toSeqLeft_937_ = lean_ctor_get(v_toApplicative_931_, 3);
v_toSeqRight_938_ = lean_ctor_get(v_toApplicative_931_, 4);
v_isSharedCheck_962_ = !lean_is_exclusive(v_toApplicative_931_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_toApplicative_931_, 1);
lean_dec(v_unused_963_);
v___x_940_ = v_toApplicative_931_;
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_toSeqRight_938_);
lean_inc(v_toSeqLeft_937_);
lean_inc(v_toSeq_936_);
lean_inc(v_toFunctor_935_);
lean_dec(v_toApplicative_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___f_942_; lean_object* v___f_943_; lean_object* v___f_944_; lean_object* v___f_945_; lean_object* v___x_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___f_949_; lean_object* v___x_951_; 
v___f_942_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1));
v___f_943_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2));
lean_inc_ref(v_toFunctor_935_);
v___f_944_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_944_, 0, v_toFunctor_935_);
v___f_945_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_945_, 0, v_toFunctor_935_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___f_944_);
lean_ctor_set(v___x_946_, 1, v___f_945_);
v___f_947_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_947_, 0, v_toSeqRight_938_);
v___f_948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_948_, 0, v_toSeqLeft_937_);
v___f_949_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_949_, 0, v_toSeq_936_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v___f_947_);
lean_ctor_set(v___x_940_, 3, v___f_948_);
lean_ctor_set(v___x_940_, 2, v___f_949_);
lean_ctor_set(v___x_940_, 1, v___f_942_);
lean_ctor_set(v___x_940_, 0, v___x_946_);
v___x_951_ = v___x_940_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___f_942_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v___f_949_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v___f_948_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v___f_947_);
v___x_951_ = v_reuseFailAlloc_961_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_953_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___f_943_);
lean_ctor_set(v___x_933_, 0, v___x_951_);
v___x_953_ = v___x_933_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___f_943_);
v___x_953_ = v_reuseFailAlloc_960_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___x_11117__overap_958_; lean_object* v___x_959_; 
v___x_954_ = l_StateRefT_x27_instMonad___redArg(v___x_953_);
v___x_955_ = lean_box(0);
v___x_956_ = l_instInhabitedOfMonad___redArg(v___x_954_, v___x_955_);
v___f_957_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_957_, 0, v___x_956_);
v___x_11117__overap_958_ = lean_panic_fn_borrowed(v___f_957_, v_msg_923_);
lean_dec_ref(v___f_957_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_959_ = lean_apply_5(v___x_11117__overap_958_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___boxed(lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(lean_object* v_a_973_, lean_object* v_as_974_, size_t v_i_975_, size_t v_stop_976_){
_start:
{
uint8_t v___x_977_; 
v___x_977_ = lean_usize_dec_eq(v_i_975_, v_stop_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = lean_array_uget_borrowed(v_as_974_, v_i_975_);
v___x_979_ = lean_nat_dec_eq(v_a_973_, v___x_978_);
if (v___x_979_ == 0)
{
size_t v___x_980_; size_t v___x_981_; 
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_add(v_i_975_, v___x_980_);
v_i_975_ = v___x_981_;
goto _start;
}
else
{
return v___x_979_;
}
}
else
{
uint8_t v___x_983_; 
v___x_983_ = 0;
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0___boxed(lean_object* v_a_984_, lean_object* v_as_985_, lean_object* v_i_986_, lean_object* v_stop_987_){
_start:
{
size_t v_i_boxed_988_; size_t v_stop_boxed_989_; uint8_t v_res_990_; lean_object* v_r_991_; 
v_i_boxed_988_ = lean_unbox_usize(v_i_986_);
lean_dec(v_i_986_);
v_stop_boxed_989_ = lean_unbox_usize(v_stop_987_);
lean_dec(v_stop_987_);
v_res_990_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(v_a_984_, v_as_985_, v_i_boxed_988_, v_stop_boxed_989_);
lean_dec_ref(v_as_985_);
lean_dec(v_a_984_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(lean_object* v_as_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_array_get_size(v_as_992_);
v___x_996_ = lean_nat_dec_lt(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
return v___x_996_;
}
else
{
if (v___x_996_ == 0)
{
return v___x_996_;
}
else
{
size_t v___x_997_; size_t v___x_998_; uint8_t v___x_999_; 
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_of_nat(v___x_995_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(v_a_993_, v_as_992_, v___x_997_, v___x_998_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0___boxed(lean_object* v_as_1000_, lean_object* v_a_1001_){
_start:
{
uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_res_1002_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_as_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_as_1000_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(lean_object* v_b_1004_, lean_object* v_info_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_array_push(v_b_1004_, v_info_1005_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0___boxed(lean_object* v_b_1014_, lean_object* v_info_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_1014_, v_info_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(lean_object* v_upperBound_1024_, lean_object* v___x_1025_, lean_object* v_autoSpecialize_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v_a_1029_, lean_object* v_b_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___y_1037_; uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_lt(v_a_1029_, v_upperBound_1024_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_dec(v_a_1029_);
lean_dec(v___x_1028_);
lean_dec(v___x_1027_);
lean_dec_ref(v_autoSpecialize_1026_);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_b_1030_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_type_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_st_ref_get(v___y_1034_);
v___x_1062_ = lean_array_fget_borrowed(v___x_1025_, v_a_1029_);
v_type_1063_ = lean_ctor_get(v___x_1062_, 2);
lean_inc_ref(v_type_1063_);
v___x_1064_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_1063_, v___y_1034_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v_env_1066_; uint8_t v___y_1077_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v_env_1066_ = lean_ctor_get(v___x_1061_, 0);
lean_inc_ref(v_env_1066_);
lean_dec(v___x_1061_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0));
v___x_1091_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v___x_1090_, v_a_1029_);
v___y_1077_ = v___x_1091_;
goto v___jp_1076_;
}
else
{
lean_object* v_val_1092_; uint8_t v___x_1093_; 
v_val_1092_ = lean_ctor_get(v___x_1028_, 0);
v___x_1093_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_val_1092_, v_a_1029_);
v___y_1077_ = v___x_1093_;
goto v___jp_1076_;
}
v___jp_1067_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_box(4);
v___x_1069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_1030_, v___x_1068_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
v___y_1037_ = v___x_1069_;
goto v___jp_1036_;
}
v___jp_1070_:
{
lean_object* v___x_1071_; lean_object* v_env_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1071_ = lean_st_ref_get(v___y_1034_);
v_env_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc_ref(v_env_1072_);
lean_dec(v___x_1071_);
v___x_1073_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_1072_, v_type_1063_);
v___x_1074_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1074_, 0, v___x_1073_);
v___x_1075_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_1030_, v___x_1074_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
v___y_1037_ = v___x_1075_;
goto v___jp_1036_;
}
v___jp_1076_:
{
if (v___y_1077_ == 0)
{
uint8_t v___x_1078_; 
v___x_1078_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_1066_, v_type_1063_);
if (v___x_1078_ == 0)
{
uint8_t v___x_1079_; 
lean_inc_ref(v_type_1063_);
v___x_1079_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_1063_);
if (v___x_1079_ == 0)
{
if (lean_obj_tag(v_a_1065_) == 0)
{
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
lean_inc_ref(v_autoSpecialize_1026_);
lean_inc(v___x_1028_);
lean_inc(v___x_1027_);
v___x_1080_ = lean_apply_2(v_autoSpecialize_1026_, v___x_1027_, v___x_1028_);
v___x_1081_ = lean_unbox(v___x_1080_);
if (v___x_1081_ == 0)
{
goto v___jp_1067_;
}
else
{
if (lean_obj_tag(v_type_1063_) == 7)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_box(1);
v___x_1083_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_1030_, v___x_1082_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
v___y_1037_ = v___x_1083_;
goto v___jp_1036_;
}
else
{
goto v___jp_1067_;
}
}
}
else
{
goto v___jp_1070_;
}
}
else
{
lean_dec_ref_known(v_a_1065_, 1);
goto v___jp_1070_;
}
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v_a_1065_);
v___x_1084_ = lean_box(2);
v___x_1085_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_1030_, v___x_1084_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
v___y_1037_ = v___x_1085_;
goto v___jp_1036_;
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v_a_1065_);
v___x_1086_ = lean_box(4);
v___x_1087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_1030_, v___x_1086_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
v___y_1037_ = v___x_1087_;
goto v___jp_1036_;
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v_env_1066_);
lean_dec(v_a_1065_);
v___x_1088_ = lean_box(3);
v___x_1089_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_1030_, v___x_1088_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
v___y_1037_ = v___x_1089_;
goto v___jp_1036_;
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v___x_1061_);
lean_dec_ref(v_b_1030_);
lean_dec(v_a_1029_);
lean_dec(v___x_1028_);
lean_dec(v___x_1027_);
lean_dec_ref(v_autoSpecialize_1026_);
v_a_1094_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1064_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1064_);
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
v___jp_1036_:
{
if (lean_obj_tag(v___y_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1050_; 
v_a_1038_ = lean_ctor_get(v___y_1037_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___y_1037_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1040_ = v___y_1037_;
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___y_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
if (lean_obj_tag(v_a_1038_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; 
lean_dec(v_a_1029_);
lean_dec(v___x_1028_);
lean_dec(v___x_1027_);
lean_dec_ref(v_autoSpecialize_1026_);
v_a_1042_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v_a_1038_, 1);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_a_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_del_object(v___x_1040_);
v_a_1046_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v_a_1038_, 1);
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = lean_nat_add(v_a_1029_, v___x_1047_);
lean_dec(v_a_1029_);
v_a_1029_ = v___x_1048_;
v_b_1030_ = v_a_1046_;
goto _start;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1029_);
lean_dec(v___x_1028_);
lean_dec(v___x_1027_);
lean_dec_ref(v_autoSpecialize_1026_);
v_a_1051_ = lean_ctor_get(v___y_1037_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___y_1037_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___y_1037_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___y_1037_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___boxed(lean_object* v_upperBound_1102_, lean_object* v___x_1103_, lean_object* v_autoSpecialize_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v_a_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v_upperBound_1102_, v___x_1103_, v_autoSpecialize_1104_, v___x_1105_, v___x_1106_, v_a_1107_, v_b_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___x_1103_);
lean_dec(v_upperBound_1102_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(lean_object* v_autoSpecialize_1115_, lean_object* v_as_1116_, size_t v_sz_1117_, size_t v_i_1118_, lean_object* v_b_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_a_1126_; uint8_t v___x_1130_; 
v___x_1130_ = lean_usize_dec_lt(v_i_1118_, v_sz_1117_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v_autoSpecialize_1115_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_b_1119_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v_env_1133_; lean_object* v_a_1134_; lean_object* v_toSignature_1135_; lean_object* v_name_1136_; lean_object* v_params_1137_; uint8_t v___x_1138_; 
v___x_1132_ = lean_st_ref_get(v___y_1123_);
v_env_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_env_1133_);
lean_dec(v___x_1132_);
v_a_1134_ = lean_array_uget_borrowed(v_as_1116_, v_i_1118_);
v_toSignature_1135_ = lean_ctor_get(v_a_1134_, 0);
v_name_1136_ = lean_ctor_get(v_toSignature_1135_, 0);
v_params_1137_ = lean_ctor_get(v_toSignature_1135_, 3);
lean_inc(v_name_1136_);
v___x_1138_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1133_, v_name_1136_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v_env_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1139_ = lean_st_ref_get(v___y_1123_);
v_env_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc_ref(v_env_1140_);
lean_dec(v___x_1139_);
v___x_1141_ = lean_array_get_size(v_params_1137_);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
lean_inc_n(v_name_1136_, 2);
v___x_1144_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_1140_, v_name_1136_);
lean_inc_ref(v_autoSpecialize_1115_);
v___x_1145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v___x_1141_, v_params_1137_, v_autoSpecialize_1115_, v_name_1136_, v___x_1144_, v___x_1142_, v___x_1143_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_array_push(v_b_1119_, v_a_1146_);
v_a_1126_ = v___x_1147_;
goto v___jp_1125_;
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec_ref(v_b_1119_);
lean_dec_ref(v_autoSpecialize_1115_);
v_a_1148_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1145_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1145_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = lean_array_get_size(v_params_1137_);
v___x_1157_ = lean_box(4);
v___x_1158_ = lean_mk_array(v___x_1156_, v___x_1157_);
v___x_1159_ = lean_array_push(v_b_1119_, v___x_1158_);
v_a_1126_ = v___x_1159_;
goto v___jp_1125_;
}
}
v___jp_1125_:
{
size_t v___x_1127_; size_t v___x_1128_; 
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_add(v_i_1118_, v___x_1127_);
v_i_1118_ = v___x_1128_;
v_b_1119_ = v_a_1126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3___boxed(lean_object* v_autoSpecialize_1160_, lean_object* v_as_1161_, lean_object* v_sz_1162_, lean_object* v_i_1163_, lean_object* v_b_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_sz_boxed_1170_; size_t v_i_boxed_1171_; lean_object* v_res_1172_; 
v_sz_boxed_1170_ = lean_unbox_usize(v_sz_1162_);
lean_dec(v_sz_1162_);
v_i_boxed_1171_ = lean_unbox_usize(v_i_1163_);
lean_dec(v_i_1163_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1160_, v_as_1161_, v_sz_boxed_1170_, v_i_boxed_1171_, v_b_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec_ref(v_as_1161_);
return v_res_1172_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(lean_object* v_as_1173_, size_t v_i_1174_, size_t v_stop_1175_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_eq(v_i_1174_, v_stop_1175_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; uint8_t v___y_1179_; lean_object* v___x_1183_; 
v___x_1177_ = 1;
v___x_1183_ = lean_array_uget_borrowed(v_as_1173_, v_i_1174_);
switch(lean_obj_tag(v___x_1183_))
{
case 0:
{
uint8_t v_weak_1184_; 
v_weak_1184_ = lean_ctor_get_uint8(v___x_1183_, 0);
if (v_weak_1184_ == 0)
{
return v___x_1177_;
}
else
{
v___y_1179_ = v___x_1176_;
goto v___jp_1178_;
}
}
case 2:
{
v___y_1179_ = v___x_1176_;
goto v___jp_1178_;
}
case 4:
{
v___y_1179_ = v___x_1176_;
goto v___jp_1178_;
}
default: 
{
return v___x_1177_;
}
}
v___jp_1178_:
{
if (v___y_1179_ == 0)
{
size_t v___x_1180_; size_t v___x_1181_; 
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_add(v_i_1174_, v___x_1180_);
v_i_1174_ = v___x_1181_;
goto _start;
}
else
{
return v___x_1177_;
}
}
}
else
{
uint8_t v___x_1185_; 
v___x_1185_ = 0;
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___boxed(lean_object* v_as_1186_, lean_object* v_i_1187_, lean_object* v_stop_1188_){
_start:
{
size_t v_i_boxed_1189_; size_t v_stop_boxed_1190_; uint8_t v_res_1191_; lean_object* v_r_1192_; 
v_i_boxed_1189_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_stop_boxed_1190_ = lean_unbox_usize(v_stop_1188_);
lean_dec(v_stop_1188_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_as_1186_, v_i_boxed_1189_, v_stop_boxed_1190_);
lean_dec_ref(v_as_1186_);
v_r_1192_ = lean_box(v_res_1191_);
return v_r_1192_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(lean_object* v_as_1193_, size_t v_i_1194_, size_t v_stop_1195_){
_start:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_usize_dec_eq(v_i_1194_, v_stop_1195_);
if (v___x_1196_ == 0)
{
uint8_t v___x_1197_; uint8_t v___y_1199_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1197_ = 1;
v___x_1203_ = lean_array_uget_borrowed(v_as_1193_, v_i_1194_);
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_array_get_size(v___x_1203_);
v___x_1206_ = lean_nat_dec_lt(v___x_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
v___y_1199_ = v___x_1196_;
goto v___jp_1198_;
}
else
{
if (v___x_1206_ == 0)
{
v___y_1199_ = v___x_1196_;
goto v___jp_1198_;
}
else
{
size_t v___x_1207_; size_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1207_ = ((size_t)0ULL);
v___x_1208_ = lean_usize_of_nat(v___x_1205_);
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v___x_1203_, v___x_1207_, v___x_1208_);
v___y_1199_ = v___x_1209_;
goto v___jp_1198_;
}
}
v___jp_1198_:
{
if (v___y_1199_ == 0)
{
size_t v___x_1200_; size_t v___x_1201_; 
v___x_1200_ = ((size_t)1ULL);
v___x_1201_ = lean_usize_add(v_i_1194_, v___x_1200_);
v_i_1194_ = v___x_1201_;
goto _start;
}
else
{
return v___x_1197_;
}
}
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5___boxed(lean_object* v_as_1211_, lean_object* v_i_1212_, lean_object* v_stop_1213_){
_start:
{
size_t v_i_boxed_1214_; size_t v_stop_boxed_1215_; uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_i_boxed_1214_ = lean_unbox_usize(v_i_1212_);
lean_dec(v_i_1212_);
v_stop_boxed_1215_ = lean_unbox_usize(v_stop_1213_);
lean_dec(v_stop_1213_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_as_1211_, v_i_boxed_1214_, v_stop_boxed_1215_);
lean_dec_ref(v_as_1211_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(lean_object* v_as_1218_, lean_object* v_bs_1219_, lean_object* v_i_1220_, lean_object* v_cs_1221_){
_start:
{
lean_object* v___y_1223_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_array_get_size(v_as_1218_);
v___x_1229_ = lean_nat_dec_lt(v_i_1220_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec(v_i_1220_);
return v_cs_1221_;
}
else
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_array_get_size(v_bs_1219_);
v___x_1231_ = lean_nat_dec_lt(v_i_1220_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_i_1220_);
return v_cs_1221_;
}
else
{
lean_object* v_a_1232_; lean_object* v_b_1233_; uint8_t v___x_1234_; 
v_a_1232_ = lean_array_fget_borrowed(v_as_1218_, v_i_1220_);
v_b_1233_ = lean_array_fget_borrowed(v_bs_1219_, v_i_1220_);
v___x_1234_ = lean_unbox(v_b_1233_);
if (v___x_1234_ == 0)
{
if (lean_obj_tag(v_a_1232_) == 3)
{
v___y_1223_ = v_a_1232_;
goto v___jp_1222_;
}
else
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_box(4);
v___y_1223_ = v___x_1235_;
goto v___jp_1222_;
}
}
else
{
lean_inc(v_a_1232_);
v___y_1223_ = v_a_1232_;
goto v___jp_1222_;
}
}
}
v___jp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_add(v_i_1220_, v___x_1224_);
lean_dec(v_i_1220_);
v___x_1226_ = lean_array_push(v_cs_1221_, v___y_1223_);
v_i_1220_ = v___x_1225_;
v_cs_1221_ = v___x_1226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6___boxed(lean_object* v_as_1236_, lean_object* v_bs_1237_, lean_object* v_i_1238_, lean_object* v_cs_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v_as_1236_, v_bs_1237_, v_i_1238_, v_cs_1239_);
lean_dec_ref(v_bs_1237_);
lean_dec_ref(v_as_1236_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(lean_object* v_upperBound_1241_, lean_object* v___x_1242_, lean_object* v_a_1243_, lean_object* v_b_1244_){
_start:
{
lean_object* v_a_1247_; uint8_t v___x_1251_; 
v___x_1251_ = lean_nat_dec_lt(v_a_1243_, v_upperBound_1241_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec(v_a_1243_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_b_1244_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default));
v___x_1254_ = lean_array_get_borrowed(v___x_1253_, v_b_1244_, v_a_1243_);
if (lean_obj_tag(v___x_1254_) == 2)
{
uint8_t v___x_1255_; 
v___x_1255_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v___x_1242_, v_b_1244_, v_a_1243_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_box(4);
v___x_1257_ = lean_array_set(v_b_1244_, v_a_1243_, v___x_1256_);
v_a_1247_ = v___x_1257_;
goto v___jp_1246_;
}
else
{
v_a_1247_ = v_b_1244_;
goto v___jp_1246_;
}
}
else
{
v_a_1247_ = v_b_1244_;
goto v___jp_1246_;
}
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v_a_1243_, v___x_1248_);
lean_dec(v_a_1243_);
v_a_1243_ = v___x_1249_;
v_b_1244_ = v_a_1247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg___boxed(lean_object* v_upperBound_1258_, lean_object* v___x_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1258_, v___x_1259_, v_a_1260_, v_b_1261_);
lean_dec_ref(v___x_1259_);
lean_dec(v_upperBound_1258_);
return v_res_1263_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Array_instInhabited(lean_box(0));
return v___x_1264_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1268_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3));
v___x_1269_ = lean_unsigned_to_nat(43u);
v___x_1270_ = lean_unsigned_to_nat(236u);
v___x_1271_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2));
v___x_1272_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1));
v___x_1273_ = l_mkPanicMessageWithDecl(v___x_1272_, v___x_1271_, v___x_1270_, v___x_1269_, v___x_1268_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(lean_object* v_upperBound_1274_, lean_object* v_decls_1275_, lean_object* v_alreadySpecialized_1276_, lean_object* v___x_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_a_1287_; uint8_t v___x_1291_; 
v___x_1291_ = lean_nat_dec_lt(v_a_1279_, v_upperBound_1274_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_dec(v_a_1279_);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v_b_1280_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; lean_object* v_toSignature_1294_; lean_object* v_name_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_array_fget_borrowed(v_decls_1275_, v_a_1279_);
v_toSignature_1294_ = lean_ctor_get(v___x_1293_, 0);
v_name_1295_ = lean_ctor_get(v_toSignature_1294_, 0);
v___x_1296_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1277_, v_name_1295_);
if (lean_obj_tag(v___x_1296_) == 1)
{
lean_object* v_val_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_val_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0);
v___x_1299_ = lean_array_get_borrowed(v___x_1298_, v_a_1278_, v_a_1279_);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1302_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v___x_1299_, v_val_1297_, v___x_1300_, v___x_1301_);
lean_dec(v_val_1297_);
v___x_1303_ = lean_array_get_size(v___x_1302_);
v___x_1304_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v___x_1303_, v___x_1293_, v___x_1300_, v___x_1302_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = 0;
v___x_1307_ = lean_box(v___x_1306_);
v___x_1308_ = lean_array_get(v___x_1307_, v_alreadySpecialized_1276_, v_a_1279_);
lean_dec(v___x_1307_);
lean_inc(v_name_1295_);
v___x_1309_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1309_, 0, v_name_1295_);
lean_ctor_set(v___x_1309_, 1, v_a_1305_);
v___x_1310_ = lean_unbox(v___x_1308_);
lean_dec(v___x_1308_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*2, v___x_1310_);
v___x_1311_ = lean_array_push(v_b_1280_, v___x_1309_);
v_a_1287_ = v___x_1311_;
goto v___jp_1286_;
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v_b_1280_);
lean_dec(v_a_1279_);
v_a_1312_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1304_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1304_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec(v___x_1296_);
v___x_1320_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4);
v___x_1321_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v___x_1320_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_dec_ref_known(v___x_1321_, 1);
v_a_1287_ = v_b_1280_;
goto v___jp_1286_;
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v_b_1280_);
lean_dec(v_a_1279_);
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
v___jp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_add(v_a_1279_, v___x_1288_);
lean_dec(v_a_1279_);
v_a_1279_ = v___x_1289_;
v_b_1280_ = v_a_1287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___boxed(lean_object* v_upperBound_1330_, lean_object* v_decls_1331_, lean_object* v_alreadySpecialized_1332_, lean_object* v___x_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1330_, v_decls_1331_, v_alreadySpecialized_1332_, v___x_1333_, v_a_1334_, v_a_1335_, v_b_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v_a_1334_);
lean_dec(v___x_1333_);
lean_dec_ref(v_alreadySpecialized_1332_);
lean_dec_ref(v_decls_1331_);
lean_dec(v_upperBound_1330_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(lean_object* v_alreadySpecialized_1343_, lean_object* v_as_1344_, lean_object* v_i_1345_, lean_object* v_j_1346_, lean_object* v_bs_1347_){
_start:
{
lean_object* v_zero_1348_; uint8_t v_isZero_1349_; 
v_zero_1348_ = lean_unsigned_to_nat(0u);
v_isZero_1349_ = lean_nat_dec_eq(v_i_1345_, v_zero_1348_);
if (v_isZero_1349_ == 1)
{
lean_dec(v_j_1346_);
lean_dec(v_i_1345_);
return v_bs_1347_;
}
else
{
lean_object* v___x_1350_; lean_object* v_toSignature_1351_; lean_object* v_name_1352_; lean_object* v_params_1353_; lean_object* v_one_1354_; lean_object* v_n_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1350_ = lean_array_fget_borrowed(v_as_1344_, v_j_1346_);
v_toSignature_1351_ = lean_ctor_get(v___x_1350_, 0);
v_name_1352_ = lean_ctor_get(v_toSignature_1351_, 0);
v_params_1353_ = lean_ctor_get(v_toSignature_1351_, 3);
v_one_1354_ = lean_unsigned_to_nat(1u);
v_n_1355_ = lean_nat_sub(v_i_1345_, v_one_1354_);
lean_dec(v_i_1345_);
v___x_1356_ = lean_array_get_size(v_params_1353_);
v___x_1357_ = lean_box(4);
v___x_1358_ = lean_mk_array(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_box(v_isZero_1349_);
v___x_1360_ = lean_array_get(v___x_1359_, v_alreadySpecialized_1343_, v_j_1346_);
lean_dec(v___x_1359_);
lean_inc(v_name_1352_);
v___x_1361_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1361_, 0, v_name_1352_);
lean_ctor_set(v___x_1361_, 1, v___x_1358_);
v___x_1362_ = lean_unbox(v___x_1360_);
lean_dec(v___x_1360_);
lean_ctor_set_uint8(v___x_1361_, sizeof(void*)*2, v___x_1362_);
v___x_1363_ = lean_nat_add(v_j_1346_, v_one_1354_);
lean_dec(v_j_1346_);
v___x_1364_ = lean_array_push(v_bs_1347_, v___x_1361_);
v_i_1345_ = v_n_1355_;
v_j_1346_ = v___x_1363_;
v_bs_1347_ = v___x_1364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg___boxed(lean_object* v_alreadySpecialized_1366_, lean_object* v_as_1367_, lean_object* v_i_1368_, lean_object* v_j_1369_, lean_object* v_bs_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1366_, v_as_1367_, v_i_1368_, v_j_1369_, v_bs_1370_);
lean_dec_ref(v_as_1367_);
lean_dec_ref(v_alreadySpecialized_1366_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries(lean_object* v_decls_1374_, lean_object* v_autoSpecialize_1375_, lean_object* v_alreadySpecialized_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v_declsInfo_1383_; size_t v_sz_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v_declsInfo_1383_ = ((lean_object*)(l_Lean_Compiler_LCNF_computeSpecEntries___closed__0));
v_sz_1384_ = lean_array_size(v_decls_1374_);
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1375_, v_decls_1374_, v_sz_1384_, v___x_1385_, v_declsInfo_1383_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1406_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1406_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1406_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = lean_array_get_size(v_a_1387_);
v___x_1399_ = lean_nat_dec_lt(v___x_1382_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_dec(v_a_1387_);
goto v___jp_1391_;
}
else
{
if (v___x_1399_ == 0)
{
lean_dec(v_a_1387_);
goto v___jp_1391_;
}
else
{
size_t v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = lean_usize_of_nat(v___x_1398_);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_a_1387_, v___x_1385_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_dec(v_a_1387_);
goto v___jp_1391_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_del_object(v___x_1389_);
v___x_1402_ = lean_array_get_size(v_decls_1374_);
v___x_1403_ = lean_mk_empty_array_with_capacity(v___x_1402_);
lean_inc_ref(v_decls_1374_);
v___x_1404_ = l_Lean_Compiler_LCNF_mkFixedParamsMap(v_decls_1374_);
v___x_1405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v___x_1402_, v_decls_1374_, v_alreadySpecialized_1376_, v___x_1404_, v_a_1387_, v___x_1382_, v___x_1403_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1387_);
lean_dec(v___x_1404_);
lean_dec_ref(v_decls_1374_);
return v___x_1405_;
}
}
}
v___jp_1391_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1392_ = lean_array_get_size(v_decls_1374_);
v___x_1393_ = lean_mk_empty_array_with_capacity(v___x_1392_);
v___x_1394_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1376_, v_decls_1374_, v___x_1392_, v___x_1382_, v___x_1393_);
lean_dec_ref(v_decls_1374_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1394_);
v___x_1396_ = v___x_1389_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v_decls_1374_);
v_a_1407_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1386_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1386_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries___boxed(lean_object* v_decls_1415_, lean_object* v_autoSpecialize_1416_, lean_object* v_alreadySpecialized_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1415_, v_autoSpecialize_1416_, v_alreadySpecialized_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec_ref(v_alreadySpecialized_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(lean_object* v_upperBound_1424_, lean_object* v___x_1425_, lean_object* v_autoSpecialize_1426_, lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v_inst_1429_, lean_object* v_R_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_, lean_object* v_c_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v_upperBound_1424_, v___x_1425_, v_autoSpecialize_1426_, v___x_1427_, v___x_1428_, v_a_1431_, v_b_1432_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___boxed(lean_object* v_upperBound_1440_, lean_object* v___x_1441_, lean_object* v_autoSpecialize_1442_, lean_object* v___x_1443_, lean_object* v___x_1444_, lean_object* v_inst_1445_, lean_object* v_R_1446_, lean_object* v_a_1447_, lean_object* v_b_1448_, lean_object* v_c_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v_upperBound_1440_, v___x_1441_, v_autoSpecialize_1442_, v___x_1443_, v___x_1444_, v_inst_1445_, v_R_1446_, v_a_1447_, v_b_1448_, v_c_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v___x_1441_);
lean_dec(v_upperBound_1440_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(lean_object* v_alreadySpecialized_1456_, lean_object* v_as_1457_, lean_object* v_i_1458_, lean_object* v_j_1459_, lean_object* v_inv_1460_, lean_object* v_bs_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1456_, v_as_1457_, v_i_1458_, v_j_1459_, v_bs_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___boxed(lean_object* v_alreadySpecialized_1463_, lean_object* v_as_1464_, lean_object* v_i_1465_, lean_object* v_j_1466_, lean_object* v_inv_1467_, lean_object* v_bs_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(v_alreadySpecialized_1463_, v_as_1464_, v_i_1465_, v_j_1466_, v_inv_1467_, v_bs_1468_);
lean_dec_ref(v_as_1464_);
lean_dec_ref(v_alreadySpecialized_1463_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(lean_object* v_upperBound_1470_, lean_object* v___x_1471_, lean_object* v_inst_1472_, lean_object* v_R_1473_, lean_object* v_a_1474_, lean_object* v_b_1475_, lean_object* v_c_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1470_, v___x_1471_, v_a_1474_, v_b_1475_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___boxed(lean_object* v_upperBound_1483_, lean_object* v___x_1484_, lean_object* v_inst_1485_, lean_object* v_R_1486_, lean_object* v_a_1487_, lean_object* v_b_1488_, lean_object* v_c_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(v_upperBound_1483_, v___x_1484_, v_inst_1485_, v_R_1486_, v_a_1487_, v_b_1488_, v_c_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec_ref(v___x_1484_);
lean_dec(v_upperBound_1483_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(lean_object* v_upperBound_1496_, lean_object* v_decls_1497_, lean_object* v_alreadySpecialized_1498_, lean_object* v___x_1499_, lean_object* v_a_1500_, lean_object* v_inst_1501_, lean_object* v_R_1502_, lean_object* v_a_1503_, lean_object* v_b_1504_, lean_object* v_c_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1496_, v_decls_1497_, v_alreadySpecialized_1498_, v___x_1499_, v_a_1500_, v_a_1503_, v_b_1504_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___boxed(lean_object* v_upperBound_1512_, lean_object* v_decls_1513_, lean_object* v_alreadySpecialized_1514_, lean_object* v___x_1515_, lean_object* v_a_1516_, lean_object* v_inst_1517_, lean_object* v_R_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_, lean_object* v_c_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(v_upperBound_1512_, v_decls_1513_, v_alreadySpecialized_1514_, v___x_1515_, v_a_1516_, v_inst_1517_, v_R_1518_, v_a_1519_, v_b_1520_, v_c_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec_ref(v_a_1516_);
lean_dec(v___x_1515_);
lean_dec_ref(v_alreadySpecialized_1514_);
lean_dec_ref(v_decls_1513_);
lean_dec(v_upperBound_1512_);
return v_res_1527_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1);
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
lean_ctor_set(v___x_1533_, 2, v___x_1532_);
lean_ctor_set(v___x_1533_, 3, v___x_1532_);
lean_ctor_set(v___x_1533_, 4, v___x_1531_);
lean_ctor_set(v___x_1533_, 5, v___x_1531_);
lean_ctor_set(v___x_1533_, 6, v___x_1531_);
lean_ctor_set(v___x_1533_, 7, v___x_1531_);
lean_ctor_set(v___x_1533_, 8, v___x_1531_);
lean_ctor_set(v___x_1533_, 9, v___x_1531_);
return v___x_1533_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1534_; double v___x_1535_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_float_of_nat(v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(lean_object* v_cls_1539_, lean_object* v_msg_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_options_1546_; lean_object* v_ref_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_options_1546_ = lean_ctor_get(v___y_1543_, 2);
v_ref_1547_ = lean_ctor_get(v___y_1543_, 5);
v___x_1548_ = lean_st_ref_get(v___y_1544_);
v___x_1549_ = lean_st_ref_get(v___y_1542_);
v___x_1550_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1541_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1609_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1609_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1609_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_env_1555_; lean_object* v_lctx_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1607_; 
v_env_1555_ = lean_ctor_get(v___x_1548_, 0);
lean_inc_ref(v_env_1555_);
lean_dec(v___x_1548_);
v_lctx_1556_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1549_, 1);
lean_dec(v_unused_1608_);
v___x_1558_ = v___x_1549_;
v_isShared_1559_ = v_isSharedCheck_1607_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_lctx_1556_);
lean_dec(v___x_1549_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1607_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_traceState_1562_; lean_object* v_env_1563_; lean_object* v_nextMacroScope_1564_; lean_object* v_ngen_1565_; lean_object* v_auxDeclNGen_1566_; lean_object* v_cache_1567_; lean_object* v_messages_1568_; lean_object* v_infoState_1569_; lean_object* v_snapshotTasks_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1606_; 
v___x_1560_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2);
v___x_1561_ = lean_st_ref_take(v___y_1544_);
v_traceState_1562_ = lean_ctor_get(v___x_1561_, 4);
v_env_1563_ = lean_ctor_get(v___x_1561_, 0);
v_nextMacroScope_1564_ = lean_ctor_get(v___x_1561_, 1);
v_ngen_1565_ = lean_ctor_get(v___x_1561_, 2);
v_auxDeclNGen_1566_ = lean_ctor_get(v___x_1561_, 3);
v_cache_1567_ = lean_ctor_get(v___x_1561_, 5);
v_messages_1568_ = lean_ctor_get(v___x_1561_, 6);
v_infoState_1569_ = lean_ctor_get(v___x_1561_, 7);
v_snapshotTasks_1570_ = lean_ctor_get(v___x_1561_, 8);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1572_ = v___x_1561_;
v_isShared_1573_ = v_isSharedCheck_1606_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snapshotTasks_1570_);
lean_inc(v_infoState_1569_);
lean_inc(v_messages_1568_);
lean_inc(v_cache_1567_);
lean_inc(v_traceState_1562_);
lean_inc(v_auxDeclNGen_1566_);
lean_inc(v_ngen_1565_);
lean_inc(v_nextMacroScope_1564_);
lean_inc(v_env_1563_);
lean_dec(v___x_1561_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1606_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
uint64_t v_tid_1574_; lean_object* v_traces_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1605_; 
v_tid_1574_ = lean_ctor_get_uint64(v_traceState_1562_, sizeof(void*)*1);
v_traces_1575_ = lean_ctor_get(v_traceState_1562_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_traceState_1562_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1577_ = v_traceState_1562_;
v_isShared_1578_ = v_isSharedCheck_1605_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_traces_1575_);
lean_dec(v_traceState_1562_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1605_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1579_ = lean_unbox(v_a_1551_);
lean_dec(v_a_1551_);
v___x_1580_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1556_, v___x_1579_);
lean_dec_ref(v_lctx_1556_);
lean_inc_ref(v_options_1546_);
v___x_1581_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1581_, 0, v_env_1555_);
lean_ctor_set(v___x_1581_, 1, v___x_1560_);
lean_ctor_set(v___x_1581_, 2, v___x_1580_);
lean_ctor_set(v___x_1581_, 3, v_options_1546_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 3);
lean_ctor_set(v___x_1558_, 1, v_msg_1540_);
lean_ctor_set(v___x_1558_, 0, v___x_1581_);
v___x_1583_ = v___x_1558_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_msg_1540_);
v___x_1583_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; double v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3);
v___x_1586_ = 0;
v___x_1587_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4));
v___x_1588_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1588_, 0, v_cls_1539_);
lean_ctor_set(v___x_1588_, 1, v___x_1584_);
lean_ctor_set(v___x_1588_, 2, v___x_1587_);
lean_ctor_set_float(v___x_1588_, sizeof(void*)*3, v___x_1585_);
lean_ctor_set_float(v___x_1588_, sizeof(void*)*3 + 8, v___x_1585_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*3 + 16, v___x_1586_);
v___x_1589_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5));
v___x_1590_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1583_);
lean_ctor_set(v___x_1590_, 2, v___x_1589_);
lean_inc(v_ref_1547_);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v_ref_1547_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_PersistentArray_push___redArg(v_traces_1575_, v___x_1591_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1592_);
v___x_1594_ = v___x_1577_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1592_);
lean_ctor_set_uint64(v_reuseFailAlloc_1603_, sizeof(void*)*1, v_tid_1574_);
v___x_1594_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 4, v___x_1594_);
v___x_1596_ = v___x_1572_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_env_1563_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_nextMacroScope_1564_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_ngen_1565_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_auxDeclNGen_1566_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1602_, 5, v_cache_1567_);
lean_ctor_set(v_reuseFailAlloc_1602_, 6, v_messages_1568_);
lean_ctor_set(v_reuseFailAlloc_1602_, 7, v_infoState_1569_);
lean_ctor_set(v_reuseFailAlloc_1602_, 8, v_snapshotTasks_1570_);
v___x_1596_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1597_ = lean_st_ref_set(v___y_1544_, v___x_1596_);
v___x_1598_ = lean_box(0);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1598_);
v___x_1600_ = v___x_1553_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
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
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v___x_1549_);
lean_dec(v___x_1548_);
lean_dec_ref(v_msg_1540_);
lean_dec(v_cls_1539_);
v_a_1610_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1550_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1550_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___boxed(lean_object* v_cls_1618_, lean_object* v_msg_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v_cls_1618_, v_msg_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1625_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(lean_object* v_xs_1626_, lean_object* v_ys_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v_zero_1629_; uint8_t v_isZero_1630_; 
v_zero_1629_ = lean_unsigned_to_nat(0u);
v_isZero_1630_ = lean_nat_dec_eq(v_x_1628_, v_zero_1629_);
if (v_isZero_1630_ == 1)
{
lean_dec(v_x_1628_);
return v_isZero_1630_;
}
else
{
lean_object* v_one_1631_; lean_object* v_n_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_one_1631_ = lean_unsigned_to_nat(1u);
v_n_1632_ = lean_nat_sub(v_x_1628_, v_one_1631_);
lean_dec(v_x_1628_);
v___x_1633_ = lean_array_fget_borrowed(v_xs_1626_, v_n_1632_);
v___x_1634_ = lean_array_fget_borrowed(v_ys_1627_, v_n_1632_);
v___x_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_dec(v_n_1632_);
return v___x_1635_;
}
else
{
v_x_1628_ = v_n_1632_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg___boxed(lean_object* v_xs_1637_, lean_object* v_ys_1638_, lean_object* v_x_1639_){
_start:
{
uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_res_1640_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1637_, v_ys_1638_, v_x_1639_);
lean_dec_ref(v_ys_1638_);
lean_dec_ref(v_xs_1637_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(lean_object* v_x_1642_, lean_object* v_x_1643_){
_start:
{
if (lean_obj_tag(v_x_1642_) == 0)
{
if (lean_obj_tag(v_x_1643_) == 0)
{
uint8_t v___x_1644_; 
v___x_1644_ = 1;
return v___x_1644_;
}
else
{
uint8_t v___x_1645_; 
v___x_1645_ = 0;
return v___x_1645_;
}
}
else
{
if (lean_obj_tag(v_x_1643_) == 0)
{
uint8_t v___x_1646_; 
v___x_1646_ = 0;
return v___x_1646_;
}
else
{
lean_object* v_val_1647_; lean_object* v_val_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_val_1647_ = lean_ctor_get(v_x_1642_, 0);
v_val_1648_ = lean_ctor_get(v_x_1643_, 0);
v___x_1649_ = lean_array_get_size(v_val_1647_);
v___x_1650_ = lean_array_get_size(v_val_1648_);
v___x_1651_ = lean_nat_dec_eq(v___x_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
return v___x_1651_;
}
else
{
uint8_t v___x_1652_; 
v___x_1652_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_val_1647_, v_val_1648_, v___x_1649_);
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0___boxed(lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
uint8_t v_res_1655_; lean_object* v_r_1656_; 
v_res_1655_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_x_1653_, v_x_1654_);
lean_dec(v_x_1654_);
lean_dec(v_x_1653_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(lean_object* v_x_1659_, lean_object* v_specArgs_x3f_1660_){
_start:
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = ((lean_object*)(l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0));
v___x_1662_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_specArgs_x3f_1660_, v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed(lean_object* v_x_1663_, lean_object* v_specArgs_x3f_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(v_x_1663_, v_specArgs_x3f_1664_);
lean_dec(v_specArgs_x3f_1664_);
lean_dec(v_x_1663_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
if (lean_obj_tag(v_a_1667_) == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = l_List_reverse___redArg(v_a_1668_);
return v___x_1669_;
}
else
{
lean_object* v_head_1670_; lean_object* v_tail_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1688_; 
v_head_1670_ = lean_ctor_get(v_a_1667_, 0);
v_tail_1671_ = lean_ctor_get(v_a_1667_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_a_1667_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1673_ = v_a_1667_;
v_isShared_1674_ = v_isSharedCheck_1688_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_tail_1671_);
lean_inc(v_head_1670_);
lean_dec(v_a_1667_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1688_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___y_1676_; 
switch(lean_obj_tag(v_head_1670_))
{
case 0:
{
uint8_t v_weak_1681_; 
v_weak_1681_ = lean_ctor_get_uint8(v_head_1670_, 0);
lean_dec_ref_known(v_head_1670_, 0);
if (v_weak_1681_ == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
v___y_1676_ = v___x_1682_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
v___y_1676_ = v___x_1683_;
goto v___jp_1675_;
}
}
case 1:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8);
v___y_1676_ = v___x_1684_;
goto v___jp_1675_;
}
case 2:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11);
v___y_1676_ = v___x_1685_;
goto v___jp_1675_;
}
case 3:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14);
v___y_1676_ = v___x_1686_;
goto v___jp_1675_;
}
default: 
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17);
v___y_1676_ = v___x_1687_;
goto v___jp_1675_;
}
}
v___jp_1675_:
{
lean_object* v___x_1678_; 
lean_inc_ref(v___y_1676_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v_a_1668_);
lean_ctor_set(v___x_1673_, 0, v___y_1676_);
v___x_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___y_1676_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_a_1668_);
v___x_1678_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
v_a_1667_ = v_tail_1671_;
v_a_1668_ = v___x_1678_;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1689_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
return v___x_1693_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_1704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7));
v___x_1705_ = l_Lean_Name_append(v___x_1704_, v___x_1703_);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9));
v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(lean_object* v_as_1709_, size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_a_1719_; uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_b_1712_);
return v___x_1724_;
}
else
{
lean_object* v_a_1725_; lean_object* v_declName_1726_; lean_object* v_paramsInfo_1727_; lean_object* v___x_1728_; lean_object* v___y_1730_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_a_1725_ = lean_array_uget_borrowed(v_as_1709_, v_i_1711_);
v_declName_1726_ = lean_ctor_get(v_a_1725_, 0);
v_paramsInfo_1727_ = lean_ctor_get(v_a_1725_, 1);
v___x_1728_ = lean_box(0);
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = lean_array_get_size(v_paramsInfo_1727_);
v___x_1757_ = lean_nat_dec_lt(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
v_a_1719_ = v___x_1728_;
goto v___jp_1718_;
}
else
{
if (v___x_1757_ == 0)
{
v_a_1719_ = v___x_1728_;
goto v___jp_1718_;
}
else
{
size_t v___x_1758_; size_t v___x_1759_; uint8_t v___x_1760_; 
v___x_1758_ = ((size_t)0ULL);
v___x_1759_ = lean_usize_of_nat(v___x_1756_);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_paramsInfo_1727_, v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
v_a_1719_ = v___x_1728_;
goto v___jp_1718_;
}
else
{
lean_object* v_options_1761_; uint8_t v_hasTrace_1762_; 
v_options_1761_ = lean_ctor_get(v___y_1715_, 2);
v_hasTrace_1762_ = lean_ctor_get_uint8(v_options_1761_, sizeof(void*)*1);
if (v_hasTrace_1762_ == 0)
{
v___y_1730_ = v___y_1716_;
goto v___jp_1729_;
}
else
{
lean_object* v_inheritedTraceOptions_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_inheritedTraceOptions_1763_ = lean_ctor_get(v___y_1715_, 13);
v___x_1764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_1765_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8);
v___x_1766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1763_, v_options_1761_, v___x_1765_);
if (v___x_1766_ == 0)
{
v___y_1730_ = v___y_1716_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc(v_declName_1726_);
v___x_1767_ = l_Lean_MessageData_ofName(v_declName_1726_);
v___x_1768_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
lean_inc_ref(v_paramsInfo_1727_);
v___x_1770_ = lean_array_to_list(v_paramsInfo_1727_);
v___x_1771_ = lean_box(0);
v___x_1772_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(v___x_1770_, v___x_1771_);
v___x_1773_ = l_Lean_MessageData_ofList(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1769_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v___x_1764_, v___x_1774_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_dec_ref_known(v___x_1775_, 1);
v___y_1730_ = v___y_1716_;
goto v___jp_1729_;
}
else
{
return v___x_1775_;
}
}
}
}
}
}
v___jp_1729_:
{
lean_object* v___x_1731_; lean_object* v_env_1732_; lean_object* v_nextMacroScope_1733_; lean_object* v_ngen_1734_; lean_object* v_auxDeclNGen_1735_; lean_object* v_traceState_1736_; lean_object* v_messages_1737_; lean_object* v_infoState_1738_; lean_object* v_snapshotTasks_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1753_; 
v___x_1731_ = lean_st_ref_take(v___y_1730_);
v_env_1732_ = lean_ctor_get(v___x_1731_, 0);
v_nextMacroScope_1733_ = lean_ctor_get(v___x_1731_, 1);
v_ngen_1734_ = lean_ctor_get(v___x_1731_, 2);
v_auxDeclNGen_1735_ = lean_ctor_get(v___x_1731_, 3);
v_traceState_1736_ = lean_ctor_get(v___x_1731_, 4);
v_messages_1737_ = lean_ctor_get(v___x_1731_, 6);
v_infoState_1738_ = lean_ctor_get(v___x_1731_, 7);
v_snapshotTasks_1739_ = lean_ctor_get(v___x_1731_, 8);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v___x_1731_, 5);
lean_dec(v_unused_1754_);
v___x_1741_ = v___x_1731_;
v_isShared_1742_ = v_isSharedCheck_1753_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snapshotTasks_1739_);
lean_inc(v_infoState_1738_);
lean_inc(v_messages_1737_);
lean_inc(v_traceState_1736_);
lean_inc(v_auxDeclNGen_1735_);
lean_inc(v_ngen_1734_);
lean_inc(v_nextMacroScope_1733_);
lean_inc(v_env_1732_);
lean_dec(v___x_1731_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1753_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v_toEnvExtension_1744_; lean_object* v_asyncMode_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1743_ = l_Lean_Compiler_LCNF_specExtension;
v_toEnvExtension_1744_ = lean_ctor_get(v___x_1743_, 0);
v_asyncMode_1745_ = lean_ctor_get(v_toEnvExtension_1744_, 2);
v___x_1746_ = lean_box(0);
lean_inc(v_a_1725_);
v___x_1747_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1743_, v_env_1732_, v_a_1725_, v_asyncMode_1745_, v___x_1746_);
v___x_1748_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 5, v___x_1748_);
lean_ctor_set(v___x_1741_, 0, v___x_1747_);
v___x_1750_ = v___x_1741_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_nextMacroScope_1733_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_ngen_1734_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_auxDeclNGen_1735_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_traceState_1736_);
lean_ctor_set(v_reuseFailAlloc_1752_, 5, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1752_, 6, v_messages_1737_);
lean_ctor_set(v_reuseFailAlloc_1752_, 7, v_infoState_1738_);
lean_ctor_set(v_reuseFailAlloc_1752_, 8, v_snapshotTasks_1739_);
v___x_1750_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_st_ref_set(v___y_1730_, v___x_1750_);
v_a_1719_ = v___x_1728_;
goto v___jp_1718_;
}
}
}
}
v___jp_1718_:
{
size_t v___x_1720_; size_t v___x_1721_; 
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = lean_usize_add(v_i_1711_, v___x_1720_);
v_i_1711_ = v___x_1721_;
v_b_1712_ = v_a_1719_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___boxed(lean_object* v_as_1776_, lean_object* v_sz_1777_, lean_object* v_i_1778_, lean_object* v_b_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
size_t v_sz_boxed_1785_; size_t v_i_boxed_1786_; lean_object* v_res_1787_; 
v_sz_boxed_1785_ = lean_unbox_usize(v_sz_1777_);
lean_dec(v_sz_1777_);
v_i_boxed_1786_ = lean_unbox_usize(v_i_1778_);
lean_dec(v_i_1778_);
v_res_1787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_as_1776_, v_sz_boxed_1785_, v_i_boxed_1786_, v_b_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v_as_1776_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries(lean_object* v_decls_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___f_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___f_1795_ = ((lean_object*)(l_Lean_Compiler_LCNF_saveSpecEntries___closed__0));
v___x_1796_ = lean_array_get_size(v_decls_1789_);
v___x_1797_ = 0;
v___x_1798_ = lean_box(v___x_1797_);
v___x_1799_ = lean_mk_array(v___x_1796_, v___x_1798_);
v___x_1800_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1789_, v___f_1795_, v___x_1799_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec_ref(v___x_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1802_; size_t v_sz_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = lean_box(0);
v_sz_1803_ = lean_array_size(v_a_1801_);
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_a_1801_, v_sz_1803_, v___x_1804_, v___x_1802_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1801_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v___x_1805_, 0);
lean_dec(v_unused_1813_);
v___x_1807_ = v___x_1805_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_dec(v___x_1805_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1802_);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1802_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
else
{
return v___x_1805_;
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1814_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1800_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1800_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___boxed(lean_object* v_decls_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Compiler_LCNF_saveSpecEntries(v_decls_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
return v_res_1828_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(lean_object* v_xs_1829_, lean_object* v_ys_1830_, lean_object* v_hsz_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1829_, v_ys_1830_, v_x_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___boxed(lean_object* v_xs_1835_, lean_object* v_ys_1836_, lean_object* v_hsz_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_res_1840_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(v_xs_1835_, v_ys_1836_, v_hsz_1837_, v_x_1838_, v_x_1839_);
lean_dec_ref(v_ys_1836_);
lean_dec_ref(v_xs_1835_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(lean_object* v_as_1842_, lean_object* v_k_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v_m_1848_; lean_object* v_a_1849_; uint8_t v___x_1850_; 
v___x_1846_ = lean_nat_add(v_x_1844_, v_x_1845_);
v___x_1847_ = lean_unsigned_to_nat(1u);
v_m_1848_ = lean_nat_shiftr(v___x_1846_, v___x_1847_);
lean_dec(v___x_1846_);
v_a_1849_ = lean_array_fget_borrowed(v_as_1842_, v_m_1848_);
v___x_1850_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_a_1849_, v_k_1843_);
if (v___x_1850_ == 0)
{
uint8_t v___x_1851_; 
lean_dec(v_x_1845_);
v___x_1851_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_k_1843_, v_a_1849_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_dec(v_m_1848_);
lean_dec(v_x_1844_);
lean_inc(v_a_1849_);
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v_a_1849_);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = lean_nat_dec_eq(v_m_1848_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = lean_nat_sub(v_m_1848_, v___x_1847_);
lean_dec(v_m_1848_);
v___x_1856_ = lean_nat_dec_lt(v___x_1855_, v_x_1844_);
if (v___x_1856_ == 0)
{
v_x_1845_ = v___x_1855_;
goto _start;
}
else
{
lean_object* v___x_1858_; 
lean_dec(v___x_1855_);
lean_dec(v_x_1844_);
v___x_1858_ = lean_box(0);
return v___x_1858_;
}
}
else
{
lean_object* v___x_1859_; 
lean_dec(v_m_1848_);
lean_dec(v_x_1844_);
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
}
}
else
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
lean_dec(v_x_1844_);
v___x_1860_ = lean_nat_add(v_m_1848_, v___x_1847_);
lean_dec(v_m_1848_);
v___x_1861_ = lean_nat_dec_le(v___x_1860_, v_x_1845_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec(v___x_1860_);
lean_dec(v_x_1845_);
v___x_1862_ = lean_box(0);
return v___x_1862_;
}
else
{
v_x_1844_ = v___x_1860_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg___boxed(lean_object* v_as_1864_, lean_object* v_k_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v_as_1864_, v_k_1865_, v_x_1866_, v_x_1867_);
lean_dec_ref(v_k_1865_);
lean_dec_ref(v_as_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1869_, lean_object* v_vals_1870_, lean_object* v_i_1871_, lean_object* v_k_1872_){
_start:
{
lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = lean_array_get_size(v_keys_1869_);
v___x_1874_ = lean_nat_dec_lt(v_i_1871_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
lean_dec(v_i_1871_);
v___x_1875_ = lean_box(0);
return v___x_1875_;
}
else
{
lean_object* v_k_x27_1876_; uint8_t v___x_1877_; 
v_k_x27_1876_ = lean_array_fget_borrowed(v_keys_1869_, v_i_1871_);
v___x_1877_ = lean_name_eq(v_k_1872_, v_k_x27_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_nat_add(v_i_1871_, v___x_1878_);
lean_dec(v_i_1871_);
v_i_1871_ = v___x_1879_;
goto _start;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_array_fget_borrowed(v_vals_1870_, v_i_1871_);
lean_dec(v_i_1871_);
lean_inc(v___x_1881_);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1883_, lean_object* v_vals_1884_, lean_object* v_i_1885_, lean_object* v_k_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1883_, v_vals_1884_, v_i_1885_, v_k_1886_);
lean_dec(v_k_1886_);
lean_dec_ref(v_vals_1884_);
lean_dec_ref(v_keys_1883_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_1888_, size_t v_x_1889_, lean_object* v_x_1890_){
_start:
{
if (lean_obj_tag(v_x_1888_) == 0)
{
lean_object* v_es_1891_; lean_object* v___x_1892_; size_t v___x_1893_; size_t v___x_1894_; lean_object* v_j_1895_; lean_object* v___x_1896_; 
v_es_1891_ = lean_ctor_get(v_x_1888_, 0);
v___x_1892_ = lean_box(2);
v___x_1893_ = ((size_t)31ULL);
v___x_1894_ = lean_usize_land(v_x_1889_, v___x_1893_);
v_j_1895_ = lean_usize_to_nat(v___x_1894_);
v___x_1896_ = lean_array_get_borrowed(v___x_1892_, v_es_1891_, v_j_1895_);
lean_dec(v_j_1895_);
switch(lean_obj_tag(v___x_1896_))
{
case 0:
{
lean_object* v_key_1897_; lean_object* v_val_1898_; uint8_t v___x_1899_; 
v_key_1897_ = lean_ctor_get(v___x_1896_, 0);
v_val_1898_ = lean_ctor_get(v___x_1896_, 1);
v___x_1899_ = lean_name_eq(v_x_1890_, v_key_1897_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_box(0);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; 
lean_inc(v_val_1898_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v_val_1898_);
return v___x_1901_;
}
}
case 1:
{
lean_object* v_node_1902_; size_t v___x_1903_; size_t v___x_1904_; 
v_node_1902_ = lean_ctor_get(v___x_1896_, 0);
v___x_1903_ = ((size_t)5ULL);
v___x_1904_ = lean_usize_shift_right(v_x_1889_, v___x_1903_);
v_x_1888_ = v_node_1902_;
v_x_1889_ = v___x_1904_;
goto _start;
}
default: 
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_box(0);
return v___x_1906_;
}
}
}
else
{
lean_object* v_ks_1907_; lean_object* v_vs_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_ks_1907_ = lean_ctor_get(v_x_1888_, 0);
v_vs_1908_ = lean_ctor_get(v_x_1888_, 1);
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1907_, v_vs_1908_, v___x_1909_, v_x_1890_);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1911_, lean_object* v_x_1912_, lean_object* v_x_1913_){
_start:
{
size_t v_x_403__boxed_1914_; lean_object* v_res_1915_; 
v_x_403__boxed_1914_ = lean_unbox_usize(v_x_1912_);
lean_dec(v_x_1912_);
v_res_1915_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1911_, v_x_403__boxed_1914_, v_x_1913_);
lean_dec(v_x_1913_);
lean_dec_ref(v_x_1911_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
uint64_t v___y_1919_; 
if (lean_obj_tag(v_x_1917_) == 0)
{
uint64_t v___x_1922_; 
v___x_1922_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1919_ = v___x_1922_;
goto v___jp_1918_;
}
else
{
uint64_t v_hash_1923_; 
v_hash_1923_ = lean_ctor_get_uint64(v_x_1917_, sizeof(void*)*2);
v___y_1919_ = v_hash_1923_;
goto v___jp_1918_;
}
v___jp_1918_:
{
size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_uint64_to_usize(v___y_1919_);
v___x_1921_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1916_, v___x_1920_, v_x_1917_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg___boxed(lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_1924_, v_x_1925_);
lean_dec(v_x_1925_);
lean_dec_ref(v_x_1924_);
return v_res_1926_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(lean_object* v_env_1930_, lean_object* v_declName_1931_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1941_; 
v___x_1932_ = lean_obj_once(&l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0, &l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0);
v___x_1933_ = l_Lean_Compiler_LCNF_specExtension;
v___x_1941_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1930_, v_declName_1931_);
if (lean_obj_tag(v___x_1941_) == 0)
{
goto v___jp_1934_;
}
else
{
lean_object* v_val_1942_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_val_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_val_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1956_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1932_, v___x_1933_, v_env_1930_, v_val_1942_);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_array_get_size(v___x_1956_);
v___x_1959_ = lean_nat_dec_lt(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_dec_ref(v___x_1956_);
goto v___jp_1943_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1960_ = lean_unsigned_to_nat(1u);
v___x_1961_ = lean_nat_sub(v___x_1958_, v___x_1960_);
v___x_1962_ = lean_nat_dec_le(v___x_1957_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_dec(v___x_1961_);
lean_dec_ref(v___x_1956_);
goto v___jp_1943_;
}
else
{
lean_object* v___x_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1963_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1964_ = 0;
lean_inc(v_declName_1931_);
v___x_1965_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1965_, 0, v_declName_1931_);
lean_ctor_set(v___x_1965_, 1, v___x_1963_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*2, v___x_1964_);
v___x_1966_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_1956_, v___x_1965_, v___x_1957_, v___x_1961_);
lean_dec_ref_known(v___x_1965_, 2);
lean_dec_ref(v___x_1956_);
if (lean_obj_tag(v___x_1966_) == 0)
{
goto v___jp_1943_;
}
else
{
lean_dec(v_val_1942_);
lean_dec(v_declName_1931_);
lean_dec_ref(v_env_1930_);
return v___x_1966_;
}
}
}
v___jp_1943_:
{
uint8_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1944_ = 0;
v___x_1945_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1932_, v___x_1933_, v_env_1930_, v_val_1942_, v___x_1944_);
lean_dec(v_val_1942_);
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = lean_array_get_size(v___x_1945_);
v___x_1948_ = lean_nat_dec_lt(v___x_1946_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_dec_ref(v___x_1945_);
goto v___jp_1934_;
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1949_ = lean_unsigned_to_nat(1u);
v___x_1950_ = lean_nat_sub(v___x_1947_, v___x_1949_);
v___x_1951_ = lean_nat_dec_le(v___x_1946_, v___x_1950_);
if (v___x_1951_ == 0)
{
lean_dec(v___x_1950_);
lean_dec_ref(v___x_1945_);
goto v___jp_1934_;
}
else
{
lean_object* v___x_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1952_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1953_ = 0;
lean_inc(v_declName_1931_);
v___x_1954_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1954_, 0, v_declName_1931_);
lean_ctor_set(v___x_1954_, 1, v___x_1952_);
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*2, v___x_1953_);
v___x_1955_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_1945_, v___x_1954_, v___x_1946_, v___x_1950_);
lean_dec_ref_known(v___x_1954_, 2);
lean_dec_ref(v___x_1945_);
if (lean_obj_tag(v___x_1955_) == 0)
{
goto v___jp_1934_;
}
else
{
lean_dec(v_declName_1931_);
lean_dec_ref(v_env_1930_);
return v___x_1955_;
}
}
}
}
}
v___jp_1934_:
{
lean_object* v_toEnvExtension_1935_; lean_object* v_asyncMode_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v_snd_1939_; lean_object* v___x_1940_; 
v_toEnvExtension_1935_ = lean_ctor_get(v___x_1933_, 0);
v_asyncMode_1936_ = lean_ctor_get(v_toEnvExtension_1935_, 2);
v___x_1937_ = lean_box(0);
v___x_1938_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1932_, v___x_1933_, v_env_1930_, v_asyncMode_1936_, v___x_1937_);
v_snd_1939_ = lean_ctor_get(v___x_1938_, 1);
lean_inc(v_snd_1939_);
lean_dec(v___x_1938_);
v___x_1940_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_snd_1939_, v_declName_1931_);
lean_dec(v_declName_1931_);
lean_dec(v_snd_1939_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(lean_object* v_00_u03b2_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_1968_, v_x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_1971_, lean_object* v_x_1972_, lean_object* v_x_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(v_00_u03b2_1971_, v_x_1972_, v_x_1973_);
lean_dec(v_x_1973_);
lean_dec_ref(v_x_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(lean_object* v_as_1975_, lean_object* v_k_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v_as_1975_, v_k_1976_, v_x_1977_, v_x_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___boxed(lean_object* v_as_1981_, lean_object* v_k_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(v_as_1981_, v_k_1982_, v_x_1983_, v_x_1984_, v_x_1985_);
lean_dec_ref(v_k_1982_);
lean_dec_ref(v_as_1981_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1987_, lean_object* v_x_1988_, size_t v_x_1989_, lean_object* v_x_1990_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1988_, v_x_1989_, v_x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
size_t v_x_567__boxed_1996_; lean_object* v_res_1997_; 
v_x_567__boxed_1996_ = lean_unbox_usize(v_x_1994_);
lean_dec(v_x_1994_);
v_res_1997_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(v_00_u03b2_1992_, v_x_1993_, v_x_567__boxed_1996_, v_x_1995_);
lean_dec(v_x_1995_);
lean_dec_ref(v_x_1993_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1998_, lean_object* v_keys_1999_, lean_object* v_vals_2000_, lean_object* v_heq_2001_, lean_object* v_i_2002_, lean_object* v_k_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1999_, v_vals_2000_, v_i_2002_, v_k_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2005_, lean_object* v_keys_2006_, lean_object* v_vals_2007_, lean_object* v_heq_2008_, lean_object* v_i_2009_, lean_object* v_k_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2005_, v_keys_2006_, v_vals_2007_, v_heq_2008_, v_i_2009_, v_k_2010_);
lean_dec(v_k_2010_);
lean_dec_ref(v_vals_2007_);
lean_dec_ref(v_keys_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0(lean_object* v_declName_2012_, lean_object* v_toPure_2013_, lean_object* v_____do__lift_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_2014_, v_declName_2012_);
v___x_2016_ = lean_apply_2(v_toPure_2013_, lean_box(0), v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_declName_2019_){
_start:
{
lean_object* v_toApplicative_2020_; lean_object* v_toBind_2021_; lean_object* v_getEnv_2022_; lean_object* v_toPure_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; 
v_toApplicative_2020_ = lean_ctor_get(v_inst_2017_, 0);
lean_inc_ref(v_toApplicative_2020_);
v_toBind_2021_ = lean_ctor_get(v_inst_2017_, 1);
lean_inc(v_toBind_2021_);
lean_dec_ref(v_inst_2017_);
v_getEnv_2022_ = lean_ctor_get(v_inst_2018_, 0);
lean_inc(v_getEnv_2022_);
lean_dec_ref(v_inst_2018_);
v_toPure_2023_ = lean_ctor_get(v_toApplicative_2020_, 1);
lean_inc(v_toPure_2023_);
lean_dec_ref(v_toApplicative_2020_);
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2024_, 0, v_declName_2019_);
lean_closure_set(v___f_2024_, 1, v_toPure_2023_);
v___x_2025_ = lean_apply_4(v_toBind_2021_, lean_box(0), lean_box(0), v_getEnv_2022_, v___f_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f(lean_object* v_m_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_declName_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(v_inst_2027_, v_inst_2028_, v_declName_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0(lean_object* v_declName_2031_, lean_object* v_toPure_2032_, lean_object* v_____do__lift_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_2033_, v_declName_2031_);
if (lean_obj_tag(v___x_2034_) == 0)
{
uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = 0;
v___x_2036_ = lean_box(v___x_2035_);
v___x_2037_ = lean_apply_2(v_toPure_2032_, lean_box(0), v___x_2036_);
return v___x_2037_;
}
else
{
uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref_known(v___x_2034_, 1);
v___x_2038_ = 1;
v___x_2039_ = lean_box(v___x_2038_);
v___x_2040_ = lean_apply_2(v_toPure_2032_, lean_box(0), v___x_2039_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg(lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_declName_2043_){
_start:
{
lean_object* v_toApplicative_2044_; lean_object* v_toBind_2045_; lean_object* v_getEnv_2046_; lean_object* v_toPure_2047_; lean_object* v___f_2048_; lean_object* v___x_2049_; 
v_toApplicative_2044_ = lean_ctor_get(v_inst_2041_, 0);
lean_inc_ref(v_toApplicative_2044_);
v_toBind_2045_ = lean_ctor_get(v_inst_2041_, 1);
lean_inc(v_toBind_2045_);
lean_dec_ref(v_inst_2041_);
v_getEnv_2046_ = lean_ctor_get(v_inst_2042_, 0);
lean_inc(v_getEnv_2046_);
lean_dec_ref(v_inst_2042_);
v_toPure_2047_ = lean_ctor_get(v_toApplicative_2044_, 1);
lean_inc(v_toPure_2047_);
lean_dec_ref(v_toApplicative_2044_);
v___f_2048_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2048_, 0, v_declName_2043_);
lean_closure_set(v___f_2048_, 1, v_toPure_2047_);
v___x_2049_ = lean_apply_4(v_toBind_2045_, lean_box(0), lean_box(0), v_getEnv_2046_, v___f_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate(lean_object* v_m_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_declName_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_Compiler_LCNF_isSpecCandidate___redArg(v_inst_2051_, v_inst_2052_, v_declName_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_2120_ = 0;
v___x_2121_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_));
v___x_2122_ = l_Lean_registerTraceClass(v___x_2119_, v___x_2120_, v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2____boxed(lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
return v_res_2124_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_SpecInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
