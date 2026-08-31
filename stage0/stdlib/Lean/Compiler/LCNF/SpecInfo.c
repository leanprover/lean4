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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___closed__0_value)}};
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(lean_object* v_x_334_, size_t v_x_335_, size_t v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v_es_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v_j_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_es_339_ = lean_ctor_get(v_x_334_, 0);
v___x_340_ = ((size_t)31ULL);
v___x_341_ = lean_usize_land(v_x_335_, v___x_340_);
v_j_342_ = lean_usize_to_nat(v___x_341_);
v___x_343_ = lean_array_get_size(v_es_339_);
v___x_344_ = lean_nat_dec_lt(v_j_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_dec(v_j_342_);
lean_dec(v_x_338_);
lean_dec(v_x_337_);
return v_x_334_;
}
else
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_383_; 
lean_inc_ref(v_es_339_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_x_334_, 0);
lean_dec(v_unused_384_);
v___x_346_ = v_x_334_;
v_isShared_347_ = v_isSharedCheck_383_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_x_334_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_383_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_v_348_; lean_object* v___x_349_; lean_object* v_xs_x27_350_; lean_object* v___y_352_; 
v_v_348_ = lean_array_fget(v_es_339_, v_j_342_);
v___x_349_ = lean_box(0);
v_xs_x27_350_ = lean_array_fset(v_es_339_, v_j_342_, v___x_349_);
switch(lean_obj_tag(v_v_348_))
{
case 0:
{
lean_object* v_key_357_; lean_object* v_val_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_368_; 
v_key_357_ = lean_ctor_get(v_v_348_, 0);
v_val_358_ = lean_ctor_get(v_v_348_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_v_348_);
if (v_isSharedCheck_368_ == 0)
{
v___x_360_ = v_v_348_;
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_val_358_);
lean_inc(v_key_357_);
lean_dec(v_v_348_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
uint8_t v___x_362_; 
v___x_362_ = lean_name_eq(v_x_337_, v_key_357_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_del_object(v___x_360_);
v___x_363_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_357_, v_val_358_, v_x_337_, v_x_338_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
v___y_352_ = v___x_364_;
goto v___jp_351_;
}
else
{
lean_object* v___x_366_; 
lean_dec(v_val_358_);
lean_dec(v_key_357_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_x_338_);
lean_ctor_set(v___x_360_, 0, v_x_337_);
v___x_366_ = v___x_360_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_x_337_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_x_338_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
v___y_352_ = v___x_366_;
goto v___jp_351_;
}
}
}
}
case 1:
{
lean_object* v_node_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_381_; 
v_node_369_ = lean_ctor_get(v_v_348_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_v_348_);
if (v_isSharedCheck_381_ == 0)
{
v___x_371_ = v_v_348_;
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_node_369_);
lean_dec(v_v_348_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_373_ = ((size_t)5ULL);
v___x_374_ = lean_usize_shift_right(v_x_335_, v___x_373_);
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_x_336_, v___x_375_);
v___x_377_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_node_369_, v___x_374_, v___x_376_, v_x_337_, v_x_338_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_377_);
v___x_379_ = v___x_371_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
v___y_352_ = v___x_379_;
goto v___jp_351_;
}
}
}
default: 
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_x_337_);
lean_ctor_set(v___x_382_, 1, v_x_338_);
v___y_352_ = v___x_382_;
goto v___jp_351_;
}
}
v___jp_351_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_array_fset(v_xs_x27_350_, v_j_342_, v___y_352_);
lean_dec(v_j_342_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_353_);
v___x_355_ = v___x_346_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
else
{
lean_object* v_ks_385_; lean_object* v_vs_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_404_; 
v_ks_385_ = lean_ctor_get(v_x_334_, 0);
v_vs_386_ = lean_ctor_get(v_x_334_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_404_ == 0)
{
v___x_388_ = v_x_334_;
v_isShared_389_ = v_isSharedCheck_404_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_vs_386_);
lean_inc(v_ks_385_);
lean_dec(v_x_334_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_404_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_ks_385_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_vs_386_);
v___x_391_ = v_reuseFailAlloc_403_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v_newNode_392_; size_t v___x_393_; uint8_t v___x_394_; 
v_newNode_392_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v___x_391_, v_x_337_, v_x_338_);
v___x_393_ = ((size_t)7ULL);
v___x_394_ = lean_usize_dec_le(v___x_393_, v_x_336_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_395_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_392_);
v___x_396_ = lean_unsigned_to_nat(4u);
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_396_);
lean_dec(v___x_395_);
if (v___x_397_ == 0)
{
lean_object* v_ks_398_; lean_object* v_vs_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_ks_398_ = lean_ctor_get(v_newNode_392_, 0);
lean_inc_ref(v_ks_398_);
v_vs_399_ = lean_ctor_get(v_newNode_392_, 1);
lean_inc_ref(v_vs_399_);
lean_dec_ref(v_newNode_392_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0);
v___x_402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_x_336_, v_ks_398_, v_vs_399_, v___x_400_, v___x_401_);
lean_dec_ref(v_vs_399_);
lean_dec_ref(v_ks_398_);
return v___x_402_;
}
else
{
return v_newNode_392_;
}
}
else
{
return v_newNode_392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(size_t v_depth_405_, lean_object* v_keys_406_, lean_object* v_vals_407_, lean_object* v_i_408_, lean_object* v_entries_409_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_keys_406_);
v___x_411_ = lean_nat_dec_lt(v_i_408_, v___x_410_);
if (v___x_411_ == 0)
{
lean_dec(v_i_408_);
return v_entries_409_;
}
else
{
lean_object* v_k_412_; lean_object* v_v_413_; uint64_t v___y_415_; 
v_k_412_ = lean_array_fget_borrowed(v_keys_406_, v_i_408_);
v_v_413_ = lean_array_fget_borrowed(v_vals_407_, v_i_408_);
if (lean_obj_tag(v_k_412_) == 0)
{
uint64_t v___x_426_; 
v___x_426_ = 1723ULL;
v___y_415_ = v___x_426_;
goto v___jp_414_;
}
else
{
uint64_t v_hash_427_; 
v_hash_427_ = lean_ctor_get_uint64(v_k_412_, sizeof(void*)*2);
v___y_415_ = v_hash_427_;
goto v___jp_414_;
}
v___jp_414_:
{
size_t v_h_416_; size_t v___x_417_; lean_object* v___x_418_; size_t v___x_419_; size_t v___x_420_; size_t v___x_421_; size_t v_h_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_h_416_ = lean_uint64_to_usize(v___y_415_);
v___x_417_ = ((size_t)5ULL);
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_sub(v_depth_405_, v___x_419_);
v___x_421_ = lean_usize_mul(v___x_417_, v___x_420_);
v_h_422_ = lean_usize_shift_right(v_h_416_, v___x_421_);
v___x_423_ = lean_nat_add(v_i_408_, v___x_418_);
lean_dec(v_i_408_);
lean_inc(v_v_413_);
lean_inc(v_k_412_);
v___x_424_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_entries_409_, v_h_422_, v_depth_405_, v_k_412_, v_v_413_);
v_i_408_ = v___x_423_;
v_entries_409_ = v___x_424_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_428_, lean_object* v_keys_429_, lean_object* v_vals_430_, lean_object* v_i_431_, lean_object* v_entries_432_){
_start:
{
size_t v_depth_boxed_433_; lean_object* v_res_434_; 
v_depth_boxed_433_ = lean_unbox_usize(v_depth_428_);
lean_dec(v_depth_428_);
v_res_434_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_boxed_433_, v_keys_429_, v_vals_430_, v_i_431_, v_entries_432_);
lean_dec_ref(v_vals_430_);
lean_dec_ref(v_keys_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
size_t v_x_363__boxed_440_; size_t v_x_364__boxed_441_; lean_object* v_res_442_; 
v_x_363__boxed_440_ = lean_unbox_usize(v_x_436_);
lean_dec(v_x_436_);
v_x_364__boxed_441_ = lean_unbox_usize(v_x_437_);
lean_dec(v_x_437_);
v_res_442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_435_, v_x_363__boxed_440_, v_x_364__boxed_441_, v_x_438_, v_x_439_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
uint64_t v___y_447_; 
if (lean_obj_tag(v_x_444_) == 0)
{
uint64_t v___x_451_; 
v___x_451_ = 1723ULL;
v___y_447_ = v___x_451_;
goto v___jp_446_;
}
else
{
uint64_t v_hash_452_; 
v_hash_452_ = lean_ctor_get_uint64(v_x_444_, sizeof(void*)*2);
v___y_447_ = v_hash_452_;
goto v___jp_446_;
}
v___jp_446_:
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_uint64_to_usize(v___y_447_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_443_, v___x_448_, v___x_449_, v_x_444_, v_x_445_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecState_addEntry(lean_object* v_s_453_, lean_object* v_e_454_){
_start:
{
lean_object* v_declName_455_; lean_object* v___x_456_; 
v_declName_455_ = lean_ctor_get(v_e_454_, 0);
lean_inc(v_declName_455_);
v___x_456_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_s_453_, v_declName_455_, v_e_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0(lean_object* v_00_u03b2_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_x_458_, v_x_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_x_463_, size_t v_x_464_, size_t v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_463_, v_x_464_, v_x_465_, v_x_466_, v_x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
size_t v_x_545__boxed_475_; size_t v_x_546__boxed_476_; lean_object* v_res_477_; 
v_x_545__boxed_475_ = lean_unbox_usize(v_x_471_);
lean_dec(v_x_471_);
v_x_546__boxed_476_ = lean_unbox_usize(v_x_472_);
lean_dec(v_x_472_);
v_res_477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(v_00_u03b2_469_, v_x_470_, v_x_545__boxed_475_, v_x_546__boxed_476_, v_x_473_, v_x_474_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_483_, size_t v_depth_484_, lean_object* v_keys_485_, lean_object* v_vals_486_, lean_object* v_heq_487_, lean_object* v_i_488_, lean_object* v_entries_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_484_, v_keys_485_, v_vals_486_, v_i_488_, v_entries_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_491_, lean_object* v_depth_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_heq_495_, lean_object* v_i_496_, lean_object* v_entries_497_){
_start:
{
size_t v_depth_boxed_498_; lean_object* v_res_499_; 
v_depth_boxed_498_ = lean_unbox_usize(v_depth_492_);
lean_dec(v_depth_492_);
v_res_499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(v_00_u03b2_491_, v_depth_boxed_498_, v_keys_493_, v_vals_494_, v_heq_495_, v_i_496_, v_entries_497_);
lean_dec_ref(v_vals_494_);
lean_dec_ref(v_keys_493_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_x_501_, v_x_502_, v_x_503_, v_x_504_);
return v___x_505_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(lean_object* v_a_506_, lean_object* v_b_507_){
_start:
{
lean_object* v_declName_508_; lean_object* v_declName_509_; uint8_t v___x_510_; 
v_declName_508_ = lean_ctor_get(v_a_506_, 0);
v_declName_509_ = lean_ctor_get(v_b_507_, 0);
v___x_510_ = l_Lean_Name_quickLt(v_declName_508_, v_declName_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed(lean_object* v_a_511_, lean_object* v_b_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(v_a_511_, v_b_512_);
lean_dec_ref(v_b_512_);
lean_dec_ref(v_a_511_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries(lean_object* v_entries_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_array_get_size(v_entries_516_);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_nat_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___y_524_; uint8_t v___x_528_; 
v___x_520_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0));
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_sub(v___x_517_, v___x_521_);
v___x_528_ = lean_nat_dec_le(v___x_518_, v___x_522_);
if (v___x_528_ == 0)
{
lean_inc(v___x_522_);
v___y_524_ = v___x_522_;
goto v___jp_523_;
}
else
{
v___y_524_ = v___x_518_;
goto v___jp_523_;
}
v___jp_523_:
{
uint8_t v___x_525_; 
v___x_525_ = lean_nat_dec_le(v___y_524_, v___x_522_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_dec(v___x_522_);
lean_inc(v___y_524_);
v___x_526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_520_, v___x_517_, v_entries_516_, v___y_524_, v___y_524_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_524_);
return v___x_526_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_520_, v___x_517_, v_entries_516_, v___y_524_, v___x_522_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_522_);
return v___x_527_;
}
}
}
else
{
return v_entries_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(lean_object* v_entries_532_, lean_object* v_declName_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_array_get_size(v_entries_532_);
v___x_536_ = lean_nat_dec_lt(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v_declName_533_);
v___x_537_ = lean_box(0);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_sub(v___x_535_, v___x_538_);
v___x_540_ = lean_nat_dec_le(v___x_534_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_dec(v___x_539_);
lean_dec(v_declName_533_);
v___x_541_ = lean_box(0);
return v___x_541_;
}
else
{
lean_object* v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_543_ = 0;
v___x_544_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_544_, 0, v_declName_533_);
lean_ctor_set(v___x_544_, 1, v___x_542_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*2, v___x_543_);
v___x_545_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0));
v___x_546_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1));
v___x_547_ = l_Array_binSearchAux___redArg(v___x_545_, v___x_546_, v_entries_532_, v___x_544_, v___x_534_, v___x_539_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___boxed(lean_object* v_entries_548_, lean_object* v_declName_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(v_entries_548_, v_declName_549_);
lean_dec_ref(v_entries_548_);
return v_res_550_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_declName_553_; lean_object* v_declName_554_; uint8_t v___x_555_; 
v_declName_553_ = lean_ctor_get(v___y_551_, 0);
v_declName_554_ = lean_ctor_get(v___y_552_, 0);
v___x_555_ = l_Lean_Name_quickLt(v_declName_553_, v_declName_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0___boxed(lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v_res_558_; lean_object* v_r_559_; 
v_res_558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___y_556_, v___y_557_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___y_556_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_hi_560_, lean_object* v_pivot_561_, lean_object* v_as_562_, lean_object* v_i_563_, lean_object* v_k_564_){
_start:
{
uint8_t v___x_565_; 
v___x_565_ = lean_nat_dec_lt(v_k_564_, v_hi_560_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v_k_564_);
v___x_566_ = lean_array_fswap(v_as_562_, v_i_563_, v_hi_560_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_i_563_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
return v___x_567_;
}
else
{
lean_object* v___x_568_; lean_object* v_declName_569_; lean_object* v_declName_570_; uint8_t v___x_571_; 
v___x_568_ = lean_array_fget_borrowed(v_as_562_, v_k_564_);
v_declName_569_ = lean_ctor_get(v___x_568_, 0);
v_declName_570_ = lean_ctor_get(v_pivot_561_, 0);
v___x_571_ = l_Lean_Name_quickLt(v_declName_569_, v_declName_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v_k_564_, v___x_572_);
lean_dec(v_k_564_);
v_k_564_ = v___x_573_;
goto _start;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_array_fswap(v_as_562_, v_i_563_, v_k_564_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_i_563_, v___x_576_);
lean_dec(v_i_563_);
v___x_578_ = lean_nat_add(v_k_564_, v___x_576_);
lean_dec(v_k_564_);
v_as_562_ = v___x_575_;
v_i_563_ = v___x_577_;
v_k_564_ = v___x_578_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_hi_580_, lean_object* v_pivot_581_, lean_object* v_as_582_, lean_object* v_i_583_, lean_object* v_k_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_580_, v_pivot_581_, v_as_582_, v_i_583_, v_k_584_);
lean_dec_ref(v_pivot_581_);
lean_dec(v_hi_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(lean_object* v_n_586_, lean_object* v_as_587_, lean_object* v_lo_588_, lean_object* v_hi_589_){
_start:
{
lean_object* v___y_591_; uint8_t v___x_601_; 
v___x_601_ = lean_nat_dec_lt(v_lo_588_, v_hi_589_);
if (v___x_601_ == 0)
{
lean_dec(v_lo_588_);
return v_as_587_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_mid_604_; lean_object* v___y_606_; lean_object* v___y_612_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_602_ = lean_nat_add(v_lo_588_, v_hi_589_);
v___x_603_ = lean_unsigned_to_nat(1u);
v_mid_604_ = lean_nat_shiftr(v___x_602_, v___x_603_);
lean_dec(v___x_602_);
v___x_617_ = lean_array_fget_borrowed(v_as_587_, v_mid_604_);
v___x_618_ = lean_array_fget_borrowed(v_as_587_, v_lo_588_);
v___x_619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
v___y_612_ = v_as_587_;
goto v___jp_611_;
}
else
{
lean_object* v___x_620_; 
v___x_620_ = lean_array_fswap(v_as_587_, v_lo_588_, v_mid_604_);
v___y_612_ = v___x_620_;
goto v___jp_611_;
}
v___jp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_array_fget_borrowed(v___y_606_, v_mid_604_);
v___x_608_ = lean_array_fget_borrowed(v___y_606_, v_hi_589_);
v___x_609_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v_mid_604_);
v___y_591_ = v___y_606_;
goto v___jp_590_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_array_fswap(v___y_606_, v_mid_604_, v_hi_589_);
lean_dec(v_mid_604_);
v___y_591_ = v___x_610_;
goto v___jp_590_;
}
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_array_fget_borrowed(v___y_612_, v_hi_589_);
v___x_614_ = lean_array_fget_borrowed(v___y_612_, v_lo_588_);
v___x_615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
v___y_606_ = v___y_612_;
goto v___jp_605_;
}
else
{
lean_object* v___x_616_; 
v___x_616_ = lean_array_fswap(v___y_612_, v_lo_588_, v_hi_589_);
v___y_606_ = v___x_616_;
goto v___jp_605_;
}
}
}
v___jp_590_:
{
lean_object* v_pivot_592_; lean_object* v___x_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; uint8_t v___x_596_; 
v_pivot_592_ = lean_array_fget(v___y_591_, v_hi_589_);
lean_inc_n(v_lo_588_, 2);
v___x_593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_589_, v_pivot_592_, v___y_591_, v_lo_588_, v_lo_588_);
lean_dec(v_pivot_592_);
v_fst_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v___x_593_, 1);
lean_inc(v_snd_595_);
lean_dec_ref(v___x_593_);
v___x_596_ = lean_nat_dec_le(v_hi_589_, v_fst_594_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_586_, v_snd_595_, v_lo_588_, v_fst_594_);
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_fst_594_, v___x_598_);
lean_dec(v_fst_594_);
v_as_587_ = v___x_597_;
v_lo_588_ = v___x_599_;
goto _start;
}
else
{
lean_dec(v_fst_594_);
lean_dec(v_lo_588_);
return v_snd_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_n_621_, lean_object* v_as_622_, lean_object* v_lo_623_, lean_object* v_hi_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_621_, v_as_622_, v_lo_623_, v_hi_624_);
lean_dec(v_hi_624_);
lean_dec(v_n_621_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_s_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_627_ = lean_array_mk(v_s_626_);
v___x_628_ = lean_array_get_size(v___x_627_);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_nat_dec_eq(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___y_634_; uint8_t v___x_638_; 
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_sub(v___x_628_, v___x_631_);
v___x_638_ = lean_nat_dec_le(v___x_629_, v___x_632_);
if (v___x_638_ == 0)
{
lean_inc(v___x_632_);
v___y_634_ = v___x_632_;
goto v___jp_633_;
}
else
{
v___y_634_ = v___x_629_;
goto v___jp_633_;
}
v___jp_633_:
{
uint8_t v___x_635_; 
v___x_635_ = lean_nat_dec_le(v___y_634_, v___x_632_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_dec(v___x_632_);
lean_inc(v___y_634_);
v___x_636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_628_, v___x_627_, v___y_634_, v___y_634_);
lean_dec(v___y_634_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_628_, v___x_627_, v___y_634_, v___x_632_);
lean_dec(v___x_632_);
return v___x_637_;
}
}
}
else
{
return v___x_627_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_keys_639_, lean_object* v_i_640_, lean_object* v_k_641_){
_start:
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_array_get_size(v_keys_639_);
v___x_643_ = lean_nat_dec_lt(v_i_640_, v___x_642_);
if (v___x_643_ == 0)
{
lean_dec(v_i_640_);
return v___x_643_;
}
else
{
lean_object* v_k_x27_644_; uint8_t v___x_645_; 
v_k_x27_644_ = lean_array_fget_borrowed(v_keys_639_, v_i_640_);
v___x_645_ = lean_name_eq(v_k_641_, v_k_x27_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_i_640_, v___x_646_);
lean_dec(v_i_640_);
v_i_640_ = v___x_647_;
goto _start;
}
else
{
lean_dec(v_i_640_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_649_, lean_object* v_i_650_, lean_object* v_k_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_649_, v_i_650_, v_k_651_);
lean_dec(v_k_651_);
lean_dec_ref(v_keys_649_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_654_, size_t v_x_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_es_657_; lean_object* v___x_658_; size_t v___x_659_; size_t v___x_660_; lean_object* v_j_661_; lean_object* v___x_662_; 
v_es_657_ = lean_ctor_get(v_x_654_, 0);
v___x_658_ = lean_box(2);
v___x_659_ = ((size_t)31ULL);
v___x_660_ = lean_usize_land(v_x_655_, v___x_659_);
v_j_661_ = lean_usize_to_nat(v___x_660_);
v___x_662_ = lean_array_get_borrowed(v___x_658_, v_es_657_, v_j_661_);
lean_dec(v_j_661_);
switch(lean_obj_tag(v___x_662_))
{
case 0:
{
lean_object* v_key_663_; uint8_t v___x_664_; 
v_key_663_ = lean_ctor_get(v___x_662_, 0);
v___x_664_ = lean_name_eq(v_x_656_, v_key_663_);
return v___x_664_;
}
case 1:
{
lean_object* v_node_665_; size_t v___x_666_; size_t v___x_667_; 
v_node_665_ = lean_ctor_get(v___x_662_, 0);
v___x_666_ = ((size_t)5ULL);
v___x_667_ = lean_usize_shift_right(v_x_655_, v___x_666_);
v_x_654_ = v_node_665_;
v_x_655_ = v___x_667_;
goto _start;
}
default: 
{
uint8_t v___x_669_; 
v___x_669_ = 0;
return v___x_669_;
}
}
}
else
{
lean_object* v_ks_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_ks_670_ = lean_ctor_get(v_x_654_, 0);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_ks_670_, v___x_671_, v_x_656_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
size_t v_x_476__boxed_676_; uint8_t v_res_677_; lean_object* v_r_678_; 
v_x_476__boxed_676_ = lean_unbox_usize(v_x_674_);
lean_dec(v_x_674_);
v_res_677_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_673_, v_x_476__boxed_676_, v_x_675_);
lean_dec(v_x_675_);
lean_dec_ref(v_x_673_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
uint64_t v___y_682_; 
if (lean_obj_tag(v_x_680_) == 0)
{
uint64_t v___x_685_; 
v___x_685_ = 1723ULL;
v___y_682_ = v___x_685_;
goto v___jp_681_;
}
else
{
uint64_t v_hash_686_; 
v_hash_686_ = lean_ctor_get_uint64(v_x_680_, sizeof(void*)*2);
v___y_682_ = v_hash_686_;
goto v___jp_681_;
}
v___jp_681_:
{
size_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_uint64_to_usize(v___y_682_);
v___x_684_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_679_, v___x_683_, v_x_680_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec_ref(v_x_687_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_x1_691_, lean_object* v_x2_692_){
_start:
{
lean_object* v_declName_693_; uint8_t v___x_694_; 
v_declName_693_ = lean_ctor_get(v_x2_692_, 0);
v___x_694_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x1_691_, v_declName_693_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; 
v___x_695_ = 1;
return v___x_695_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = 0;
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_x1_697_, lean_object* v_x2_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x1_697_, v_x2_698_);
lean_dec_ref(v_x2_698_);
lean_dec_ref(v_x1_697_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_x_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x_703_);
lean_dec_ref(v_x_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_));
v___x_733_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(lean_object* v_n_736_, lean_object* v_as_737_, lean_object* v_lo_738_, lean_object* v_hi_739_, lean_object* v_w_740_, lean_object* v_hlo_741_, lean_object* v_hhi_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_736_, v_as_737_, v_lo_738_, v_hi_739_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___boxed(lean_object* v_n_744_, lean_object* v_as_745_, lean_object* v_lo_746_, lean_object* v_hi_747_, lean_object* v_w_748_, lean_object* v_hlo_749_, lean_object* v_hhi_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(v_n_744_, v_as_745_, v_lo_746_, v_hi_747_, v_w_748_, v_hlo_749_, v_hhi_750_);
lean_dec(v_hi_747_);
lean_dec(v_n_744_);
return v_res_751_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(v_00_u03b2_756_, v_x_757_, v_x_758_);
lean_dec(v_x_758_);
lean_dec_ref(v_x_757_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_n_761_, lean_object* v_lo_762_, lean_object* v_hi_763_, lean_object* v_hhi_764_, lean_object* v_pivot_765_, lean_object* v_as_766_, lean_object* v_i_767_, lean_object* v_k_768_, lean_object* v_ilo_769_, lean_object* v_ik_770_, lean_object* v_w_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_763_, v_pivot_765_, v_as_766_, v_i_767_, v_k_768_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_n_773_, lean_object* v_lo_774_, lean_object* v_hi_775_, lean_object* v_hhi_776_, lean_object* v_pivot_777_, lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_k_780_, lean_object* v_ilo_781_, lean_object* v_ik_782_, lean_object* v_w_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(v_n_773_, v_lo_774_, v_hi_775_, v_hhi_776_, v_pivot_777_, v_as_778_, v_i_779_, v_k_780_, v_ilo_781_, v_ik_782_, v_w_783_);
lean_dec_ref(v_pivot_777_);
lean_dec(v_hi_775_);
lean_dec(v_lo_774_);
lean_dec(v_n_773_);
return v_res_784_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_785_, lean_object* v_x_786_, size_t v_x_787_, lean_object* v_x_788_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_786_, v_x_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
size_t v_x_651__boxed_794_; uint8_t v_res_795_; lean_object* v_r_796_; 
v_x_651__boxed_794_ = lean_unbox_usize(v_x_792_);
lean_dec(v_x_792_);
v_res_795_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_790_, v_x_791_, v_x_651__boxed_794_, v_x_793_);
lean_dec(v_x_793_);
lean_dec_ref(v_x_791_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03b2_797_, lean_object* v_keys_798_, lean_object* v_vals_799_, lean_object* v_heq_800_, lean_object* v_i_801_, lean_object* v_k_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_798_, v_i_801_, v_k_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_804_, lean_object* v_keys_805_, lean_object* v_vals_806_, lean_object* v_heq_807_, lean_object* v_i_808_, lean_object* v_k_809_){
_start:
{
uint8_t v_res_810_; lean_object* v_r_811_; 
v_res_810_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03b2_804_, v_keys_805_, v_vals_806_, v_heq_807_, v_i_808_, v_k_809_);
lean_dec(v_k_809_);
lean_dec_ref(v_vals_806_);
lean_dec_ref(v_keys_805_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(lean_object* v_env_812_, lean_object* v_type_813_){
_start:
{
if (lean_obj_tag(v_type_813_) == 7)
{
lean_object* v_body_814_; 
v_body_814_ = lean_ctor_get(v_type_813_, 2);
v_type_813_ = v_body_814_;
goto _start;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Expr_getAppFn(v_type_813_);
if (lean_obj_tag(v___x_816_) == 4)
{
lean_object* v_declName_817_; uint8_t v___x_818_; 
v_declName_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_declName_817_);
lean_dec_ref_known(v___x_816_, 2);
v___x_818_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_812_, v_declName_817_);
return v___x_818_;
}
else
{
uint8_t v___x_819_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v_env_812_);
v___x_819_ = 0;
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType___boxed(lean_object* v_env_820_, lean_object* v_type_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_820_, v_type_821_);
lean_dec_ref(v_type_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(lean_object* v_env_824_, lean_object* v_type_825_){
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
v___x_830_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_824_, v_declName_829_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType___boxed(lean_object* v_env_832_, lean_object* v_type_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_832_, v_type_833_);
lean_dec_ref(v_type_833_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(lean_object* v_upperBound_839_, lean_object* v___x_840_, lean_object* v_param_841_, lean_object* v_paramsInfo_842_, lean_object* v_a_843_, lean_object* v_b_844_){
_start:
{
lean_object* v_a_846_; uint8_t v___x_850_; 
v___x_850_ = lean_nat_dec_lt(v_a_843_, v_upperBound_839_);
if (v___x_850_ == 0)
{
lean_dec(v_a_843_);
lean_inc_ref(v_b_844_);
return v_b_844_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_861_; lean_object* v___x_864_; 
v___x_851_ = lean_box(0);
v___x_852_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0));
v___x_861_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default));
v___x_864_ = lean_array_get_borrowed(v___x_861_, v_paramsInfo_842_, v_a_843_);
switch(lean_obj_tag(v___x_864_))
{
case 0:
{
uint8_t v_weak_865_; 
v_weak_865_ = lean_ctor_get_uint8(v___x_864_, 0);
if (v_weak_865_ == 0)
{
goto v___jp_853_;
}
else
{
goto v___jp_862_;
}
}
case 2:
{
goto v___jp_862_;
}
case 4:
{
goto v___jp_862_;
}
default: 
{
goto v___jp_853_;
}
}
v___jp_853_:
{
lean_object* v___x_854_; lean_object* v_type_855_; lean_object* v_fvarId_856_; uint8_t v___x_857_; 
v___x_854_ = lean_array_fget_borrowed(v___x_840_, v_a_843_);
v_type_855_ = lean_ctor_get(v___x_854_, 2);
v_fvarId_856_ = lean_ctor_get(v_param_841_, 0);
v___x_857_ = l_Lean_Expr_containsFVar(v_type_855_, v_fvarId_856_);
if (v___x_857_ == 0)
{
v_a_846_ = v___x_852_;
goto v___jp_845_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v_a_843_);
v___x_858_ = lean_box(v___x_850_);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_851_);
return v___x_860_;
}
}
v___jp_862_:
{
lean_object* v___x_863_; 
v___x_863_ = lean_array_get_borrowed(v___x_861_, v_paramsInfo_842_, v_a_843_);
if (lean_obj_tag(v___x_863_) == 0)
{
goto v___jp_853_;
}
else
{
v_a_846_ = v___x_852_;
goto v___jp_845_;
}
}
}
v___jp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_add(v_a_843_, v___x_847_);
lean_dec(v_a_843_);
v_a_843_ = v___x_848_;
v_b_844_ = v_a_846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___boxed(lean_object* v_upperBound_866_, lean_object* v___x_867_, lean_object* v_param_868_, lean_object* v_paramsInfo_869_, lean_object* v_a_870_, lean_object* v_b_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v_upperBound_866_, v___x_867_, v_param_868_, v_paramsInfo_869_, v_a_870_, v_b_871_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_paramsInfo_869_);
lean_dec_ref(v_param_868_);
lean_dec_ref(v___x_867_);
lean_dec(v_upperBound_866_);
return v_res_872_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0(void){
_start:
{
uint8_t v___x_873_; lean_object* v___x_874_; 
v___x_873_ = 0;
v___x_874_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(lean_object* v_decl_875_, lean_object* v_paramsInfo_876_, lean_object* v_j_877_){
_start:
{
lean_object* v_toSignature_878_; lean_object* v_params_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_param_885_; lean_object* v___x_886_; lean_object* v_fst_887_; 
v_toSignature_878_ = lean_ctor_get(v_decl_875_, 0);
v_params_879_ = lean_ctor_get(v_toSignature_878_, 3);
v___x_880_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0, &l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0);
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_add(v_j_877_, v___x_881_);
v___x_883_ = lean_array_get_size(v_params_879_);
v___x_884_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0));
v_param_885_ = lean_array_get_borrowed(v___x_880_, v_params_879_, v_j_877_);
v___x_886_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_883_, v_params_879_, v_param_885_, v_paramsInfo_876_, v___x_882_, v___x_884_);
v_fst_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_fst_887_);
lean_dec_ref(v___x_886_);
if (lean_obj_tag(v_fst_887_) == 0)
{
uint8_t v___x_888_; 
v___x_888_ = 0;
return v___x_888_;
}
else
{
lean_object* v_val_889_; uint8_t v___x_890_; 
v_val_889_ = lean_ctor_get(v_fst_887_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v_fst_887_, 1);
v___x_890_ = lean_unbox(v_val_889_);
lean_dec(v_val_889_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___boxed(lean_object* v_decl_891_, lean_object* v_paramsInfo_892_, lean_object* v_j_893_){
_start:
{
uint8_t v_res_894_; lean_object* v_r_895_; 
v_res_894_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v_decl_891_, v_paramsInfo_892_, v_j_893_);
lean_dec(v_j_893_);
lean_dec_ref(v_paramsInfo_892_);
lean_dec_ref(v_decl_891_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(lean_object* v_upperBound_896_, lean_object* v___x_897_, lean_object* v_param_898_, lean_object* v_paramsInfo_899_, lean_object* v_inst_900_, lean_object* v_R_901_, lean_object* v_a_902_, lean_object* v_b_903_, lean_object* v_c_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v_upperBound_896_, v___x_897_, v_param_898_, v_paramsInfo_899_, v_a_902_, v_b_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___boxed(lean_object* v_upperBound_906_, lean_object* v___x_907_, lean_object* v_param_908_, lean_object* v_paramsInfo_909_, lean_object* v_inst_910_, lean_object* v_R_911_, lean_object* v_a_912_, lean_object* v_b_913_, lean_object* v_c_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(v_upperBound_906_, v___x_907_, v_param_908_, v_paramsInfo_909_, v_inst_910_, v_R_911_, v_a_912_, v_b_913_, v_c_914_);
lean_dec_ref(v_b_913_);
lean_dec_ref(v_paramsInfo_909_);
lean_dec_ref(v_param_908_);
lean_dec_ref(v___x_907_);
lean_dec(v_upperBound_906_);
return v_res_915_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0(void){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_instMonadEIO(lean_box(0));
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_toApplicative_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_960_; 
v___x_925_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0, &l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0);
v___x_926_ = l_StateRefT_x27_instMonad___redArg(v___x_925_);
v_toApplicative_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_926_, 1);
lean_dec(v_unused_961_);
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_960_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_toApplicative_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_960_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_toFunctor_931_; lean_object* v_toSeq_932_; lean_object* v_toSeqLeft_933_; lean_object* v_toSeqRight_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_958_; 
v_toFunctor_931_ = lean_ctor_get(v_toApplicative_927_, 0);
v_toSeq_932_ = lean_ctor_get(v_toApplicative_927_, 2);
v_toSeqLeft_933_ = lean_ctor_get(v_toApplicative_927_, 3);
v_toSeqRight_934_ = lean_ctor_get(v_toApplicative_927_, 4);
v_isSharedCheck_958_ = !lean_is_exclusive(v_toApplicative_927_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v_toApplicative_927_, 1);
lean_dec(v_unused_959_);
v___x_936_ = v_toApplicative_927_;
v_isShared_937_ = v_isSharedCheck_958_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_toSeqRight_934_);
lean_inc(v_toSeqLeft_933_);
lean_inc(v_toSeq_932_);
lean_inc(v_toFunctor_931_);
lean_dec(v_toApplicative_927_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_958_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___f_938_; lean_object* v___f_939_; lean_object* v___f_940_; lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___f_943_; lean_object* v___f_944_; lean_object* v___f_945_; lean_object* v___x_947_; 
v___f_938_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1));
v___f_939_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2));
lean_inc_ref(v_toFunctor_931_);
v___f_940_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_940_, 0, v_toFunctor_931_);
v___f_941_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_941_, 0, v_toFunctor_931_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___f_940_);
lean_ctor_set(v___x_942_, 1, v___f_941_);
v___f_943_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_943_, 0, v_toSeqRight_934_);
v___f_944_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_944_, 0, v_toSeqLeft_933_);
v___f_945_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_945_, 0, v_toSeq_932_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 4, v___f_943_);
lean_ctor_set(v___x_936_, 3, v___f_944_);
lean_ctor_set(v___x_936_, 2, v___f_945_);
lean_ctor_set(v___x_936_, 1, v___f_938_);
lean_ctor_set(v___x_936_, 0, v___x_942_);
v___x_947_ = v___x_936_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___f_938_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v___f_945_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v___f_944_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v___f_943_);
v___x_947_ = v_reuseFailAlloc_957_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___f_939_);
lean_ctor_set(v___x_929_, 0, v___x_947_);
v___x_949_ = v___x_929_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___f_939_);
v___x_949_ = v_reuseFailAlloc_956_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___f_953_; lean_object* v___x_9155__overap_954_; lean_object* v___x_955_; 
v___x_950_ = l_StateRefT_x27_instMonad___redArg(v___x_949_);
v___x_951_ = lean_box(0);
v___x_952_ = l_instInhabitedOfMonad___redArg(v___x_950_, v___x_951_);
v___f_953_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_953_, 0, v___x_952_);
v___x_9155__overap_954_ = lean_panic_fn_borrowed(v___f_953_, v_msg_919_);
lean_dec_ref(v___f_953_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
v___x_955_ = lean_apply_5(v___x_9155__overap_954_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, lean_box(0));
return v___x_955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___boxed(lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v_msg_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(lean_object* v_alreadySpecialized_969_, size_t v_sz_970_, size_t v_i_971_, lean_object* v_bs_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_lt(v_i_971_, v_sz_970_);
if (v___x_973_ == 0)
{
return v_bs_972_;
}
else
{
lean_object* v_v_974_; lean_object* v_toSignature_975_; lean_object* v_name_976_; lean_object* v_params_977_; lean_object* v___x_978_; lean_object* v_bs_x27_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v_v_974_ = lean_array_uget_borrowed(v_bs_972_, v_i_971_);
v_toSignature_975_ = lean_ctor_get(v_v_974_, 0);
v_name_976_ = lean_ctor_get(v_toSignature_975_, 0);
lean_inc(v_name_976_);
v_params_977_ = lean_ctor_get(v_toSignature_975_, 3);
lean_inc_ref(v_params_977_);
v___x_978_ = lean_unsigned_to_nat(0u);
v_bs_x27_979_ = lean_array_uset(v_bs_972_, v_i_971_, v___x_978_);
v___x_980_ = 0;
v___x_981_ = lean_usize_to_nat(v_i_971_);
v___x_982_ = lean_array_get_size(v_params_977_);
lean_dec_ref(v_params_977_);
v___x_983_ = lean_box(4);
v___x_984_ = lean_mk_array(v___x_982_, v___x_983_);
v___x_985_ = lean_box(v___x_980_);
v___x_986_ = lean_array_get(v___x_985_, v_alreadySpecialized_969_, v___x_981_);
lean_dec(v___x_981_);
lean_dec(v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_987_, 0, v_name_976_);
lean_ctor_set(v___x_987_, 1, v___x_984_);
v___x_988_ = lean_unbox(v___x_986_);
lean_dec(v___x_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*2, v___x_988_);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_add(v_i_971_, v___x_989_);
v___x_991_ = lean_array_uset(v_bs_x27_979_, v_i_971_, v___x_987_);
v_i_971_ = v___x_990_;
v_bs_972_ = v___x_991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg___boxed(lean_object* v_alreadySpecialized_993_, lean_object* v_sz_994_, lean_object* v_i_995_, lean_object* v_bs_996_){
_start:
{
size_t v_sz_boxed_997_; size_t v_i_boxed_998_; lean_object* v_res_999_; 
v_sz_boxed_997_ = lean_unbox_usize(v_sz_994_);
lean_dec(v_sz_994_);
v_i_boxed_998_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_993_, v_sz_boxed_997_, v_i_boxed_998_, v_bs_996_);
lean_dec_ref(v_alreadySpecialized_993_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(lean_object* v_b_1000_, lean_object* v_info_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_array_push(v_b_1000_, v_info_1001_);
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0___boxed(lean_object* v_b_1010_, lean_object* v_info_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1010_, v_info_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1(lean_object* v_a_1018_, lean_object* v_as_1019_, size_t v_i_1020_, size_t v_stop_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_usize_dec_eq(v_i_1020_, v_stop_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_array_uget_borrowed(v_as_1019_, v_i_1020_);
v___x_1024_ = lean_nat_dec_eq(v_a_1018_, v___x_1023_);
if (v___x_1024_ == 0)
{
size_t v___x_1025_; size_t v___x_1026_; 
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_add(v_i_1020_, v___x_1025_);
v_i_1020_ = v___x_1026_;
goto _start;
}
else
{
return v___x_1024_;
}
}
else
{
uint8_t v___x_1028_; 
v___x_1028_ = 0;
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1___boxed(lean_object* v_a_1029_, lean_object* v_as_1030_, lean_object* v_i_1031_, lean_object* v_stop_1032_){
_start:
{
size_t v_i_boxed_1033_; size_t v_stop_boxed_1034_; uint8_t v_res_1035_; lean_object* v_r_1036_; 
v_i_boxed_1033_ = lean_unbox_usize(v_i_1031_);
lean_dec(v_i_1031_);
v_stop_boxed_1034_ = lean_unbox_usize(v_stop_1032_);
lean_dec(v_stop_1032_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1(v_a_1029_, v_as_1030_, v_i_boxed_1033_, v_stop_boxed_1034_);
lean_dec_ref(v_as_1030_);
lean_dec(v_a_1029_);
v_r_1036_ = lean_box(v_res_1035_);
return v_r_1036_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(lean_object* v_as_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_get_size(v_as_1037_);
v___x_1041_ = lean_nat_dec_lt(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
return v___x_1041_;
}
else
{
if (v___x_1041_ == 0)
{
return v___x_1041_;
}
else
{
size_t v___x_1042_; size_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1042_ = ((size_t)0ULL);
v___x_1043_ = lean_usize_of_nat(v___x_1040_);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1_spec__1(v_a_1038_, v_as_1037_, v___x_1042_, v___x_1043_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___boxed(lean_object* v_as_1045_, lean_object* v_a_1046_){
_start:
{
uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_res_1047_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v_as_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_as_1045_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(lean_object* v_upperBound_1051_, lean_object* v___x_1052_, lean_object* v_autoSpecialize_1053_, lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v_a_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___y_1064_; uint8_t v___x_1086_; 
v___x_1086_ = lean_nat_dec_lt(v_a_1056_, v_upperBound_1051_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_dec(v_a_1056_);
lean_dec(v___x_1055_);
lean_dec(v___x_1054_);
lean_dec_ref(v_autoSpecialize_1053_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_b_1057_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_type_1090_; lean_object* v___x_1091_; 
v___x_1088_ = lean_st_ref_get(v___y_1061_);
v___x_1089_ = lean_array_fget_borrowed(v___x_1052_, v_a_1056_);
v_type_1090_ = lean_ctor_get(v___x_1089_, 2);
lean_inc_ref(v_type_1090_);
v___x_1091_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_1090_, v___y_1061_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_env_1093_; uint8_t v___y_1104_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v_env_1093_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_env_1093_);
lean_dec(v___x_1088_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___closed__0));
v___x_1118_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v___x_1117_, v_a_1056_);
v___y_1104_ = v___x_1118_;
goto v___jp_1103_;
}
else
{
lean_object* v_val_1119_; uint8_t v___x_1120_; 
v_val_1119_ = lean_ctor_get(v___x_1055_, 0);
v___x_1120_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v_val_1119_, v_a_1056_);
v___y_1104_ = v___x_1120_;
goto v___jp_1103_;
}
v___jp_1094_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_box(4);
v___x_1096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1057_, v___x_1095_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
v___y_1064_ = v___x_1096_;
goto v___jp_1063_;
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v_env_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1098_ = lean_st_ref_get(v___y_1061_);
v_env_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_ref(v_env_1099_);
lean_dec(v___x_1098_);
v___x_1100_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_1099_, v_type_1090_);
v___x_1101_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1101_, 0, v___x_1100_);
v___x_1102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1057_, v___x_1101_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
v___y_1064_ = v___x_1102_;
goto v___jp_1063_;
}
v___jp_1103_:
{
if (v___y_1104_ == 0)
{
uint8_t v___x_1105_; 
v___x_1105_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_1093_, v_type_1090_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; 
lean_inc_ref(v_type_1090_);
v___x_1106_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_1090_);
if (v___x_1106_ == 0)
{
if (lean_obj_tag(v_a_1092_) == 0)
{
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
lean_inc_ref(v_autoSpecialize_1053_);
lean_inc(v___x_1055_);
lean_inc(v___x_1054_);
v___x_1107_ = lean_apply_2(v_autoSpecialize_1053_, v___x_1054_, v___x_1055_);
v___x_1108_ = lean_unbox(v___x_1107_);
if (v___x_1108_ == 0)
{
goto v___jp_1094_;
}
else
{
if (lean_obj_tag(v_type_1090_) == 7)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_box(1);
v___x_1110_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1057_, v___x_1109_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
v___y_1064_ = v___x_1110_;
goto v___jp_1063_;
}
else
{
goto v___jp_1094_;
}
}
}
else
{
goto v___jp_1097_;
}
}
else
{
lean_dec_ref_known(v_a_1092_, 1);
goto v___jp_1097_;
}
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_a_1092_);
v___x_1111_ = lean_box(2);
v___x_1112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1057_, v___x_1111_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
v___y_1064_ = v___x_1112_;
goto v___jp_1063_;
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v_a_1092_);
v___x_1113_ = lean_box(4);
v___x_1114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1057_, v___x_1113_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
v___y_1064_ = v___x_1114_;
goto v___jp_1063_;
}
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec_ref(v_env_1093_);
lean_dec(v_a_1092_);
v___x_1115_ = lean_box(3);
v___x_1116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___lam__0(v_b_1057_, v___x_1115_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
v___y_1064_ = v___x_1116_;
goto v___jp_1063_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v___x_1088_);
lean_dec_ref(v_b_1057_);
lean_dec(v_a_1056_);
lean_dec(v___x_1055_);
lean_dec(v___x_1054_);
lean_dec_ref(v_autoSpecialize_1053_);
v_a_1121_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1091_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1091_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
v___jp_1063_:
{
if (lean_obj_tag(v___y_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1077_; 
v_a_1065_ = lean_ctor_get(v___y_1064_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___y_1064_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1067_ = v___y_1064_;
v_isShared_1068_ = v_isSharedCheck_1077_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___y_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1077_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
if (lean_obj_tag(v_a_1065_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; 
lean_dec(v_a_1056_);
lean_dec(v___x_1055_);
lean_dec(v___x_1054_);
lean_dec_ref(v_autoSpecialize_1053_);
v_a_1069_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v_a_1065_, 1);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v_a_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_del_object(v___x_1067_);
v_a_1073_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v_a_1065_, 1);
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = lean_nat_add(v_a_1056_, v___x_1074_);
lean_dec(v_a_1056_);
v_a_1056_ = v___x_1075_;
v_b_1057_ = v_a_1073_;
goto _start;
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_a_1056_);
lean_dec(v___x_1055_);
lean_dec(v___x_1054_);
lean_dec_ref(v_autoSpecialize_1053_);
v_a_1078_ = lean_ctor_get(v___y_1064_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___y_1064_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___y_1064_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___y_1064_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg___boxed(lean_object* v_upperBound_1129_, lean_object* v___x_1130_, lean_object* v_autoSpecialize_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(v_upperBound_1129_, v___x_1130_, v_autoSpecialize_1131_, v___x_1132_, v___x_1133_, v_a_1134_, v_b_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec_ref(v___x_1130_);
lean_dec(v_upperBound_1129_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(lean_object* v_autoSpecialize_1142_, lean_object* v_as_1143_, size_t v_sz_1144_, size_t v_i_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_a_1153_; uint8_t v___x_1157_; 
v___x_1157_ = lean_usize_dec_lt(v_i_1145_, v_sz_1144_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
lean_dec_ref(v_autoSpecialize_1142_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_b_1146_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; lean_object* v_env_1160_; lean_object* v_a_1161_; lean_object* v_toSignature_1162_; lean_object* v_name_1163_; lean_object* v_params_1164_; uint8_t v___x_1165_; 
v___x_1159_ = lean_st_ref_get(v___y_1150_);
v_env_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc_ref(v_env_1160_);
lean_dec(v___x_1159_);
v_a_1161_ = lean_array_uget_borrowed(v_as_1143_, v_i_1145_);
v_toSignature_1162_ = lean_ctor_get(v_a_1161_, 0);
v_name_1163_ = lean_ctor_get(v_toSignature_1162_, 0);
v_params_1164_ = lean_ctor_get(v_toSignature_1162_, 3);
lean_inc(v_name_1163_);
v___x_1165_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1160_, v_name_1163_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v_env_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1166_ = lean_st_ref_get(v___y_1150_);
v_env_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc_ref(v_env_1167_);
lean_dec(v___x_1166_);
v___x_1168_ = lean_array_get_size(v_params_1164_);
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
lean_inc_n(v_name_1163_, 2);
v___x_1171_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_1167_, v_name_1163_);
lean_inc_ref(v_autoSpecialize_1142_);
v___x_1172_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(v___x_1168_, v_params_1164_, v_autoSpecialize_1142_, v_name_1163_, v___x_1171_, v___x_1169_, v___x_1170_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = lean_array_push(v_b_1146_, v_a_1173_);
v_a_1153_ = v___x_1174_;
goto v___jp_1152_;
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_b_1146_);
lean_dec_ref(v_autoSpecialize_1142_);
v_a_1175_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1172_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1172_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1183_ = lean_array_get_size(v_params_1164_);
v___x_1184_ = lean_box(4);
v___x_1185_ = lean_mk_array(v___x_1183_, v___x_1184_);
v___x_1186_ = lean_array_push(v_b_1146_, v___x_1185_);
v_a_1153_ = v___x_1186_;
goto v___jp_1152_;
}
}
v___jp_1152_:
{
size_t v___x_1154_; size_t v___x_1155_; 
v___x_1154_ = ((size_t)1ULL);
v___x_1155_ = lean_usize_add(v_i_1145_, v___x_1154_);
v_i_1145_ = v___x_1155_;
v_b_1146_ = v_a_1153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3___boxed(lean_object* v_autoSpecialize_1187_, lean_object* v_as_1188_, lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1187_, v_as_1188_, v_sz_boxed_1197_, v_i_boxed_1198_, v_b_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_as_1188_);
return v_res_1199_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(lean_object* v_as_1200_, size_t v_i_1201_, size_t v_stop_1202_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_usize_dec_eq(v_i_1201_, v_stop_1202_);
if (v___x_1207_ == 0)
{
uint8_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = 1;
v___x_1209_ = lean_array_uget_borrowed(v_as_1200_, v_i_1201_);
switch(lean_obj_tag(v___x_1209_))
{
case 0:
{
uint8_t v_weak_1210_; 
v_weak_1210_ = lean_ctor_get_uint8(v___x_1209_, 0);
if (v_weak_1210_ == 0)
{
return v___x_1208_;
}
else
{
goto v___jp_1203_;
}
}
case 2:
{
goto v___jp_1203_;
}
case 4:
{
goto v___jp_1203_;
}
default: 
{
return v___x_1208_;
}
}
}
else
{
uint8_t v___x_1211_; 
v___x_1211_ = 0;
return v___x_1211_;
}
v___jp_1203_:
{
size_t v___x_1204_; size_t v___x_1205_; 
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = lean_usize_add(v_i_1201_, v___x_1204_);
v_i_1201_ = v___x_1205_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0___boxed(lean_object* v_as_1212_, lean_object* v_i_1213_, lean_object* v_stop_1214_){
_start:
{
size_t v_i_boxed_1215_; size_t v_stop_boxed_1216_; uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_i_boxed_1215_ = lean_unbox_usize(v_i_1213_);
lean_dec(v_i_1213_);
v_stop_boxed_1216_ = lean_unbox_usize(v_stop_1214_);
lean_dec(v_stop_1214_);
v_res_1217_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_as_1212_, v_i_boxed_1215_, v_stop_boxed_1216_);
lean_dec_ref(v_as_1212_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(lean_object* v_as_1219_, size_t v_i_1220_, size_t v_stop_1221_){
_start:
{
uint8_t v___x_1226_; 
v___x_1226_ = lean_usize_dec_eq(v_i_1220_, v_stop_1221_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1227_ = lean_array_uget_borrowed(v_as_1219_, v_i_1220_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_array_get_size(v___x_1227_);
v___x_1230_ = lean_nat_dec_lt(v___x_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
goto v___jp_1222_;
}
else
{
if (v___x_1230_ == 0)
{
goto v___jp_1222_;
}
else
{
size_t v___x_1231_; size_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = lean_usize_of_nat(v___x_1229_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v___x_1227_, v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
goto v___jp_1222_;
}
else
{
return v___x_1233_;
}
}
}
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
return v___x_1234_;
}
v___jp_1222_:
{
size_t v___x_1223_; size_t v___x_1224_; 
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_add(v_i_1220_, v___x_1223_);
v_i_1220_ = v___x_1224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5___boxed(lean_object* v_as_1235_, lean_object* v_i_1236_, lean_object* v_stop_1237_){
_start:
{
size_t v_i_boxed_1238_; size_t v_stop_boxed_1239_; uint8_t v_res_1240_; lean_object* v_r_1241_; 
v_i_boxed_1238_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_stop_boxed_1239_ = lean_unbox_usize(v_stop_1237_);
lean_dec(v_stop_1237_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_as_1235_, v_i_boxed_1238_, v_stop_boxed_1239_);
lean_dec_ref(v_as_1235_);
v_r_1241_ = lean_box(v_res_1240_);
return v_r_1241_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(lean_object* v_as_1242_, lean_object* v_bs_1243_, lean_object* v_i_1244_, lean_object* v_cs_1245_){
_start:
{
lean_object* v___y_1247_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_array_get_size(v_as_1242_);
v___x_1253_ = lean_nat_dec_lt(v_i_1244_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec(v_i_1244_);
return v_cs_1245_;
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_array_get_size(v_bs_1243_);
v___x_1255_ = lean_nat_dec_lt(v_i_1244_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v_i_1244_);
return v_cs_1245_;
}
else
{
lean_object* v_a_1256_; lean_object* v_b_1257_; uint8_t v___x_1258_; 
v_a_1256_ = lean_array_fget_borrowed(v_as_1242_, v_i_1244_);
v_b_1257_ = lean_array_fget_borrowed(v_bs_1243_, v_i_1244_);
v___x_1258_ = lean_unbox(v_b_1257_);
if (v___x_1258_ == 0)
{
if (lean_obj_tag(v_a_1256_) == 3)
{
v___y_1247_ = v_a_1256_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_box(4);
v___y_1247_ = v___x_1259_;
goto v___jp_1246_;
}
}
else
{
lean_inc(v_a_1256_);
v___y_1247_ = v_a_1256_;
goto v___jp_1246_;
}
}
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v_i_1244_, v___x_1248_);
lean_dec(v_i_1244_);
v___x_1250_ = lean_array_push(v_cs_1245_, v___y_1247_);
v_i_1244_ = v___x_1249_;
v_cs_1245_ = v___x_1250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6___boxed(lean_object* v_as_1260_, lean_object* v_bs_1261_, lean_object* v_i_1262_, lean_object* v_cs_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v_as_1260_, v_bs_1261_, v_i_1262_, v_cs_1263_);
lean_dec_ref(v_bs_1261_);
lean_dec_ref(v_as_1260_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(lean_object* v_upperBound_1265_, lean_object* v___x_1266_, lean_object* v_a_1267_, lean_object* v_b_1268_){
_start:
{
lean_object* v_a_1271_; uint8_t v___x_1275_; 
v___x_1275_ = lean_nat_dec_lt(v_a_1267_, v_upperBound_1265_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec(v_a_1267_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v_b_1268_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default));
v___x_1278_ = lean_array_get_borrowed(v___x_1277_, v_b_1268_, v_a_1267_);
if (lean_obj_tag(v___x_1278_) == 2)
{
uint8_t v___x_1279_; 
v___x_1279_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v___x_1266_, v_b_1268_, v_a_1267_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_box(4);
v___x_1281_ = lean_array_set(v_b_1268_, v_a_1267_, v___x_1280_);
v_a_1271_ = v___x_1281_;
goto v___jp_1270_;
}
else
{
v_a_1271_ = v_b_1268_;
goto v___jp_1270_;
}
}
else
{
v_a_1271_ = v_b_1268_;
goto v___jp_1270_;
}
}
v___jp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_add(v_a_1267_, v___x_1272_);
lean_dec(v_a_1267_);
v_a_1267_ = v___x_1273_;
v_b_1268_ = v_a_1271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg___boxed(lean_object* v_upperBound_1282_, lean_object* v___x_1283_, lean_object* v_a_1284_, lean_object* v_b_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1282_, v___x_1283_, v_a_1284_, v_b_1285_);
lean_dec_ref(v___x_1283_);
lean_dec(v_upperBound_1282_);
return v_res_1287_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Array_instInhabited(lean_box(0));
return v___x_1288_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3));
v___x_1293_ = lean_unsigned_to_nat(43u);
v___x_1294_ = lean_unsigned_to_nat(236u);
v___x_1295_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2));
v___x_1296_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1));
v___x_1297_ = l_mkPanicMessageWithDecl(v___x_1296_, v___x_1295_, v___x_1294_, v___x_1293_, v___x_1292_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(lean_object* v_upperBound_1298_, lean_object* v_decls_1299_, lean_object* v_alreadySpecialized_1300_, lean_object* v___x_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_b_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_a_1311_; uint8_t v___x_1315_; 
v___x_1315_ = lean_nat_dec_lt(v_a_1303_, v_upperBound_1298_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec(v_a_1303_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_b_1304_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; lean_object* v_toSignature_1318_; lean_object* v_name_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_array_fget_borrowed(v_decls_1299_, v_a_1303_);
v_toSignature_1318_ = lean_ctor_get(v___x_1317_, 0);
v_name_1319_ = lean_ctor_get(v_toSignature_1318_, 0);
v___x_1320_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1301_, v_name_1319_);
if (lean_obj_tag(v___x_1320_) == 1)
{
lean_object* v_val_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_val_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_val_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v___x_1322_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0);
v___x_1323_ = lean_array_get_borrowed(v___x_1322_, v_a_1302_, v_a_1303_);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1326_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v___x_1323_, v_val_1321_, v___x_1324_, v___x_1325_);
lean_dec(v_val_1321_);
v___x_1327_ = lean_array_get_size(v___x_1326_);
v___x_1328_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v___x_1327_, v___x_1317_, v___x_1324_, v___x_1326_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = 0;
v___x_1331_ = lean_box(v___x_1330_);
v___x_1332_ = lean_array_get(v___x_1331_, v_alreadySpecialized_1300_, v_a_1303_);
lean_dec(v___x_1331_);
lean_inc(v_name_1319_);
v___x_1333_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1333_, 0, v_name_1319_);
lean_ctor_set(v___x_1333_, 1, v_a_1329_);
v___x_1334_ = lean_unbox(v___x_1332_);
lean_dec(v___x_1332_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*2, v___x_1334_);
v___x_1335_ = lean_array_push(v_b_1304_, v___x_1333_);
v_a_1311_ = v___x_1335_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_b_1304_);
lean_dec(v_a_1303_);
v_a_1336_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1328_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1328_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec(v___x_1320_);
v___x_1344_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4);
v___x_1345_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v___x_1344_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_dec_ref_known(v___x_1345_, 1);
v_a_1311_ = v_b_1304_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v_b_1304_);
lean_dec(v_a_1303_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
v___jp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_unsigned_to_nat(1u);
v___x_1313_ = lean_nat_add(v_a_1303_, v___x_1312_);
lean_dec(v_a_1303_);
v_a_1303_ = v___x_1313_;
v_b_1304_ = v_a_1311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___boxed(lean_object* v_upperBound_1354_, lean_object* v_decls_1355_, lean_object* v_alreadySpecialized_1356_, lean_object* v___x_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_b_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1354_, v_decls_1355_, v_alreadySpecialized_1356_, v___x_1357_, v_a_1358_, v_a_1359_, v_b_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec_ref(v_a_1358_);
lean_dec(v___x_1357_);
lean_dec_ref(v_alreadySpecialized_1356_);
lean_dec_ref(v_decls_1355_);
lean_dec(v_upperBound_1354_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries(lean_object* v_decls_1369_, lean_object* v_autoSpecialize_1370_, lean_object* v_alreadySpecialized_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v_declsInfo_1378_; size_t v_sz_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v___x_1377_ = lean_unsigned_to_nat(0u);
v_declsInfo_1378_ = ((lean_object*)(l_Lean_Compiler_LCNF_computeSpecEntries___closed__0));
v_sz_1379_ = lean_array_size(v_decls_1369_);
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1370_, v_decls_1369_, v_sz_1379_, v___x_1380_, v_declsInfo_1378_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1399_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1399_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1399_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = lean_array_get_size(v_a_1382_);
v___x_1392_ = lean_nat_dec_lt(v___x_1377_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_dec(v_a_1382_);
goto v___jp_1386_;
}
else
{
if (v___x_1392_ == 0)
{
lean_dec(v_a_1382_);
goto v___jp_1386_;
}
else
{
size_t v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_usize_of_nat(v___x_1391_);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_a_1382_, v___x_1380_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_dec(v_a_1382_);
goto v___jp_1386_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_del_object(v___x_1384_);
v___x_1395_ = lean_array_get_size(v_decls_1369_);
v___x_1396_ = lean_mk_empty_array_with_capacity(v___x_1395_);
lean_inc_ref(v_decls_1369_);
v___x_1397_ = l_Lean_Compiler_LCNF_mkFixedParamsMap(v_decls_1369_);
v___x_1398_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v___x_1395_, v_decls_1369_, v_alreadySpecialized_1371_, v___x_1397_, v_a_1382_, v___x_1377_, v___x_1396_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1382_);
lean_dec(v___x_1397_);
lean_dec_ref(v_decls_1369_);
return v___x_1398_;
}
}
}
v___jp_1386_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1371_, v_sz_1379_, v___x_1380_, v_decls_1369_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_decls_1369_);
v_a_1400_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1381_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1381_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries___boxed(lean_object* v_decls_1408_, lean_object* v_autoSpecialize_1409_, lean_object* v_alreadySpecialized_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1408_, v_autoSpecialize_1409_, v_alreadySpecialized_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec_ref(v_alreadySpecialized_1410_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(lean_object* v_upperBound_1417_, lean_object* v___x_1418_, lean_object* v_autoSpecialize_1419_, lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v_inst_1422_, lean_object* v_R_1423_, lean_object* v_a_1424_, lean_object* v_b_1425_, lean_object* v_c_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___redArg(v_upperBound_1417_, v___x_1418_, v_autoSpecialize_1419_, v___x_1420_, v___x_1421_, v_a_1424_, v_b_1425_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___boxed(lean_object* v_upperBound_1433_, lean_object* v___x_1434_, lean_object* v_autoSpecialize_1435_, lean_object* v___x_1436_, lean_object* v___x_1437_, lean_object* v_inst_1438_, lean_object* v_R_1439_, lean_object* v_a_1440_, lean_object* v_b_1441_, lean_object* v_c_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_upperBound_1433_, v___x_1434_, v_autoSpecialize_1435_, v___x_1436_, v___x_1437_, v_inst_1438_, v_R_1439_, v_a_1440_, v_b_1441_, v_c_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec_ref(v___x_1434_);
lean_dec(v_upperBound_1433_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(lean_object* v_alreadySpecialized_1449_, lean_object* v_as_1450_, size_t v_sz_1451_, size_t v_i_1452_, lean_object* v_bs_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1449_, v_sz_1451_, v_i_1452_, v_bs_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___boxed(lean_object* v_alreadySpecialized_1455_, lean_object* v_as_1456_, lean_object* v_sz_1457_, lean_object* v_i_1458_, lean_object* v_bs_1459_){
_start:
{
size_t v_sz_boxed_1460_; size_t v_i_boxed_1461_; lean_object* v_res_1462_; 
v_sz_boxed_1460_ = lean_unbox_usize(v_sz_1457_);
lean_dec(v_sz_1457_);
v_i_boxed_1461_ = lean_unbox_usize(v_i_1458_);
lean_dec(v_i_1458_);
v_res_1462_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(v_alreadySpecialized_1455_, v_as_1456_, v_sz_boxed_1460_, v_i_boxed_1461_, v_bs_1459_);
lean_dec_ref(v_as_1456_);
lean_dec_ref(v_alreadySpecialized_1455_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(lean_object* v_upperBound_1463_, lean_object* v___x_1464_, lean_object* v_inst_1465_, lean_object* v_R_1466_, lean_object* v_a_1467_, lean_object* v_b_1468_, lean_object* v_c_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1463_, v___x_1464_, v_a_1467_, v_b_1468_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___boxed(lean_object* v_upperBound_1476_, lean_object* v___x_1477_, lean_object* v_inst_1478_, lean_object* v_R_1479_, lean_object* v_a_1480_, lean_object* v_b_1481_, lean_object* v_c_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(v_upperBound_1476_, v___x_1477_, v_inst_1478_, v_R_1479_, v_a_1480_, v_b_1481_, v_c_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec_ref(v___x_1477_);
lean_dec(v_upperBound_1476_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(lean_object* v_upperBound_1489_, lean_object* v_decls_1490_, lean_object* v_alreadySpecialized_1491_, lean_object* v___x_1492_, lean_object* v_a_1493_, lean_object* v_inst_1494_, lean_object* v_R_1495_, lean_object* v_a_1496_, lean_object* v_b_1497_, lean_object* v_c_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1489_, v_decls_1490_, v_alreadySpecialized_1491_, v___x_1492_, v_a_1493_, v_a_1496_, v_b_1497_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___boxed(lean_object* v_upperBound_1505_, lean_object* v_decls_1506_, lean_object* v_alreadySpecialized_1507_, lean_object* v___x_1508_, lean_object* v_a_1509_, lean_object* v_inst_1510_, lean_object* v_R_1511_, lean_object* v_a_1512_, lean_object* v_b_1513_, lean_object* v_c_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(v_upperBound_1505_, v_decls_1506_, v_alreadySpecialized_1507_, v___x_1508_, v_a_1509_, v_inst_1510_, v_R_1511_, v_a_1512_, v_b_1513_, v_c_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec_ref(v_a_1509_);
lean_dec(v___x_1508_);
lean_dec_ref(v_alreadySpecialized_1507_);
lean_dec_ref(v_decls_1506_);
lean_dec(v_upperBound_1505_);
return v_res_1520_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1);
v___x_1525_ = lean_unsigned_to_nat(0u);
v___x_1526_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
lean_ctor_set(v___x_1526_, 2, v___x_1525_);
lean_ctor_set(v___x_1526_, 3, v___x_1525_);
lean_ctor_set(v___x_1526_, 4, v___x_1524_);
lean_ctor_set(v___x_1526_, 5, v___x_1524_);
lean_ctor_set(v___x_1526_, 6, v___x_1524_);
lean_ctor_set(v___x_1526_, 7, v___x_1524_);
lean_ctor_set(v___x_1526_, 8, v___x_1524_);
lean_ctor_set(v___x_1526_, 9, v___x_1524_);
lean_ctor_set(v___x_1526_, 10, v___x_1524_);
return v___x_1526_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1527_; double v___x_1528_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_float_of_nat(v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(lean_object* v_cls_1532_, lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_options_1539_; lean_object* v_ref_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_options_1539_ = lean_ctor_get(v___y_1536_, 1);
v_ref_1540_ = lean_ctor_get(v___y_1536_, 4);
v___x_1541_ = lean_st_ref_get(v___y_1537_);
v___x_1542_ = lean_st_ref_get(v___y_1535_);
v___x_1543_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1534_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1602_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1602_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1602_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_env_1548_; lean_object* v_lctx_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1600_; 
v_env_1548_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_ref(v_env_1548_);
lean_dec(v___x_1541_);
v_lctx_1549_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v___x_1542_, 1);
lean_dec(v_unused_1601_);
v___x_1551_ = v___x_1542_;
v_isShared_1552_ = v_isSharedCheck_1600_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_lctx_1549_);
lean_dec(v___x_1542_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1600_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v_traceState_1555_; lean_object* v_env_1556_; lean_object* v_nextMacroScope_1557_; lean_object* v_ngen_1558_; lean_object* v_auxDeclNGen_1559_; lean_object* v_cache_1560_; lean_object* v_messages_1561_; lean_object* v_infoState_1562_; lean_object* v_snapshotTasks_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1599_; 
v___x_1553_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2);
v___x_1554_ = lean_st_ref_take(v___y_1537_);
v_traceState_1555_ = lean_ctor_get(v___x_1554_, 4);
v_env_1556_ = lean_ctor_get(v___x_1554_, 0);
v_nextMacroScope_1557_ = lean_ctor_get(v___x_1554_, 1);
v_ngen_1558_ = lean_ctor_get(v___x_1554_, 2);
v_auxDeclNGen_1559_ = lean_ctor_get(v___x_1554_, 3);
v_cache_1560_ = lean_ctor_get(v___x_1554_, 5);
v_messages_1561_ = lean_ctor_get(v___x_1554_, 6);
v_infoState_1562_ = lean_ctor_get(v___x_1554_, 7);
v_snapshotTasks_1563_ = lean_ctor_get(v___x_1554_, 8);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1565_ = v___x_1554_;
v_isShared_1566_ = v_isSharedCheck_1599_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_snapshotTasks_1563_);
lean_inc(v_infoState_1562_);
lean_inc(v_messages_1561_);
lean_inc(v_cache_1560_);
lean_inc(v_traceState_1555_);
lean_inc(v_auxDeclNGen_1559_);
lean_inc(v_ngen_1558_);
lean_inc(v_nextMacroScope_1557_);
lean_inc(v_env_1556_);
lean_dec(v___x_1554_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1599_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
uint64_t v_tid_1567_; lean_object* v_traces_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1598_; 
v_tid_1567_ = lean_ctor_get_uint64(v_traceState_1555_, sizeof(void*)*1);
v_traces_1568_ = lean_ctor_get(v_traceState_1555_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_traceState_1555_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1570_ = v_traceState_1555_;
v_isShared_1571_ = v_isSharedCheck_1598_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_traces_1568_);
lean_dec(v_traceState_1555_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1598_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1572_ = lean_unbox(v_a_1544_);
lean_dec(v_a_1544_);
v___x_1573_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1549_, v___x_1572_);
lean_dec_ref(v_lctx_1549_);
lean_inc_ref(v_options_1539_);
v___x_1574_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1574_, 0, v_env_1548_);
lean_ctor_set(v___x_1574_, 1, v___x_1553_);
lean_ctor_set(v___x_1574_, 2, v___x_1573_);
lean_ctor_set(v___x_1574_, 3, v_options_1539_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 3);
lean_ctor_set(v___x_1551_, 1, v_msg_1533_);
lean_ctor_set(v___x_1551_, 0, v___x_1574_);
v___x_1576_ = v___x_1551_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_msg_1533_);
v___x_1576_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; double v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3);
v___x_1579_ = 0;
v___x_1580_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4));
v___x_1581_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1581_, 0, v_cls_1532_);
lean_ctor_set(v___x_1581_, 1, v___x_1577_);
lean_ctor_set(v___x_1581_, 2, v___x_1580_);
lean_ctor_set_float(v___x_1581_, sizeof(void*)*3, v___x_1578_);
lean_ctor_set_float(v___x_1581_, sizeof(void*)*3 + 8, v___x_1578_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*3 + 16, v___x_1579_);
v___x_1582_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5));
v___x_1583_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1576_);
lean_ctor_set(v___x_1583_, 2, v___x_1582_);
lean_inc(v_ref_1540_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v_ref_1540_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_PersistentArray_push___redArg(v_traces_1568_, v___x_1584_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1585_);
v___x_1587_ = v___x_1570_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1585_);
lean_ctor_set_uint64(v_reuseFailAlloc_1596_, sizeof(void*)*1, v_tid_1567_);
v___x_1587_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 4, v___x_1587_);
v___x_1589_ = v___x_1565_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_env_1556_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_nextMacroScope_1557_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_ngen_1558_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_auxDeclNGen_1559_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1595_, 5, v_cache_1560_);
lean_ctor_set(v_reuseFailAlloc_1595_, 6, v_messages_1561_);
lean_ctor_set(v_reuseFailAlloc_1595_, 7, v_infoState_1562_);
lean_ctor_set(v_reuseFailAlloc_1595_, 8, v_snapshotTasks_1563_);
v___x_1589_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = lean_st_ref_put(v___y_1537_, v___x_1589_);
v___x_1591_ = lean_box(0);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1591_);
v___x_1593_ = v___x_1546_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
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
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v___x_1542_);
lean_dec(v___x_1541_);
lean_dec_ref(v_msg_1533_);
lean_dec(v_cls_1532_);
v_a_1603_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1543_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1543_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___boxed(lean_object* v_cls_1611_, lean_object* v_msg_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v_cls_1611_, v_msg_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1618_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(lean_object* v_xs_1619_, lean_object* v_ys_1620_, lean_object* v_x_1621_){
_start:
{
lean_object* v_zero_1622_; uint8_t v_isZero_1623_; 
v_zero_1622_ = lean_unsigned_to_nat(0u);
v_isZero_1623_ = lean_nat_dec_eq(v_x_1621_, v_zero_1622_);
if (v_isZero_1623_ == 1)
{
lean_dec(v_x_1621_);
return v_isZero_1623_;
}
else
{
lean_object* v_one_1624_; lean_object* v_n_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v_one_1624_ = lean_unsigned_to_nat(1u);
v_n_1625_ = lean_nat_sub(v_x_1621_, v_one_1624_);
lean_dec(v_x_1621_);
v___x_1626_ = lean_array_fget_borrowed(v_xs_1619_, v_n_1625_);
v___x_1627_ = lean_array_fget_borrowed(v_ys_1620_, v_n_1625_);
v___x_1628_ = lean_nat_dec_eq(v___x_1626_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_dec(v_n_1625_);
return v___x_1628_;
}
else
{
v_x_1621_ = v_n_1625_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg___boxed(lean_object* v_xs_1630_, lean_object* v_ys_1631_, lean_object* v_x_1632_){
_start:
{
uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_res_1633_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1630_, v_ys_1631_, v_x_1632_);
lean_dec_ref(v_ys_1631_);
lean_dec_ref(v_xs_1630_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(lean_object* v_x_1635_, lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1635_) == 0)
{
if (lean_obj_tag(v_x_1636_) == 0)
{
uint8_t v___x_1637_; 
v___x_1637_ = 1;
return v___x_1637_;
}
else
{
uint8_t v___x_1638_; 
v___x_1638_ = 0;
return v___x_1638_;
}
}
else
{
if (lean_obj_tag(v_x_1636_) == 0)
{
uint8_t v___x_1639_; 
v___x_1639_ = 0;
return v___x_1639_;
}
else
{
lean_object* v_val_1640_; lean_object* v_val_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v_val_1640_ = lean_ctor_get(v_x_1635_, 0);
v_val_1641_ = lean_ctor_get(v_x_1636_, 0);
v___x_1642_ = lean_array_get_size(v_val_1640_);
v___x_1643_ = lean_array_get_size(v_val_1641_);
v___x_1644_ = lean_nat_dec_eq(v___x_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
return v___x_1644_;
}
else
{
uint8_t v___x_1645_; 
v___x_1645_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_val_1640_, v_val_1641_, v___x_1642_);
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0___boxed(lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_x_1646_, v_x_1647_);
lean_dec(v_x_1647_);
lean_dec(v_x_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(lean_object* v_x_1652_, lean_object* v_specArgs_x3f_1653_){
_start:
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0));
v___x_1655_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_specArgs_x3f_1653_, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed(lean_object* v_x_1656_, lean_object* v_specArgs_x3f_1657_){
_start:
{
uint8_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(v_x_1656_, v_specArgs_x3f_1657_);
lean_dec(v_specArgs_x3f_1657_);
lean_dec(v_x_1656_);
v_r_1659_ = lean_box(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
if (lean_obj_tag(v_a_1660_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = l_List_reverse___redArg(v_a_1661_);
return v___x_1662_;
}
else
{
lean_object* v_head_1663_; lean_object* v_tail_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1681_; 
v_head_1663_ = lean_ctor_get(v_a_1660_, 0);
v_tail_1664_ = lean_ctor_get(v_a_1660_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1666_ = v_a_1660_;
v_isShared_1667_ = v_isSharedCheck_1681_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_tail_1664_);
lean_inc(v_head_1663_);
lean_dec(v_a_1660_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1681_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___y_1669_; 
switch(lean_obj_tag(v_head_1663_))
{
case 0:
{
uint8_t v_weak_1674_; 
v_weak_1674_ = lean_ctor_get_uint8(v_head_1663_, 0);
lean_dec_ref_known(v_head_1663_, 0);
if (v_weak_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
v___y_1669_ = v___x_1675_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
v___y_1669_ = v___x_1676_;
goto v___jp_1668_;
}
}
case 1:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8);
v___y_1669_ = v___x_1677_;
goto v___jp_1668_;
}
case 2:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11);
v___y_1669_ = v___x_1678_;
goto v___jp_1668_;
}
case 3:
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14);
v___y_1669_ = v___x_1679_;
goto v___jp_1668_;
}
default: 
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17);
v___y_1669_ = v___x_1680_;
goto v___jp_1668_;
}
}
v___jp_1668_:
{
lean_object* v___x_1671_; 
lean_inc_ref(v___y_1669_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v_a_1661_);
lean_ctor_set(v___x_1666_, 0, v___y_1669_);
v___x_1671_ = v___x_1666_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___y_1669_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_a_1661_);
v___x_1671_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
v_a_1660_ = v_tail_1664_;
v_a_1661_ = v___x_1671_;
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
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1682_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0);
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
return v___x_1684_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_1697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7));
v___x_1698_ = l_Lean_Name_append(v___x_1697_, v___x_1696_);
return v___x_1698_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(lean_object* v_as_1702_, size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_a_1712_; uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_b_1705_);
return v___x_1717_;
}
else
{
lean_object* v_a_1718_; lean_object* v_declName_1719_; lean_object* v_paramsInfo_1720_; lean_object* v___x_1721_; lean_object* v___y_1723_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_a_1718_ = lean_array_uget_borrowed(v_as_1702_, v_i_1704_);
v_declName_1719_ = lean_ctor_get(v_a_1718_, 0);
v_paramsInfo_1720_ = lean_ctor_get(v_a_1718_, 1);
v___x_1721_ = lean_box(0);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = lean_array_get_size(v_paramsInfo_1720_);
v___x_1750_ = lean_nat_dec_lt(v___x_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
v_a_1712_ = v___x_1721_;
goto v___jp_1711_;
}
else
{
if (v___x_1750_ == 0)
{
v_a_1712_ = v___x_1721_;
goto v___jp_1711_;
}
else
{
size_t v___x_1751_; size_t v___x_1752_; uint8_t v___x_1753_; 
v___x_1751_ = ((size_t)0ULL);
v___x_1752_ = lean_usize_of_nat(v___x_1749_);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_paramsInfo_1720_, v___x_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
v_a_1712_ = v___x_1721_;
goto v___jp_1711_;
}
else
{
lean_object* v_options_1754_; uint8_t v_hasTrace_1755_; 
v_options_1754_ = lean_ctor_get(v___y_1708_, 1);
v_hasTrace_1755_ = lean_ctor_get_uint8(v_options_1754_, sizeof(void*)*1);
if (v_hasTrace_1755_ == 0)
{
v___y_1723_ = v___y_1709_;
goto v___jp_1722_;
}
else
{
lean_object* v_toCold_1756_; lean_object* v_inheritedTraceOptions_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_toCold_1756_ = lean_ctor_get(v___y_1708_, 0);
v_inheritedTraceOptions_1757_ = lean_ctor_get(v_toCold_1756_, 4);
v___x_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_1759_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8);
v___x_1760_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1757_, v_options_1754_, v___x_1759_);
if (v___x_1760_ == 0)
{
v___y_1723_ = v___y_1709_;
goto v___jp_1722_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_inc(v_declName_1719_);
v___x_1761_ = l_Lean_MessageData_ofName(v_declName_1719_);
v___x_1762_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
lean_inc_ref(v_paramsInfo_1720_);
v___x_1764_ = lean_array_to_list(v_paramsInfo_1720_);
v___x_1765_ = lean_box(0);
v___x_1766_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(v___x_1764_, v___x_1765_);
v___x_1767_ = l_Lean_MessageData_ofList(v___x_1766_);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1763_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v___x_1758_, v___x_1768_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_dec_ref_known(v___x_1769_, 1);
v___y_1723_ = v___y_1709_;
goto v___jp_1722_;
}
else
{
return v___x_1769_;
}
}
}
}
}
}
v___jp_1722_:
{
lean_object* v___x_1724_; lean_object* v_env_1725_; lean_object* v_nextMacroScope_1726_; lean_object* v_ngen_1727_; lean_object* v_auxDeclNGen_1728_; lean_object* v_traceState_1729_; lean_object* v_messages_1730_; lean_object* v_infoState_1731_; lean_object* v_snapshotTasks_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1746_; 
v___x_1724_ = lean_st_ref_take(v___y_1723_);
v_env_1725_ = lean_ctor_get(v___x_1724_, 0);
v_nextMacroScope_1726_ = lean_ctor_get(v___x_1724_, 1);
v_ngen_1727_ = lean_ctor_get(v___x_1724_, 2);
v_auxDeclNGen_1728_ = lean_ctor_get(v___x_1724_, 3);
v_traceState_1729_ = lean_ctor_get(v___x_1724_, 4);
v_messages_1730_ = lean_ctor_get(v___x_1724_, 6);
v_infoState_1731_ = lean_ctor_get(v___x_1724_, 7);
v_snapshotTasks_1732_ = lean_ctor_get(v___x_1724_, 8);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1724_, 5);
lean_dec(v_unused_1747_);
v___x_1734_ = v___x_1724_;
v_isShared_1735_ = v_isSharedCheck_1746_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snapshotTasks_1732_);
lean_inc(v_infoState_1731_);
lean_inc(v_messages_1730_);
lean_inc(v_traceState_1729_);
lean_inc(v_auxDeclNGen_1728_);
lean_inc(v_ngen_1727_);
lean_inc(v_nextMacroScope_1726_);
lean_inc(v_env_1725_);
lean_dec(v___x_1724_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1746_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v_toEnvExtension_1737_; lean_object* v_asyncMode_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1736_ = l_Lean_Compiler_LCNF_specExtension;
v_toEnvExtension_1737_ = lean_ctor_get(v___x_1736_, 0);
v_asyncMode_1738_ = lean_ctor_get(v_toEnvExtension_1737_, 2);
v___x_1739_ = lean_box(0);
lean_inc(v_a_1718_);
v___x_1740_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1736_, v_env_1725_, v_a_1718_, v_asyncMode_1738_, v___x_1739_);
v___x_1741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 5, v___x_1741_);
lean_ctor_set(v___x_1734_, 0, v___x_1740_);
v___x_1743_ = v___x_1734_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_nextMacroScope_1726_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_ngen_1727_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_auxDeclNGen_1728_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_traceState_1729_);
lean_ctor_set(v_reuseFailAlloc_1745_, 5, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1745_, 6, v_messages_1730_);
lean_ctor_set(v_reuseFailAlloc_1745_, 7, v_infoState_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 8, v_snapshotTasks_1732_);
v___x_1743_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_st_ref_put(v___y_1723_, v___x_1743_);
v_a_1712_ = v___x_1721_;
goto v___jp_1711_;
}
}
}
}
v___jp_1711_:
{
size_t v___x_1713_; size_t v___x_1714_; 
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1704_, v___x_1713_);
v_i_1704_ = v___x_1714_;
v_b_1705_ = v_a_1712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___boxed(lean_object* v_as_1770_, lean_object* v_sz_1771_, lean_object* v_i_1772_, lean_object* v_b_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
size_t v_sz_boxed_1779_; size_t v_i_boxed_1780_; lean_object* v_res_1781_; 
v_sz_boxed_1779_ = lean_unbox_usize(v_sz_1771_);
lean_dec(v_sz_1771_);
v_i_boxed_1780_ = lean_unbox_usize(v_i_1772_);
lean_dec(v_i_1772_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_as_1770_, v_sz_boxed_1779_, v_i_boxed_1780_, v_b_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v_as_1770_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries(lean_object* v_decls_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___f_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___f_1789_ = ((lean_object*)(l_Lean_Compiler_LCNF_saveSpecEntries___closed__0));
v___x_1790_ = lean_array_get_size(v_decls_1783_);
v___x_1791_ = 0;
v___x_1792_ = lean_box(v___x_1791_);
v___x_1793_ = lean_mk_array(v___x_1790_, v___x_1792_);
v___x_1794_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1783_, v___f_1789_, v___x_1793_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec_ref(v___x_1793_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; size_t v_sz_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = lean_box(0);
v_sz_1797_ = lean_array_size(v_a_1795_);
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_a_1795_, v_sz_1797_, v___x_1798_, v___x_1796_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1795_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v___x_1799_, 0);
lean_dec(v_unused_1807_);
v___x_1801_ = v___x_1799_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_dec(v___x_1799_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1796_);
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1796_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
return v___x_1799_;
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_a_1808_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1794_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1794_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___boxed(lean_object* v_decls_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Compiler_LCNF_saveSpecEntries(v_decls_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
return v_res_1822_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(lean_object* v_xs_1823_, lean_object* v_ys_1824_, lean_object* v_hsz_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1823_, v_ys_1824_, v_x_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___boxed(lean_object* v_xs_1829_, lean_object* v_ys_1830_, lean_object* v_hsz_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(v_xs_1829_, v_ys_1830_, v_hsz_1831_, v_x_1832_, v_x_1833_);
lean_dec_ref(v_ys_1830_);
lean_dec_ref(v_xs_1829_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(lean_object* v_as_1836_, lean_object* v_k_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v_m_1842_; lean_object* v_a_1843_; uint8_t v___x_1844_; 
v___x_1840_ = lean_nat_add(v_x_1838_, v_x_1839_);
v___x_1841_ = lean_unsigned_to_nat(1u);
v_m_1842_ = lean_nat_shiftr(v___x_1840_, v___x_1841_);
lean_dec(v___x_1840_);
v_a_1843_ = lean_array_fget_borrowed(v_as_1836_, v_m_1842_);
v___x_1844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_a_1843_, v_k_1837_);
if (v___x_1844_ == 0)
{
uint8_t v___x_1845_; 
lean_dec(v_x_1839_);
v___x_1845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_k_1837_, v_a_1843_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
lean_dec(v_m_1842_);
lean_dec(v_x_1838_);
lean_inc(v_a_1843_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_a_1843_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; uint8_t v___y_1851_; 
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_nat_dec_eq(v_m_1842_, v___x_1847_);
v___x_1849_ = lean_nat_sub(v_m_1842_, v___x_1841_);
lean_dec(v_m_1842_);
if (v___x_1848_ == 0)
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_nat_dec_lt(v___x_1849_, v_x_1838_);
v___y_1851_ = v___x_1854_;
goto v___jp_1850_;
}
else
{
v___y_1851_ = v___x_1848_;
goto v___jp_1850_;
}
v___jp_1850_:
{
if (v___y_1851_ == 0)
{
v_x_1839_ = v___x_1849_;
goto _start;
}
else
{
lean_object* v___x_1853_; 
lean_dec(v___x_1849_);
lean_dec(v_x_1838_);
v___x_1853_ = lean_box(0);
return v___x_1853_;
}
}
}
}
else
{
lean_object* v___x_1855_; uint8_t v___x_1856_; 
lean_dec(v_x_1838_);
v___x_1855_ = lean_nat_add(v_m_1842_, v___x_1841_);
lean_dec(v_m_1842_);
v___x_1856_ = lean_nat_dec_le(v___x_1855_, v_x_1839_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; 
lean_dec(v___x_1855_);
lean_dec(v_x_1839_);
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
else
{
v_x_1838_ = v___x_1855_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg___boxed(lean_object* v_as_1859_, lean_object* v_k_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v_as_1859_, v_k_1860_, v_x_1861_, v_x_1862_);
lean_dec_ref(v_k_1860_);
lean_dec_ref(v_as_1859_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1864_, lean_object* v_vals_1865_, lean_object* v_i_1866_, lean_object* v_k_1867_){
_start:
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = lean_array_get_size(v_keys_1864_);
v___x_1869_ = lean_nat_dec_lt(v_i_1866_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
lean_dec(v_i_1866_);
v___x_1870_ = lean_box(0);
return v___x_1870_;
}
else
{
lean_object* v_k_x27_1871_; uint8_t v___x_1872_; 
v_k_x27_1871_ = lean_array_fget_borrowed(v_keys_1864_, v_i_1866_);
v___x_1872_ = lean_name_eq(v_k_1867_, v_k_x27_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = lean_nat_add(v_i_1866_, v___x_1873_);
lean_dec(v_i_1866_);
v_i_1866_ = v___x_1874_;
goto _start;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_array_fget_borrowed(v_vals_1865_, v_i_1866_);
lean_dec(v_i_1866_);
lean_inc(v___x_1876_);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1878_, lean_object* v_vals_1879_, lean_object* v_i_1880_, lean_object* v_k_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1878_, v_vals_1879_, v_i_1880_, v_k_1881_);
lean_dec(v_k_1881_);
lean_dec_ref(v_vals_1879_);
lean_dec_ref(v_keys_1878_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_1883_, size_t v_x_1884_, lean_object* v_x_1885_){
_start:
{
if (lean_obj_tag(v_x_1883_) == 0)
{
lean_object* v_es_1886_; lean_object* v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; lean_object* v_j_1890_; lean_object* v___x_1891_; 
v_es_1886_ = lean_ctor_get(v_x_1883_, 0);
v___x_1887_ = lean_box(2);
v___x_1888_ = ((size_t)31ULL);
v___x_1889_ = lean_usize_land(v_x_1884_, v___x_1888_);
v_j_1890_ = lean_usize_to_nat(v___x_1889_);
v___x_1891_ = lean_array_get_borrowed(v___x_1887_, v_es_1886_, v_j_1890_);
lean_dec(v_j_1890_);
switch(lean_obj_tag(v___x_1891_))
{
case 0:
{
lean_object* v_key_1892_; lean_object* v_val_1893_; uint8_t v___x_1894_; 
v_key_1892_ = lean_ctor_get(v___x_1891_, 0);
v_val_1893_ = lean_ctor_get(v___x_1891_, 1);
v___x_1894_ = lean_name_eq(v_x_1885_, v_key_1892_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_box(0);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; 
lean_inc(v_val_1893_);
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_val_1893_);
return v___x_1896_;
}
}
case 1:
{
lean_object* v_node_1897_; size_t v___x_1898_; size_t v___x_1899_; 
v_node_1897_ = lean_ctor_get(v___x_1891_, 0);
v___x_1898_ = ((size_t)5ULL);
v___x_1899_ = lean_usize_shift_right(v_x_1884_, v___x_1898_);
v_x_1883_ = v_node_1897_;
v_x_1884_ = v___x_1899_;
goto _start;
}
default: 
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_box(0);
return v___x_1901_;
}
}
}
else
{
lean_object* v_ks_1902_; lean_object* v_vs_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_ks_1902_ = lean_ctor_get(v_x_1883_, 0);
v_vs_1903_ = lean_ctor_get(v_x_1883_, 1);
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1902_, v_vs_1903_, v___x_1904_, v_x_1885_);
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
size_t v_x_427__boxed_1909_; lean_object* v_res_1910_; 
v_x_427__boxed_1909_ = lean_unbox_usize(v_x_1907_);
lean_dec(v_x_1907_);
v_res_1910_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1906_, v_x_427__boxed_1909_, v_x_1908_);
lean_dec(v_x_1908_);
lean_dec_ref(v_x_1906_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
uint64_t v___y_1914_; 
if (lean_obj_tag(v_x_1912_) == 0)
{
uint64_t v___x_1917_; 
v___x_1917_ = 1723ULL;
v___y_1914_ = v___x_1917_;
goto v___jp_1913_;
}
else
{
uint64_t v_hash_1918_; 
v_hash_1918_ = lean_ctor_get_uint64(v_x_1912_, sizeof(void*)*2);
v___y_1914_ = v_hash_1918_;
goto v___jp_1913_;
}
v___jp_1913_:
{
size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_uint64_to_usize(v___y_1914_);
v___x_1916_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1911_, v___x_1915_, v_x_1912_);
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg___boxed(lean_object* v_x_1919_, lean_object* v_x_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_1919_, v_x_1920_);
lean_dec(v_x_1920_);
lean_dec_ref(v_x_1919_);
return v_res_1921_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v___x_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(lean_object* v_env_1925_, lean_object* v_declName_1926_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1936_; 
v___x_1927_ = lean_obj_once(&l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0, &l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0);
v___x_1928_ = l_Lean_Compiler_LCNF_specExtension;
v___x_1936_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1925_, v_declName_1926_);
if (lean_obj_tag(v___x_1936_) == 0)
{
goto v___jp_1929_;
}
else
{
lean_object* v_val_1937_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_val_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1951_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1927_, v___x_1928_, v_env_1925_, v_val_1937_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_array_get_size(v___x_1951_);
v___x_1954_ = lean_nat_dec_lt(v___x_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_dec_ref(v___x_1951_);
goto v___jp_1938_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1955_ = lean_unsigned_to_nat(1u);
v___x_1956_ = lean_nat_sub(v___x_1953_, v___x_1955_);
v___x_1957_ = lean_nat_dec_le(v___x_1952_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_dec(v___x_1956_);
lean_dec_ref(v___x_1951_);
goto v___jp_1938_;
}
else
{
lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1958_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1959_ = 0;
lean_inc(v_declName_1926_);
v___x_1960_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1960_, 0, v_declName_1926_);
lean_ctor_set(v___x_1960_, 1, v___x_1958_);
lean_ctor_set_uint8(v___x_1960_, sizeof(void*)*2, v___x_1959_);
v___x_1961_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_1951_, v___x_1960_, v___x_1952_, v___x_1956_);
lean_dec_ref_known(v___x_1960_, 2);
lean_dec_ref(v___x_1951_);
if (lean_obj_tag(v___x_1961_) == 0)
{
goto v___jp_1938_;
}
else
{
lean_dec(v_val_1937_);
lean_dec(v_declName_1926_);
lean_dec_ref(v_env_1925_);
return v___x_1961_;
}
}
}
v___jp_1938_:
{
uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1939_ = 0;
v___x_1940_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1927_, v___x_1928_, v_env_1925_, v_val_1937_, v___x_1939_);
lean_dec(v_val_1937_);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_array_get_size(v___x_1940_);
v___x_1943_ = lean_nat_dec_lt(v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_dec_ref(v___x_1940_);
goto v___jp_1929_;
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = lean_unsigned_to_nat(1u);
v___x_1945_ = lean_nat_sub(v___x_1942_, v___x_1944_);
v___x_1946_ = lean_nat_dec_le(v___x_1941_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_dec(v___x_1945_);
lean_dec_ref(v___x_1940_);
goto v___jp_1929_;
}
else
{
lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1947_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1948_ = 0;
lean_inc(v_declName_1926_);
v___x_1949_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1949_, 0, v_declName_1926_);
lean_ctor_set(v___x_1949_, 1, v___x_1947_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*2, v___x_1948_);
v___x_1950_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_1940_, v___x_1949_, v___x_1941_, v___x_1945_);
lean_dec_ref_known(v___x_1949_, 2);
lean_dec_ref(v___x_1940_);
if (lean_obj_tag(v___x_1950_) == 0)
{
goto v___jp_1929_;
}
else
{
lean_dec(v_declName_1926_);
lean_dec_ref(v_env_1925_);
return v___x_1950_;
}
}
}
}
}
v___jp_1929_:
{
lean_object* v_toEnvExtension_1930_; lean_object* v_asyncMode_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v_snd_1934_; lean_object* v___x_1935_; 
v_toEnvExtension_1930_ = lean_ctor_get(v___x_1928_, 0);
v_asyncMode_1931_ = lean_ctor_get(v_toEnvExtension_1930_, 2);
v___x_1932_ = lean_box(0);
v___x_1933_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1927_, v___x_1928_, v_env_1925_, v_asyncMode_1931_, v___x_1932_);
v_snd_1934_ = lean_ctor_get(v___x_1933_, 1);
lean_inc(v_snd_1934_);
lean_dec(v___x_1933_);
v___x_1935_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_snd_1934_, v_declName_1926_);
lean_dec(v_declName_1926_);
lean_dec(v_snd_1934_);
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(lean_object* v_00_u03b2_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_1963_, v_x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(v_00_u03b2_1966_, v_x_1967_, v_x_1968_);
lean_dec(v_x_1968_);
lean_dec_ref(v_x_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(lean_object* v_as_1970_, lean_object* v_k_1971_, lean_object* v_x_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v_as_1970_, v_k_1971_, v_x_1972_, v_x_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___boxed(lean_object* v_as_1976_, lean_object* v_k_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(v_as_1976_, v_k_1977_, v_x_1978_, v_x_1979_, v_x_1980_);
lean_dec_ref(v_k_1977_);
lean_dec_ref(v_as_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1982_, lean_object* v_x_1983_, size_t v_x_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1983_, v_x_1984_, v_x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
size_t v_x_588__boxed_1991_; lean_object* v_res_1992_; 
v_x_588__boxed_1991_ = lean_unbox_usize(v_x_1989_);
lean_dec(v_x_1989_);
v_res_1992_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(v_00_u03b2_1987_, v_x_1988_, v_x_588__boxed_1991_, v_x_1990_);
lean_dec(v_x_1990_);
lean_dec_ref(v_x_1988_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1993_, lean_object* v_keys_1994_, lean_object* v_vals_1995_, lean_object* v_heq_1996_, lean_object* v_i_1997_, lean_object* v_k_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1994_, v_vals_1995_, v_i_1997_, v_k_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2000_, lean_object* v_keys_2001_, lean_object* v_vals_2002_, lean_object* v_heq_2003_, lean_object* v_i_2004_, lean_object* v_k_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2000_, v_keys_2001_, v_vals_2002_, v_heq_2003_, v_i_2004_, v_k_2005_);
lean_dec(v_k_2005_);
lean_dec_ref(v_vals_2002_);
lean_dec_ref(v_keys_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0(lean_object* v_declName_2007_, lean_object* v_toPure_2008_, lean_object* v_____do__lift_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_2009_, v_declName_2007_);
v___x_2011_ = lean_apply_2(v_toPure_2008_, lean_box(0), v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_declName_2014_){
_start:
{
lean_object* v_toApplicative_2015_; lean_object* v_toBind_2016_; lean_object* v_getEnv_2017_; lean_object* v_toPure_2018_; lean_object* v___f_2019_; lean_object* v___x_2020_; 
v_toApplicative_2015_ = lean_ctor_get(v_inst_2012_, 0);
lean_inc_ref(v_toApplicative_2015_);
v_toBind_2016_ = lean_ctor_get(v_inst_2012_, 1);
lean_inc(v_toBind_2016_);
lean_dec_ref(v_inst_2012_);
v_getEnv_2017_ = lean_ctor_get(v_inst_2013_, 0);
lean_inc(v_getEnv_2017_);
lean_dec_ref(v_inst_2013_);
v_toPure_2018_ = lean_ctor_get(v_toApplicative_2015_, 1);
lean_inc(v_toPure_2018_);
lean_dec_ref(v_toApplicative_2015_);
v___f_2019_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2019_, 0, v_declName_2014_);
lean_closure_set(v___f_2019_, 1, v_toPure_2018_);
v___x_2020_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v_getEnv_2017_, v___f_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f(lean_object* v_m_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_declName_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(v_inst_2022_, v_inst_2023_, v_declName_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0(lean_object* v_declName_2026_, lean_object* v_toPure_2027_, lean_object* v_____do__lift_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_2028_, v_declName_2026_);
if (lean_obj_tag(v___x_2029_) == 0)
{
uint8_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = 0;
v___x_2031_ = lean_box(v___x_2030_);
v___x_2032_ = lean_apply_2(v_toPure_2027_, lean_box(0), v___x_2031_);
return v___x_2032_;
}
else
{
uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec_ref_known(v___x_2029_, 1);
v___x_2033_ = 1;
v___x_2034_ = lean_box(v___x_2033_);
v___x_2035_ = lean_apply_2(v_toPure_2027_, lean_box(0), v___x_2034_);
return v___x_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg(lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_declName_2038_){
_start:
{
lean_object* v_toApplicative_2039_; lean_object* v_toBind_2040_; lean_object* v_getEnv_2041_; lean_object* v_toPure_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; 
v_toApplicative_2039_ = lean_ctor_get(v_inst_2036_, 0);
lean_inc_ref(v_toApplicative_2039_);
v_toBind_2040_ = lean_ctor_get(v_inst_2036_, 1);
lean_inc(v_toBind_2040_);
lean_dec_ref(v_inst_2036_);
v_getEnv_2041_ = lean_ctor_get(v_inst_2037_, 0);
lean_inc(v_getEnv_2041_);
lean_dec_ref(v_inst_2037_);
v_toPure_2042_ = lean_ctor_get(v_toApplicative_2039_, 1);
lean_inc(v_toPure_2042_);
lean_dec_ref(v_toApplicative_2039_);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2043_, 0, v_declName_2038_);
lean_closure_set(v___f_2043_, 1, v_toPure_2042_);
v___x_2044_ = lean_apply_4(v_toBind_2040_, lean_box(0), lean_box(0), v_getEnv_2041_, v___f_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate(lean_object* v_m_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_declName_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Compiler_LCNF_isSpecCandidate___redArg(v_inst_2046_, v_inst_2047_, v_declName_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_2115_ = 0;
v___x_2116_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_));
v___x_2117_ = l_Lean_registerTraceClass(v___x_2114_, v___x_2115_, v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2____boxed(lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
return v_res_2119_;
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
