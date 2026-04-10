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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2;
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; 
v___x_335_ = ((size_t)5ULL);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_shift_left(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; 
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0);
v___x_340_ = lean_usize_sub(v___x_339_, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(lean_object* v_x_342_, size_t v_x_343_, size_t v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v_es_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; size_t v___x_351_; lean_object* v_j_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_es_347_ = lean_ctor_get(v_x_342_, 0);
v___x_348_ = ((size_t)5ULL);
v___x_349_ = ((size_t)1ULL);
v___x_350_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
v___x_351_ = lean_usize_land(v_x_343_, v___x_350_);
v_j_352_ = lean_usize_to_nat(v___x_351_);
v___x_353_ = lean_array_get_size(v_es_347_);
v___x_354_ = lean_nat_dec_lt(v_j_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_dec(v_j_352_);
lean_dec(v_x_346_);
lean_dec(v_x_345_);
return v_x_342_;
}
else
{
lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_391_; 
lean_inc_ref(v_es_347_);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_x_342_, 0);
lean_dec(v_unused_392_);
v___x_356_ = v_x_342_;
v_isShared_357_ = v_isSharedCheck_391_;
goto v_resetjp_355_;
}
else
{
lean_dec(v_x_342_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_391_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_v_358_; lean_object* v___x_359_; lean_object* v_xs_x27_360_; lean_object* v___y_362_; 
v_v_358_ = lean_array_fget(v_es_347_, v_j_352_);
v___x_359_ = lean_box(0);
v_xs_x27_360_ = lean_array_fset(v_es_347_, v_j_352_, v___x_359_);
switch(lean_obj_tag(v_v_358_))
{
case 0:
{
lean_object* v_key_367_; lean_object* v_val_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_378_; 
v_key_367_ = lean_ctor_get(v_v_358_, 0);
v_val_368_ = lean_ctor_get(v_v_358_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_v_358_);
if (v_isSharedCheck_378_ == 0)
{
v___x_370_ = v_v_358_;
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_val_368_);
lean_inc(v_key_367_);
lean_dec(v_v_358_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
uint8_t v___x_372_; 
v___x_372_ = lean_name_eq(v_x_345_, v_key_367_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_del_object(v___x_370_);
v___x_373_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_367_, v_val_368_, v_x_345_, v_x_346_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
v___y_362_ = v___x_374_;
goto v___jp_361_;
}
else
{
lean_object* v___x_376_; 
lean_dec(v_val_368_);
lean_dec(v_key_367_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v_x_346_);
lean_ctor_set(v___x_370_, 0, v_x_345_);
v___x_376_ = v___x_370_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_x_345_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_x_346_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v___y_362_ = v___x_376_;
goto v___jp_361_;
}
}
}
}
case 1:
{
lean_object* v_node_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_389_; 
v_node_379_ = lean_ctor_get(v_v_358_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_v_358_);
if (v_isSharedCheck_389_ == 0)
{
v___x_381_ = v_v_358_;
v_isShared_382_ = v_isSharedCheck_389_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_node_379_);
lean_dec(v_v_358_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_389_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_383_ = lean_usize_shift_right(v_x_343_, v___x_348_);
v___x_384_ = lean_usize_add(v_x_344_, v___x_349_);
v___x_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_node_379_, v___x_383_, v___x_384_, v_x_345_, v_x_346_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_385_);
v___x_387_ = v___x_381_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
v___y_362_ = v___x_387_;
goto v___jp_361_;
}
}
}
default: 
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_x_345_);
lean_ctor_set(v___x_390_, 1, v_x_346_);
v___y_362_ = v___x_390_;
goto v___jp_361_;
}
}
v___jp_361_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_array_fset(v_xs_x27_360_, v_j_352_, v___y_362_);
lean_dec(v_j_352_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_363_);
v___x_365_ = v___x_356_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
else
{
lean_object* v_ks_393_; lean_object* v_vs_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_414_; 
v_ks_393_ = lean_ctor_get(v_x_342_, 0);
v_vs_394_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_414_ == 0)
{
v___x_396_ = v_x_342_;
v_isShared_397_ = v_isSharedCheck_414_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_vs_394_);
lean_inc(v_ks_393_);
lean_dec(v_x_342_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_414_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_ks_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_vs_394_);
v___x_399_ = v_reuseFailAlloc_413_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v_newNode_400_; uint8_t v___y_402_; size_t v___x_408_; uint8_t v___x_409_; 
v_newNode_400_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v___x_399_, v_x_345_, v_x_346_);
v___x_408_ = ((size_t)7ULL);
v___x_409_ = lean_usize_dec_le(v___x_408_, v_x_344_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_400_);
v___x_411_ = lean_unsigned_to_nat(4u);
v___x_412_ = lean_nat_dec_lt(v___x_410_, v___x_411_);
lean_dec(v___x_410_);
v___y_402_ = v___x_412_;
goto v___jp_401_;
}
else
{
v___y_402_ = v___x_409_;
goto v___jp_401_;
}
v___jp_401_:
{
if (v___y_402_ == 0)
{
lean_object* v_ks_403_; lean_object* v_vs_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_ks_403_ = lean_ctor_get(v_newNode_400_, 0);
lean_inc_ref(v_ks_403_);
v_vs_404_ = lean_ctor_get(v_newNode_400_, 1);
lean_inc_ref(v_vs_404_);
lean_dec_ref(v_newNode_400_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2);
v___x_407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_x_344_, v_ks_403_, v_vs_404_, v___x_405_, v___x_406_);
lean_dec_ref(v_vs_404_);
lean_dec_ref(v_ks_403_);
return v___x_407_;
}
else
{
return v_newNode_400_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(size_t v_depth_415_, lean_object* v_keys_416_, lean_object* v_vals_417_, lean_object* v_i_418_, lean_object* v_entries_419_){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_array_get_size(v_keys_416_);
v___x_421_ = lean_nat_dec_lt(v_i_418_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec(v_i_418_);
return v_entries_419_;
}
else
{
lean_object* v_k_422_; lean_object* v_v_423_; uint64_t v___y_425_; 
v_k_422_ = lean_array_fget_borrowed(v_keys_416_, v_i_418_);
v_v_423_ = lean_array_fget_borrowed(v_vals_417_, v_i_418_);
if (lean_obj_tag(v_k_422_) == 0)
{
uint64_t v___x_436_; 
v___x_436_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_425_ = v___x_436_;
goto v___jp_424_;
}
else
{
uint64_t v_hash_437_; 
v_hash_437_ = lean_ctor_get_uint64(v_k_422_, sizeof(void*)*2);
v___y_425_ = v_hash_437_;
goto v___jp_424_;
}
v___jp_424_:
{
size_t v_h_426_; size_t v___x_427_; lean_object* v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v_h_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_h_426_ = lean_uint64_to_usize(v___y_425_);
v___x_427_ = ((size_t)5ULL);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_sub(v_depth_415_, v___x_429_);
v___x_431_ = lean_usize_mul(v___x_427_, v___x_430_);
v_h_432_ = lean_usize_shift_right(v_h_426_, v___x_431_);
v___x_433_ = lean_nat_add(v_i_418_, v___x_428_);
lean_dec(v_i_418_);
lean_inc(v_v_423_);
lean_inc(v_k_422_);
v___x_434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_entries_419_, v_h_432_, v_depth_415_, v_k_422_, v_v_423_);
v_i_418_ = v___x_433_;
v_entries_419_ = v___x_434_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_438_, lean_object* v_keys_439_, lean_object* v_vals_440_, lean_object* v_i_441_, lean_object* v_entries_442_){
_start:
{
size_t v_depth_boxed_443_; lean_object* v_res_444_; 
v_depth_boxed_443_ = lean_unbox_usize(v_depth_438_);
lean_dec(v_depth_438_);
v_res_444_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_boxed_443_, v_keys_439_, v_vals_440_, v_i_441_, v_entries_442_);
lean_dec_ref(v_vals_440_);
lean_dec_ref(v_keys_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
size_t v_x_379__boxed_450_; size_t v_x_380__boxed_451_; lean_object* v_res_452_; 
v_x_379__boxed_450_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_x_380__boxed_451_ = lean_unbox_usize(v_x_447_);
lean_dec(v_x_447_);
v_res_452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_445_, v_x_379__boxed_450_, v_x_380__boxed_451_, v_x_448_, v_x_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
uint64_t v___y_457_; 
if (lean_obj_tag(v_x_454_) == 0)
{
uint64_t v___x_461_; 
v___x_461_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_457_ = v___x_461_;
goto v___jp_456_;
}
else
{
uint64_t v_hash_462_; 
v_hash_462_ = lean_ctor_get_uint64(v_x_454_, sizeof(void*)*2);
v___y_457_ = v_hash_462_;
goto v___jp_456_;
}
v___jp_456_:
{
size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_uint64_to_usize(v___y_457_);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_453_, v___x_458_, v___x_459_, v_x_454_, v_x_455_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_SpecState_addEntry(lean_object* v_s_463_, lean_object* v_e_464_){
_start:
{
lean_object* v_declName_465_; lean_object* v___x_466_; 
v_declName_465_ = lean_ctor_get(v_e_464_, 0);
lean_inc(v_declName_465_);
v___x_466_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_s_463_, v_declName_465_, v_e_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0(lean_object* v_00_u03b2_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_x_468_, v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, size_t v_x_474_, size_t v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_473_, v_x_474_, v_x_475_, v_x_476_, v_x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
size_t v_x_576__boxed_485_; size_t v_x_577__boxed_486_; lean_object* v_res_487_; 
v_x_576__boxed_485_ = lean_unbox_usize(v_x_481_);
lean_dec(v_x_481_);
v_x_577__boxed_486_ = lean_unbox_usize(v_x_482_);
lean_dec(v_x_482_);
v_res_487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(v_00_u03b2_479_, v_x_480_, v_x_576__boxed_485_, v_x_577__boxed_486_, v_x_483_, v_x_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_488_, lean_object* v_n_489_, lean_object* v_k_490_, lean_object* v_v_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v_n_489_, v_k_490_, v_v_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_493_, size_t v_depth_494_, lean_object* v_keys_495_, lean_object* v_vals_496_, lean_object* v_heq_497_, lean_object* v_i_498_, lean_object* v_entries_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_494_, v_keys_495_, v_vals_496_, v_i_498_, v_entries_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_501_, lean_object* v_depth_502_, lean_object* v_keys_503_, lean_object* v_vals_504_, lean_object* v_heq_505_, lean_object* v_i_506_, lean_object* v_entries_507_){
_start:
{
size_t v_depth_boxed_508_; lean_object* v_res_509_; 
v_depth_boxed_508_ = lean_unbox_usize(v_depth_502_);
lean_dec(v_depth_502_);
v_res_509_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(v_00_u03b2_501_, v_depth_boxed_508_, v_keys_503_, v_vals_504_, v_heq_505_, v_i_506_, v_entries_507_);
lean_dec_ref(v_vals_504_);
lean_dec_ref(v_keys_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_510_, lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_x_511_, v_x_512_, v_x_513_, v_x_514_);
return v___x_515_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
lean_object* v_declName_518_; lean_object* v_declName_519_; uint8_t v___x_520_; 
v_declName_518_ = lean_ctor_get(v_a_516_, 0);
v_declName_519_ = lean_ctor_get(v_b_517_, 0);
v___x_520_ = l_Lean_Name_quickLt(v_declName_518_, v_declName_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed(lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(v_a_521_, v_b_522_);
lean_dec_ref(v_b_522_);
lean_dec_ref(v_a_521_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries(lean_object* v_entries_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_array_get_size(v_entries_526_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_nat_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___y_534_; uint8_t v___x_538_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0));
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_sub(v___x_527_, v___x_531_);
v___x_538_ = lean_nat_dec_le(v___x_528_, v___x_532_);
if (v___x_538_ == 0)
{
lean_inc(v___x_532_);
v___y_534_ = v___x_532_;
goto v___jp_533_;
}
else
{
v___y_534_ = v___x_528_;
goto v___jp_533_;
}
v___jp_533_:
{
uint8_t v___x_535_; 
v___x_535_ = lean_nat_dec_le(v___y_534_, v___x_532_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_dec(v___x_532_);
lean_inc(v___y_534_);
v___x_536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_530_, v___x_527_, v_entries_526_, v___y_534_, v___y_534_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_534_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_530_, v___x_527_, v_entries_526_, v___y_534_, v___x_532_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_532_);
return v___x_537_;
}
}
}
else
{
return v_entries_526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(lean_object* v_entries_542_, lean_object* v_declName_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_array_get_size(v_entries_542_);
v___x_546_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_dec(v_declName_543_);
v___x_547_ = lean_box(0);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_sub(v___x_545_, v___x_548_);
v___x_550_ = lean_nat_dec_le(v___x_544_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec(v___x_549_);
lean_dec(v_declName_543_);
v___x_551_ = lean_box(0);
return v___x_551_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_552_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_553_ = 0;
v___x_554_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_554_, 0, v_declName_543_);
lean_ctor_set(v___x_554_, 1, v___x_552_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*2, v___x_553_);
v___x_555_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0));
v___x_556_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1));
v___x_557_ = l_Array_binSearchAux___redArg(v___x_555_, v___x_556_, v_entries_542_, v___x_554_, v___x_544_, v___x_549_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___boxed(lean_object* v_entries_558_, lean_object* v_declName_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(v_entries_558_, v_declName_559_);
lean_dec_ref(v_entries_558_);
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_declName_563_; lean_object* v_declName_564_; uint8_t v___x_565_; 
v_declName_563_ = lean_ctor_get(v___y_561_, 0);
v_declName_564_ = lean_ctor_get(v___y_562_, 0);
v___x_565_ = l_Lean_Name_quickLt(v_declName_563_, v_declName_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0___boxed(lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___y_566_, v___y_567_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v___y_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(lean_object* v_as_571_, lean_object* v_lo_572_, lean_object* v_hi_573_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = lean_nat_dec_lt(v_lo_572_, v_hi_573_);
if (v___x_574_ == 0)
{
lean_dec(v_lo_572_);
return v_as_571_;
}
else
{
lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; uint8_t v___x_579_; 
v___f_575_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___closed__0));
lean_inc(v_lo_572_);
v___x_576_ = l_Array_qpartition___redArg(v_as_571_, v___f_575_, v_lo_572_, v_hi_573_);
v_fst_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v___x_576_, 1);
lean_inc(v_snd_578_);
lean_dec_ref(v___x_576_);
v___x_579_ = lean_nat_dec_le(v_hi_573_, v_fst_577_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_snd_578_, v_lo_572_, v_fst_577_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_add(v_fst_577_, v___x_581_);
lean_dec(v_fst_577_);
v_as_571_ = v___x_580_;
v_lo_572_ = v___x_582_;
goto _start;
}
else
{
lean_dec(v_fst_577_);
lean_dec(v_lo_572_);
return v_snd_578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_as_584_, lean_object* v_lo_585_, lean_object* v_hi_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_as_584_, v_lo_585_, v_hi_586_);
lean_dec(v_hi_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_s_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_589_ = lean_array_mk(v_s_588_);
v___x_590_ = lean_array_get_size(v___x_589_);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_nat_dec_eq(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___y_596_; uint8_t v___x_600_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_sub(v___x_590_, v___x_593_);
v___x_600_ = lean_nat_dec_le(v___x_591_, v___x_594_);
if (v___x_600_ == 0)
{
lean_inc(v___x_594_);
v___y_596_ = v___x_594_;
goto v___jp_595_;
}
else
{
v___y_596_ = v___x_591_;
goto v___jp_595_;
}
v___jp_595_:
{
uint8_t v___x_597_; 
v___x_597_ = lean_nat_dec_le(v___y_596_, v___x_594_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v___x_594_);
lean_inc(v___y_596_);
v___x_598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_589_, v___y_596_, v___y_596_);
lean_dec(v___y_596_);
return v___x_598_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_589_, v___y_596_, v___x_594_);
lean_dec(v___x_594_);
return v___x_599_;
}
}
}
else
{
return v___x_589_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object* v_keys_601_, lean_object* v_i_602_, lean_object* v_k_603_){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_keys_601_);
v___x_605_ = lean_nat_dec_lt(v_i_602_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec(v_i_602_);
return v___x_605_;
}
else
{
lean_object* v_k_x27_606_; uint8_t v___x_607_; 
v_k_x27_606_ = lean_array_fget_borrowed(v_keys_601_, v_i_602_);
v___x_607_ = lean_name_eq(v_k_603_, v_k_x27_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_i_602_, v___x_608_);
lean_dec(v_i_602_);
v_i_602_ = v___x_609_;
goto _start;
}
else
{
lean_dec(v_i_602_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_611_, lean_object* v_i_612_, lean_object* v_k_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_keys_611_, v_i_612_, v_k_613_);
lean_dec(v_k_613_);
lean_dec_ref(v_keys_611_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object* v_x_616_, size_t v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v_es_619_; lean_object* v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v_j_624_; lean_object* v___x_625_; 
v_es_619_ = lean_ctor_get(v_x_616_, 0);
v___x_620_ = lean_box(2);
v___x_621_ = ((size_t)5ULL);
v___x_622_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
v___x_623_ = lean_usize_land(v_x_617_, v___x_622_);
v_j_624_ = lean_usize_to_nat(v___x_623_);
v___x_625_ = lean_array_get_borrowed(v___x_620_, v_es_619_, v_j_624_);
lean_dec(v_j_624_);
switch(lean_obj_tag(v___x_625_))
{
case 0:
{
lean_object* v_key_626_; uint8_t v___x_627_; 
v_key_626_ = lean_ctor_get(v___x_625_, 0);
v___x_627_ = lean_name_eq(v_x_618_, v_key_626_);
return v___x_627_;
}
case 1:
{
lean_object* v_node_628_; size_t v___x_629_; 
v_node_628_ = lean_ctor_get(v___x_625_, 0);
v___x_629_ = lean_usize_shift_right(v_x_617_, v___x_621_);
v_x_616_ = v_node_628_;
v_x_617_ = v___x_629_;
goto _start;
}
default: 
{
uint8_t v___x_631_; 
v___x_631_ = 0;
return v___x_631_;
}
}
}
else
{
lean_object* v_ks_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_ks_632_ = lean_ctor_get(v_x_616_, 0);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_ks_632_, v___x_633_, v_x_618_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
size_t v_x_314__boxed_638_; uint8_t v_res_639_; lean_object* v_r_640_; 
v_x_314__boxed_638_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_res_639_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___redArg(v_x_635_, v_x_314__boxed_638_, v_x_637_);
lean_dec(v_x_637_);
lean_dec_ref(v_x_635_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
uint64_t v___y_644_; 
if (lean_obj_tag(v_x_642_) == 0)
{
uint64_t v___x_647_; 
v___x_647_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_644_ = v___x_647_;
goto v___jp_643_;
}
else
{
uint64_t v_hash_648_; 
v_hash_648_ = lean_ctor_get_uint64(v_x_642_, sizeof(void*)*2);
v___y_644_ = v_hash_648_;
goto v___jp_643_;
}
v___jp_643_:
{
size_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_uint64_to_usize(v___y_644_);
v___x_646_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___redArg(v_x_641_, v___x_645_, v_x_642_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_649_, v_x_650_);
lean_dec(v_x_650_);
lean_dec_ref(v_x_649_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_x1_653_, lean_object* v_x2_654_){
_start:
{
lean_object* v_declName_655_; uint8_t v___x_656_; 
v_declName_655_ = lean_ctor_get(v_x2_654_, 0);
v___x_656_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x1_653_, v_declName_655_);
if (v___x_656_ == 0)
{
uint8_t v___x_657_; 
v___x_657_ = 1;
return v___x_657_;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_x1_659_, lean_object* v_x2_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x1_659_, v_x2_660_);
lean_dec_ref(v_x2_660_);
lean_dec_ref(v_x1_659_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(lean_object* v_x_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_x_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x_665_);
lean_dec_ref(v_x_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_));
v___x_695_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(lean_object* v_n_698_, lean_object* v_as_699_, lean_object* v_lo_700_, lean_object* v_hi_701_, lean_object* v_w_702_, lean_object* v_hlo_703_, lean_object* v_hhi_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_as_699_, v_lo_700_, v_hi_701_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___boxed(lean_object* v_n_706_, lean_object* v_as_707_, lean_object* v_lo_708_, lean_object* v_hi_709_, lean_object* v_w_710_, lean_object* v_hlo_711_, lean_object* v_hhi_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(v_n_706_, v_as_707_, v_lo_708_, v_hi_709_, v_w_710_, v_hlo_711_, v_hhi_712_);
lean_dec(v_hi_709_);
lean_dec(v_n_706_);
return v_res_713_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_715_, v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(v_00_u03b2_718_, v_x_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec_ref(v_x_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_00_u03b2_723_, lean_object* v_x_724_, size_t v_x_725_, lean_object* v_x_726_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___redArg(v_x_724_, v_x_725_, v_x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
size_t v_x_492__boxed_732_; uint8_t v_res_733_; lean_object* v_r_734_; 
v_x_492__boxed_732_ = lean_unbox_usize(v_x_730_);
lean_dec(v_x_730_);
v_res_733_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1(v_00_u03b2_728_, v_x_729_, v_x_492__boxed_732_, v_x_731_);
lean_dec(v_x_731_);
lean_dec_ref(v_x_729_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object* v_00_u03b2_735_, lean_object* v_keys_736_, lean_object* v_vals_737_, lean_object* v_heq_738_, lean_object* v_i_739_, lean_object* v_k_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_keys_736_, v_i_739_, v_k_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_742_, lean_object* v_keys_743_, lean_object* v_vals_744_, lean_object* v_heq_745_, lean_object* v_i_746_, lean_object* v_k_747_){
_start:
{
uint8_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_742_, v_keys_743_, v_vals_744_, v_heq_745_, v_i_746_, v_k_747_);
lean_dec(v_k_747_);
lean_dec_ref(v_vals_744_);
lean_dec_ref(v_keys_743_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(lean_object* v_env_750_, lean_object* v_type_751_){
_start:
{
if (lean_obj_tag(v_type_751_) == 7)
{
lean_object* v_body_752_; 
v_body_752_ = lean_ctor_get(v_type_751_, 2);
v_type_751_ = v_body_752_;
goto _start;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Expr_getAppFn(v_type_751_);
if (lean_obj_tag(v___x_754_) == 4)
{
lean_object* v_declName_755_; uint8_t v___x_756_; 
v_declName_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_declName_755_);
lean_dec_ref(v___x_754_);
v___x_756_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_750_, v_declName_755_);
return v___x_756_;
}
else
{
uint8_t v___x_757_; 
lean_dec_ref(v___x_754_);
lean_dec_ref(v_env_750_);
v___x_757_ = 0;
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType___boxed(lean_object* v_env_758_, lean_object* v_type_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_758_, v_type_759_);
lean_dec_ref(v_type_759_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(lean_object* v_env_762_, lean_object* v_type_763_){
_start:
{
if (lean_obj_tag(v_type_763_) == 7)
{
lean_object* v_body_764_; 
v_body_764_ = lean_ctor_get(v_type_763_, 2);
v_type_763_ = v_body_764_;
goto _start;
}
else
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Expr_getAppFn(v_type_763_);
if (lean_obj_tag(v___x_766_) == 4)
{
lean_object* v_declName_767_; uint8_t v___x_768_; 
v_declName_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_declName_767_);
lean_dec_ref(v___x_766_);
v___x_768_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_762_, v_declName_767_);
return v___x_768_;
}
else
{
uint8_t v___x_769_; 
lean_dec_ref(v___x_766_);
lean_dec_ref(v_env_762_);
v___x_769_ = 0;
return v___x_769_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType___boxed(lean_object* v_env_770_, lean_object* v_type_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_770_, v_type_771_);
lean_dec_ref(v_type_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(lean_object* v___x_777_, lean_object* v_param_778_, lean_object* v_paramsInfo_779_, lean_object* v_upperBound_780_, lean_object* v_a_781_, lean_object* v_b_782_){
_start:
{
lean_object* v_a_784_; uint8_t v___x_788_; 
v___x_788_ = lean_nat_dec_lt(v_a_781_, v_upperBound_780_);
if (v___x_788_ == 0)
{
lean_dec(v_a_781_);
lean_inc_ref(v_b_782_);
return v_b_782_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_799_; lean_object* v___x_802_; 
v___x_789_ = lean_box(0);
v___x_790_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0));
v___x_799_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default));
v___x_802_ = lean_array_get_borrowed(v___x_799_, v_paramsInfo_779_, v_a_781_);
switch(lean_obj_tag(v___x_802_))
{
case 0:
{
uint8_t v_weak_803_; 
v_weak_803_ = lean_ctor_get_uint8(v___x_802_, 0);
if (v_weak_803_ == 0)
{
goto v___jp_791_;
}
else
{
goto v___jp_800_;
}
}
case 2:
{
goto v___jp_800_;
}
case 4:
{
goto v___jp_800_;
}
default: 
{
goto v___jp_791_;
}
}
v___jp_791_:
{
lean_object* v___x_792_; lean_object* v_type_793_; lean_object* v_fvarId_794_; uint8_t v___x_795_; 
v___x_792_ = lean_array_fget_borrowed(v___x_777_, v_a_781_);
v_type_793_ = lean_ctor_get(v___x_792_, 2);
v_fvarId_794_ = lean_ctor_get(v_param_778_, 0);
v___x_795_ = l_Lean_Expr_containsFVar(v_type_793_, v_fvarId_794_);
if (v___x_795_ == 0)
{
v_a_784_ = v___x_790_;
goto v___jp_783_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v_a_781_);
v___x_796_ = lean_box(v___x_795_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_789_);
return v___x_798_;
}
}
v___jp_800_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_array_get_borrowed(v___x_799_, v_paramsInfo_779_, v_a_781_);
if (lean_obj_tag(v___x_801_) == 0)
{
goto v___jp_791_;
}
else
{
v_a_784_ = v___x_790_;
goto v___jp_783_;
}
}
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_add(v_a_781_, v___x_785_);
lean_dec(v_a_781_);
v_a_781_ = v___x_786_;
v_b_782_ = v_a_784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___boxed(lean_object* v___x_804_, lean_object* v_param_805_, lean_object* v_paramsInfo_806_, lean_object* v_upperBound_807_, lean_object* v_a_808_, lean_object* v_b_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_804_, v_param_805_, v_paramsInfo_806_, v_upperBound_807_, v_a_808_, v_b_809_);
lean_dec_ref(v_b_809_);
lean_dec(v_upperBound_807_);
lean_dec_ref(v_paramsInfo_806_);
lean_dec_ref(v_param_805_);
lean_dec_ref(v___x_804_);
return v_res_810_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0(void){
_start:
{
uint8_t v___x_811_; lean_object* v___x_812_; 
v___x_811_ = 0;
v___x_812_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(lean_object* v_decl_813_, lean_object* v_paramsInfo_814_, lean_object* v_j_815_){
_start:
{
lean_object* v_toSignature_816_; lean_object* v_params_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_param_823_; lean_object* v___x_824_; lean_object* v_fst_825_; 
v_toSignature_816_ = lean_ctor_get(v_decl_813_, 0);
v_params_817_ = lean_ctor_get(v_toSignature_816_, 3);
v___x_818_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0, &l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0);
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_nat_add(v_j_815_, v___x_819_);
v___x_821_ = lean_array_get_size(v_params_817_);
v___x_822_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0));
v_param_823_ = lean_array_get_borrowed(v___x_818_, v_params_817_, v_j_815_);
v___x_824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v_params_817_, v_param_823_, v_paramsInfo_814_, v___x_821_, v___x_820_, v___x_822_);
v_fst_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_fst_825_);
lean_dec_ref(v___x_824_);
if (lean_obj_tag(v_fst_825_) == 0)
{
uint8_t v___x_826_; 
v___x_826_ = 0;
return v___x_826_;
}
else
{
lean_object* v_val_827_; uint8_t v___x_828_; 
v_val_827_ = lean_ctor_get(v_fst_825_, 0);
lean_inc(v_val_827_);
lean_dec_ref(v_fst_825_);
v___x_828_ = lean_unbox(v_val_827_);
lean_dec(v_val_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___boxed(lean_object* v_decl_829_, lean_object* v_paramsInfo_830_, lean_object* v_j_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v_decl_829_, v_paramsInfo_830_, v_j_831_);
lean_dec(v_j_831_);
lean_dec_ref(v_paramsInfo_830_);
lean_dec_ref(v_decl_829_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(lean_object* v___x_834_, lean_object* v_param_835_, lean_object* v_paramsInfo_836_, lean_object* v_upperBound_837_, lean_object* v_inst_838_, lean_object* v_R_839_, lean_object* v_a_840_, lean_object* v_b_841_, lean_object* v_c_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_834_, v_param_835_, v_paramsInfo_836_, v_upperBound_837_, v_a_840_, v_b_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___boxed(lean_object* v___x_844_, lean_object* v_param_845_, lean_object* v_paramsInfo_846_, lean_object* v_upperBound_847_, lean_object* v_inst_848_, lean_object* v_R_849_, lean_object* v_a_850_, lean_object* v_b_851_, lean_object* v_c_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(v___x_844_, v_param_845_, v_paramsInfo_846_, v_upperBound_847_, v_inst_848_, v_R_849_, v_a_850_, v_b_851_, v_c_852_);
lean_dec_ref(v_b_851_);
lean_dec(v_upperBound_847_);
lean_dec_ref(v_paramsInfo_846_);
lean_dec_ref(v_param_845_);
lean_dec_ref(v___x_844_);
return v_res_853_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0(void){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_instMonadEIO(lean_box(0));
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(lean_object* v_msg_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_toApplicative_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_898_; 
v___x_863_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0, &l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0);
v___x_864_ = l_StateRefT_x27_instMonad___redArg(v___x_863_);
v_toApplicative_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v___x_864_, 1);
lean_dec(v_unused_899_);
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_898_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_toApplicative_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_898_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_toFunctor_869_; lean_object* v_toSeq_870_; lean_object* v_toSeqLeft_871_; lean_object* v_toSeqRight_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_896_; 
v_toFunctor_869_ = lean_ctor_get(v_toApplicative_865_, 0);
v_toSeq_870_ = lean_ctor_get(v_toApplicative_865_, 2);
v_toSeqLeft_871_ = lean_ctor_get(v_toApplicative_865_, 3);
v_toSeqRight_872_ = lean_ctor_get(v_toApplicative_865_, 4);
v_isSharedCheck_896_ = !lean_is_exclusive(v_toApplicative_865_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_toApplicative_865_, 1);
lean_dec(v_unused_897_);
v___x_874_ = v_toApplicative_865_;
v_isShared_875_ = v_isSharedCheck_896_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_toSeqRight_872_);
lean_inc(v_toSeqLeft_871_);
lean_inc(v_toSeq_870_);
lean_inc(v_toFunctor_869_);
lean_dec(v_toApplicative_865_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_896_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___x_885_; 
v___f_876_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1));
v___f_877_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2));
lean_inc_ref(v_toFunctor_869_);
v___f_878_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_878_, 0, v_toFunctor_869_);
v___f_879_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_879_, 0, v_toFunctor_869_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___f_878_);
lean_ctor_set(v___x_880_, 1, v___f_879_);
v___f_881_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_881_, 0, v_toSeqRight_872_);
v___f_882_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_882_, 0, v_toSeqLeft_871_);
v___f_883_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_883_, 0, v_toSeq_870_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 4, v___f_881_);
lean_ctor_set(v___x_874_, 3, v___f_882_);
lean_ctor_set(v___x_874_, 2, v___f_883_);
lean_ctor_set(v___x_874_, 1, v___f_876_);
lean_ctor_set(v___x_874_, 0, v___x_880_);
v___x_885_ = v___x_874_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___f_876_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v___f_883_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v___f_882_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v___f_881_);
v___x_885_ = v_reuseFailAlloc_895_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___f_877_);
lean_ctor_set(v___x_867_, 0, v___x_885_);
v___x_887_ = v___x_867_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___f_877_);
v___x_887_ = v_reuseFailAlloc_894_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___x_11117__overap_892_; lean_object* v___x_893_; 
v___x_888_ = l_StateRefT_x27_instMonad___redArg(v___x_887_);
v___x_889_ = lean_box(0);
v___x_890_ = l_instInhabitedOfMonad___redArg(v___x_888_, v___x_889_);
v___f_891_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_891_, 0, v___x_890_);
v___x_11117__overap_892_ = lean_panic_fn_borrowed(v___f_891_, v_msg_857_);
lean_dec_ref(v___f_891_);
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
v___x_893_ = lean_apply_5(v___x_11117__overap_892_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, lean_box(0));
return v___x_893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___boxed(lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(lean_object* v_a_907_, lean_object* v_as_908_, size_t v_i_909_, size_t v_stop_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_eq(v_i_909_, v_stop_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_array_uget_borrowed(v_as_908_, v_i_909_);
v___x_913_ = lean_nat_dec_eq(v_a_907_, v___x_912_);
if (v___x_913_ == 0)
{
size_t v___x_914_; size_t v___x_915_; 
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_add(v_i_909_, v___x_914_);
v_i_909_ = v___x_915_;
goto _start;
}
else
{
return v___x_913_;
}
}
else
{
uint8_t v___x_917_; 
v___x_917_ = 0;
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0___boxed(lean_object* v_a_918_, lean_object* v_as_919_, lean_object* v_i_920_, lean_object* v_stop_921_){
_start:
{
size_t v_i_boxed_922_; size_t v_stop_boxed_923_; uint8_t v_res_924_; lean_object* v_r_925_; 
v_i_boxed_922_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_stop_boxed_923_ = lean_unbox_usize(v_stop_921_);
lean_dec(v_stop_921_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(v_a_918_, v_as_919_, v_i_boxed_922_, v_stop_boxed_923_);
lean_dec_ref(v_as_919_);
lean_dec(v_a_918_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(lean_object* v_as_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_array_get_size(v_as_926_);
v___x_930_ = lean_nat_dec_lt(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
return v___x_930_;
}
else
{
if (v___x_930_ == 0)
{
return v___x_930_;
}
else
{
size_t v___x_931_; size_t v___x_932_; uint8_t v___x_933_; 
v___x_931_ = ((size_t)0ULL);
v___x_932_ = lean_usize_of_nat(v___x_929_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(v_a_927_, v_as_926_, v___x_931_, v___x_932_);
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0___boxed(lean_object* v_as_934_, lean_object* v_a_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_as_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_as_934_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(lean_object* v_b_938_, lean_object* v_info_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_array_push(v_b_938_, v_info_939_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0___boxed(lean_object* v_b_948_, lean_object* v_info_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_948_, v_info_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(lean_object* v_upperBound_958_, lean_object* v___x_959_, lean_object* v_autoSpecialize_960_, lean_object* v___x_961_, lean_object* v___x_962_, lean_object* v_a_963_, lean_object* v_b_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___y_971_; uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_lt(v_a_963_, v_upperBound_958_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
lean_dec(v_a_963_);
lean_dec(v___x_962_);
lean_dec(v___x_961_);
lean_dec_ref(v_autoSpecialize_960_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_b_964_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_type_997_; lean_object* v___x_998_; 
v___x_995_ = lean_st_ref_get(v___y_968_);
v___x_996_ = lean_array_fget_borrowed(v___x_959_, v_a_963_);
v_type_997_ = lean_ctor_get(v___x_996_, 2);
lean_inc_ref(v_type_997_);
v___x_998_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_997_, v___y_968_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v_env_1000_; uint8_t v___y_1011_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v___x_998_);
v_env_1000_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_env_1000_);
lean_dec(v___x_995_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0));
v___x_1025_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v___x_1024_, v_a_963_);
v___y_1011_ = v___x_1025_;
goto v___jp_1010_;
}
else
{
lean_object* v_val_1026_; uint8_t v___x_1027_; 
v_val_1026_ = lean_ctor_get(v___x_962_, 0);
v___x_1027_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_val_1026_, v_a_963_);
v___y_1011_ = v___x_1027_;
goto v___jp_1010_;
}
v___jp_1001_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_box(4);
v___x_1003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_964_, v___x_1002_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
v___y_971_ = v___x_1003_;
goto v___jp_970_;
}
v___jp_1004_:
{
lean_object* v___x_1005_; lean_object* v_env_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1005_ = lean_st_ref_get(v___y_968_);
v_env_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc_ref(v_env_1006_);
lean_dec(v___x_1005_);
v___x_1007_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(v_env_1006_, v_type_997_);
v___x_1008_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1008_, 0, v___x_1007_);
v___x_1009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_964_, v___x_1008_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
v___y_971_ = v___x_1009_;
goto v___jp_970_;
}
v___jp_1010_:
{
if (v___y_1011_ == 0)
{
uint8_t v___x_1012_; 
v___x_1012_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(v_env_1000_, v_type_997_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; 
lean_inc_ref(v_type_997_);
v___x_1013_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_997_);
if (v___x_1013_ == 0)
{
if (lean_obj_tag(v_a_999_) == 0)
{
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
lean_inc_ref(v_autoSpecialize_960_);
lean_inc(v___x_962_);
lean_inc(v___x_961_);
v___x_1014_ = lean_apply_2(v_autoSpecialize_960_, v___x_961_, v___x_962_);
v___x_1015_ = lean_unbox(v___x_1014_);
if (v___x_1015_ == 0)
{
goto v___jp_1001_;
}
else
{
if (lean_obj_tag(v_type_997_) == 7)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_box(1);
v___x_1017_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_964_, v___x_1016_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
v___y_971_ = v___x_1017_;
goto v___jp_970_;
}
else
{
goto v___jp_1001_;
}
}
}
else
{
goto v___jp_1004_;
}
}
else
{
lean_dec_ref(v_a_999_);
goto v___jp_1004_;
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v_a_999_);
v___x_1018_ = lean_box(2);
v___x_1019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_964_, v___x_1018_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
v___y_971_ = v___x_1019_;
goto v___jp_970_;
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec(v_a_999_);
v___x_1020_ = lean_box(4);
v___x_1021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_964_, v___x_1020_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
v___y_971_ = v___x_1021_;
goto v___jp_970_;
}
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec_ref(v_env_1000_);
lean_dec(v_a_999_);
v___x_1022_ = lean_box(3);
v___x_1023_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_964_, v___x_1022_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
v___y_971_ = v___x_1023_;
goto v___jp_970_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v___x_995_);
lean_dec_ref(v_b_964_);
lean_dec(v_a_963_);
lean_dec(v___x_962_);
lean_dec(v___x_961_);
lean_dec_ref(v_autoSpecialize_960_);
v_a_1028_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_998_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_998_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
v___jp_970_:
{
if (lean_obj_tag(v___y_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_984_; 
v_a_972_ = lean_ctor_get(v___y_971_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___y_971_);
if (v_isSharedCheck_984_ == 0)
{
v___x_974_ = v___y_971_;
v_isShared_975_ = v_isSharedCheck_984_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___y_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_984_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
if (lean_obj_tag(v_a_972_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; 
lean_dec(v_a_963_);
lean_dec(v___x_962_);
lean_dec(v___x_961_);
lean_dec_ref(v_autoSpecialize_960_);
v_a_976_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v_a_972_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v_a_976_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_del_object(v___x_974_);
v_a_980_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v_a_972_);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_add(v_a_963_, v___x_981_);
lean_dec(v_a_963_);
v_a_963_ = v___x_982_;
v_b_964_ = v_a_980_;
goto _start;
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_a_963_);
lean_dec(v___x_962_);
lean_dec(v___x_961_);
lean_dec_ref(v_autoSpecialize_960_);
v_a_985_ = lean_ctor_get(v___y_971_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___y_971_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___y_971_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___y_971_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___boxed(lean_object* v_upperBound_1036_, lean_object* v___x_1037_, lean_object* v_autoSpecialize_1038_, lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_a_1041_, lean_object* v_b_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v_upperBound_1036_, v___x_1037_, v_autoSpecialize_1038_, v___x_1039_, v___x_1040_, v_a_1041_, v_b_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec_ref(v___x_1037_);
lean_dec(v_upperBound_1036_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(lean_object* v_autoSpecialize_1049_, lean_object* v_as_1050_, size_t v_sz_1051_, size_t v_i_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_a_1060_; uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_lt(v_i_1052_, v_sz_1051_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_dec_ref(v_autoSpecialize_1049_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_b_1053_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v_env_1067_; lean_object* v_a_1068_; lean_object* v_toSignature_1069_; lean_object* v_name_1070_; lean_object* v_params_1071_; uint8_t v___x_1072_; 
v___x_1066_ = lean_st_ref_get(v___y_1057_);
v_env_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc_ref(v_env_1067_);
lean_dec(v___x_1066_);
v_a_1068_ = lean_array_uget_borrowed(v_as_1050_, v_i_1052_);
v_toSignature_1069_ = lean_ctor_get(v_a_1068_, 0);
v_name_1070_ = lean_ctor_get(v_toSignature_1069_, 0);
v_params_1071_ = lean_ctor_get(v_toSignature_1069_, 3);
lean_inc(v_name_1070_);
v___x_1072_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1067_, v_name_1070_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v_env_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1073_ = lean_st_ref_get(v___y_1057_);
v_env_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_env_1074_);
lean_dec(v___x_1073_);
v___x_1075_ = lean_array_get_size(v_params_1071_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
lean_inc_n(v_name_1070_, 2);
v___x_1078_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_1074_, v_name_1070_);
lean_inc_ref(v_autoSpecialize_1049_);
v___x_1079_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v___x_1075_, v_params_1071_, v_autoSpecialize_1049_, v_name_1070_, v___x_1078_, v___x_1076_, v___x_1077_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = lean_array_push(v_b_1053_, v_a_1080_);
v_a_1060_ = v___x_1081_;
goto v___jp_1059_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v_b_1053_);
lean_dec_ref(v_autoSpecialize_1049_);
v_a_1082_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1079_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1090_ = lean_array_get_size(v_params_1071_);
v___x_1091_ = lean_box(4);
v___x_1092_ = lean_mk_array(v___x_1090_, v___x_1091_);
v___x_1093_ = lean_array_push(v_b_1053_, v___x_1092_);
v_a_1060_ = v___x_1093_;
goto v___jp_1059_;
}
}
v___jp_1059_:
{
size_t v___x_1061_; size_t v___x_1062_; 
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_add(v_i_1052_, v___x_1061_);
v_i_1052_ = v___x_1062_;
v_b_1053_ = v_a_1060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3___boxed(lean_object* v_autoSpecialize_1094_, lean_object* v_as_1095_, lean_object* v_sz_1096_, lean_object* v_i_1097_, lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
size_t v_sz_boxed_1104_; size_t v_i_boxed_1105_; lean_object* v_res_1106_; 
v_sz_boxed_1104_ = lean_unbox_usize(v_sz_1096_);
lean_dec(v_sz_1096_);
v_i_boxed_1105_ = lean_unbox_usize(v_i_1097_);
lean_dec(v_i_1097_);
v_res_1106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1094_, v_as_1095_, v_sz_boxed_1104_, v_i_boxed_1105_, v_b_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec_ref(v_as_1095_);
return v_res_1106_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(lean_object* v_as_1107_, size_t v_i_1108_, size_t v_stop_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_eq(v_i_1108_, v_stop_1109_);
if (v___x_1110_ == 0)
{
uint8_t v___x_1111_; uint8_t v___y_1113_; lean_object* v___x_1117_; 
v___x_1111_ = 1;
v___x_1117_ = lean_array_uget_borrowed(v_as_1107_, v_i_1108_);
switch(lean_obj_tag(v___x_1117_))
{
case 0:
{
uint8_t v_weak_1118_; 
v_weak_1118_ = lean_ctor_get_uint8(v___x_1117_, 0);
if (v_weak_1118_ == 0)
{
return v___x_1111_;
}
else
{
v___y_1113_ = v___x_1110_;
goto v___jp_1112_;
}
}
case 2:
{
v___y_1113_ = v___x_1110_;
goto v___jp_1112_;
}
case 4:
{
v___y_1113_ = v___x_1110_;
goto v___jp_1112_;
}
default: 
{
return v___x_1111_;
}
}
v___jp_1112_:
{
if (v___y_1113_ == 0)
{
size_t v___x_1114_; size_t v___x_1115_; 
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_add(v_i_1108_, v___x_1114_);
v_i_1108_ = v___x_1115_;
goto _start;
}
else
{
return v___x_1111_;
}
}
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = 0;
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___boxed(lean_object* v_as_1120_, lean_object* v_i_1121_, lean_object* v_stop_1122_){
_start:
{
size_t v_i_boxed_1123_; size_t v_stop_boxed_1124_; uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_i_boxed_1123_ = lean_unbox_usize(v_i_1121_);
lean_dec(v_i_1121_);
v_stop_boxed_1124_ = lean_unbox_usize(v_stop_1122_);
lean_dec(v_stop_1122_);
v_res_1125_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_as_1120_, v_i_boxed_1123_, v_stop_boxed_1124_);
lean_dec_ref(v_as_1120_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(lean_object* v_as_1127_, size_t v_i_1128_, size_t v_stop_1129_){
_start:
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_usize_dec_eq(v_i_1128_, v_stop_1129_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; uint8_t v___y_1133_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1131_ = 1;
v___x_1137_ = lean_array_uget_borrowed(v_as_1127_, v_i_1128_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_array_get_size(v___x_1137_);
v___x_1140_ = lean_nat_dec_lt(v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
v___y_1133_ = v___x_1130_;
goto v___jp_1132_;
}
else
{
if (v___x_1140_ == 0)
{
v___y_1133_ = v___x_1130_;
goto v___jp_1132_;
}
else
{
size_t v___x_1141_; size_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = lean_usize_of_nat(v___x_1139_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v___x_1137_, v___x_1141_, v___x_1142_);
v___y_1133_ = v___x_1143_;
goto v___jp_1132_;
}
}
v___jp_1132_:
{
if (v___y_1133_ == 0)
{
size_t v___x_1134_; size_t v___x_1135_; 
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_add(v_i_1128_, v___x_1134_);
v_i_1128_ = v___x_1135_;
goto _start;
}
else
{
return v___x_1131_;
}
}
}
else
{
uint8_t v___x_1144_; 
v___x_1144_ = 0;
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5___boxed(lean_object* v_as_1145_, lean_object* v_i_1146_, lean_object* v_stop_1147_){
_start:
{
size_t v_i_boxed_1148_; size_t v_stop_boxed_1149_; uint8_t v_res_1150_; lean_object* v_r_1151_; 
v_i_boxed_1148_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_stop_boxed_1149_ = lean_unbox_usize(v_stop_1147_);
lean_dec(v_stop_1147_);
v_res_1150_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_as_1145_, v_i_boxed_1148_, v_stop_boxed_1149_);
lean_dec_ref(v_as_1145_);
v_r_1151_ = lean_box(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(lean_object* v_as_1152_, lean_object* v_bs_1153_, lean_object* v_i_1154_, lean_object* v_cs_1155_){
_start:
{
lean_object* v___y_1157_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_array_get_size(v_as_1152_);
v___x_1163_ = lean_nat_dec_lt(v_i_1154_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_dec(v_i_1154_);
return v_cs_1155_;
}
else
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_array_get_size(v_bs_1153_);
v___x_1165_ = lean_nat_dec_lt(v_i_1154_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_dec(v_i_1154_);
return v_cs_1155_;
}
else
{
lean_object* v_a_1166_; lean_object* v_b_1167_; uint8_t v___x_1168_; 
v_a_1166_ = lean_array_fget_borrowed(v_as_1152_, v_i_1154_);
v_b_1167_ = lean_array_fget_borrowed(v_bs_1153_, v_i_1154_);
v___x_1168_ = lean_unbox(v_b_1167_);
if (v___x_1168_ == 0)
{
if (lean_obj_tag(v_a_1166_) == 3)
{
v___y_1157_ = v_a_1166_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_box(4);
v___y_1157_ = v___x_1169_;
goto v___jp_1156_;
}
}
else
{
lean_inc(v_a_1166_);
v___y_1157_ = v_a_1166_;
goto v___jp_1156_;
}
}
}
v___jp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_i_1154_, v___x_1158_);
lean_dec(v_i_1154_);
v___x_1160_ = lean_array_push(v_cs_1155_, v___y_1157_);
v_i_1154_ = v___x_1159_;
v_cs_1155_ = v___x_1160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6___boxed(lean_object* v_as_1170_, lean_object* v_bs_1171_, lean_object* v_i_1172_, lean_object* v_cs_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v_as_1170_, v_bs_1171_, v_i_1172_, v_cs_1173_);
lean_dec_ref(v_bs_1171_);
lean_dec_ref(v_as_1170_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(lean_object* v_upperBound_1175_, lean_object* v___x_1176_, lean_object* v_a_1177_, lean_object* v_b_1178_){
_start:
{
lean_object* v_a_1181_; uint8_t v___x_1185_; 
v___x_1185_ = lean_nat_dec_lt(v_a_1177_, v_upperBound_1175_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec(v_a_1177_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_b_1178_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default));
v___x_1188_ = lean_array_get_borrowed(v___x_1187_, v_b_1178_, v_a_1177_);
if (lean_obj_tag(v___x_1188_) == 2)
{
uint8_t v___x_1189_; 
v___x_1189_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v___x_1176_, v_b_1178_, v_a_1177_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_box(4);
v___x_1191_ = lean_array_set(v_b_1178_, v_a_1177_, v___x_1190_);
v_a_1181_ = v___x_1191_;
goto v___jp_1180_;
}
else
{
v_a_1181_ = v_b_1178_;
goto v___jp_1180_;
}
}
else
{
v_a_1181_ = v_b_1178_;
goto v___jp_1180_;
}
}
v___jp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_nat_add(v_a_1177_, v___x_1182_);
lean_dec(v_a_1177_);
v_a_1177_ = v___x_1183_;
v_b_1178_ = v_a_1181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg___boxed(lean_object* v_upperBound_1192_, lean_object* v___x_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1192_, v___x_1193_, v_a_1194_, v_b_1195_);
lean_dec_ref(v___x_1193_);
lean_dec(v_upperBound_1192_);
return v_res_1197_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Array_instInhabited(lean_box(0));
return v___x_1198_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1202_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3));
v___x_1203_ = lean_unsigned_to_nat(43u);
v___x_1204_ = lean_unsigned_to_nat(236u);
v___x_1205_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2));
v___x_1206_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1));
v___x_1207_ = l_mkPanicMessageWithDecl(v___x_1206_, v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(lean_object* v_upperBound_1208_, lean_object* v_decls_1209_, lean_object* v_alreadySpecialized_1210_, lean_object* v___x_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_b_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_a_1221_; uint8_t v___x_1225_; 
v___x_1225_ = lean_nat_dec_lt(v_a_1213_, v_upperBound_1208_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_dec(v_a_1213_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_b_1214_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v_toSignature_1228_; lean_object* v_name_1229_; lean_object* v___x_1230_; 
v___x_1227_ = lean_array_fget_borrowed(v_decls_1209_, v_a_1213_);
v_toSignature_1228_ = lean_ctor_get(v___x_1227_, 0);
v_name_1229_ = lean_ctor_get(v_toSignature_1228_, 0);
v___x_1230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1211_, v_name_1229_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref(v___x_1230_);
v___x_1232_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0);
v___x_1233_ = lean_array_get_borrowed(v___x_1232_, v_a_1212_, v_a_1213_);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1236_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v___x_1233_, v_val_1231_, v___x_1234_, v___x_1235_);
lean_dec(v_val_1231_);
v___x_1237_ = lean_array_get_size(v___x_1236_);
v___x_1238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v___x_1237_, v___x_1227_, v___x_1234_, v___x_1236_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = 0;
v___x_1241_ = lean_box(v___x_1240_);
v___x_1242_ = lean_array_get(v___x_1241_, v_alreadySpecialized_1210_, v_a_1213_);
lean_dec(v___x_1241_);
lean_inc(v_name_1229_);
v___x_1243_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1243_, 0, v_name_1229_);
lean_ctor_set(v___x_1243_, 1, v_a_1239_);
v___x_1244_ = lean_unbox(v___x_1242_);
lean_dec(v___x_1242_);
lean_ctor_set_uint8(v___x_1243_, sizeof(void*)*2, v___x_1244_);
v___x_1245_ = lean_array_push(v_b_1214_, v___x_1243_);
v_a_1221_ = v___x_1245_;
goto v___jp_1220_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_b_1214_);
lean_dec(v_a_1213_);
v_a_1246_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1238_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1238_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec(v___x_1230_);
v___x_1254_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4);
v___x_1255_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(v___x_1254_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_dec_ref(v___x_1255_);
v_a_1221_ = v_b_1214_;
goto v___jp_1220_;
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_b_1214_);
lean_dec(v_a_1213_);
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
v___jp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_add(v_a_1213_, v___x_1222_);
lean_dec(v_a_1213_);
v_a_1213_ = v___x_1223_;
v_b_1214_ = v_a_1221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___boxed(lean_object* v_upperBound_1264_, lean_object* v_decls_1265_, lean_object* v_alreadySpecialized_1266_, lean_object* v___x_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_b_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1264_, v_decls_1265_, v_alreadySpecialized_1266_, v___x_1267_, v_a_1268_, v_a_1269_, v_b_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec_ref(v_a_1268_);
lean_dec(v___x_1267_);
lean_dec_ref(v_alreadySpecialized_1266_);
lean_dec_ref(v_decls_1265_);
lean_dec(v_upperBound_1264_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(lean_object* v_alreadySpecialized_1277_, lean_object* v_as_1278_, lean_object* v_i_1279_, lean_object* v_j_1280_, lean_object* v_bs_1281_){
_start:
{
lean_object* v_zero_1282_; uint8_t v_isZero_1283_; 
v_zero_1282_ = lean_unsigned_to_nat(0u);
v_isZero_1283_ = lean_nat_dec_eq(v_i_1279_, v_zero_1282_);
if (v_isZero_1283_ == 1)
{
lean_dec(v_j_1280_);
lean_dec(v_i_1279_);
return v_bs_1281_;
}
else
{
lean_object* v___x_1284_; lean_object* v_toSignature_1285_; lean_object* v_name_1286_; lean_object* v_params_1287_; lean_object* v_one_1288_; lean_object* v_n_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1284_ = lean_array_fget_borrowed(v_as_1278_, v_j_1280_);
v_toSignature_1285_ = lean_ctor_get(v___x_1284_, 0);
v_name_1286_ = lean_ctor_get(v_toSignature_1285_, 0);
v_params_1287_ = lean_ctor_get(v_toSignature_1285_, 3);
v_one_1288_ = lean_unsigned_to_nat(1u);
v_n_1289_ = lean_nat_sub(v_i_1279_, v_one_1288_);
lean_dec(v_i_1279_);
v___x_1290_ = lean_array_get_size(v_params_1287_);
v___x_1291_ = lean_box(4);
v___x_1292_ = lean_mk_array(v___x_1290_, v___x_1291_);
v___x_1293_ = lean_box(v_isZero_1283_);
v___x_1294_ = lean_array_get(v___x_1293_, v_alreadySpecialized_1277_, v_j_1280_);
lean_dec(v___x_1293_);
lean_inc(v_name_1286_);
v___x_1295_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1295_, 0, v_name_1286_);
lean_ctor_set(v___x_1295_, 1, v___x_1292_);
v___x_1296_ = lean_unbox(v___x_1294_);
lean_dec(v___x_1294_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*2, v___x_1296_);
v___x_1297_ = lean_nat_add(v_j_1280_, v_one_1288_);
lean_dec(v_j_1280_);
v___x_1298_ = lean_array_push(v_bs_1281_, v___x_1295_);
v_i_1279_ = v_n_1289_;
v_j_1280_ = v___x_1297_;
v_bs_1281_ = v___x_1298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg___boxed(lean_object* v_alreadySpecialized_1300_, lean_object* v_as_1301_, lean_object* v_i_1302_, lean_object* v_j_1303_, lean_object* v_bs_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1300_, v_as_1301_, v_i_1302_, v_j_1303_, v_bs_1304_);
lean_dec_ref(v_as_1301_);
lean_dec_ref(v_alreadySpecialized_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries(lean_object* v_decls_1308_, lean_object* v_autoSpecialize_1309_, lean_object* v_alreadySpecialized_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v_declsInfo_1317_; size_t v_sz_1318_; size_t v___x_1319_; lean_object* v___x_1320_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v_declsInfo_1317_ = ((lean_object*)(l_Lean_Compiler_LCNF_computeSpecEntries___closed__0));
v_sz_1318_ = lean_array_size(v_decls_1308_);
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_1309_, v_decls_1308_, v_sz_1318_, v___x_1319_, v_declsInfo_1317_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1340_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1340_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1340_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_array_get_size(v_a_1321_);
v___x_1333_ = lean_nat_dec_lt(v___x_1316_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_dec(v_a_1321_);
goto v___jp_1325_;
}
else
{
if (v___x_1333_ == 0)
{
lean_dec(v_a_1321_);
goto v___jp_1325_;
}
else
{
size_t v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_usize_of_nat(v___x_1332_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_a_1321_, v___x_1319_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec(v_a_1321_);
goto v___jp_1325_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_del_object(v___x_1323_);
v___x_1336_ = lean_array_get_size(v_decls_1308_);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1336_);
lean_inc_ref(v_decls_1308_);
v___x_1338_ = l_Lean_Compiler_LCNF_mkFixedParamsMap(v_decls_1308_);
v___x_1339_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v___x_1336_, v_decls_1308_, v_alreadySpecialized_1310_, v___x_1338_, v_a_1321_, v___x_1316_, v___x_1337_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1321_);
lean_dec(v___x_1338_);
lean_dec_ref(v_decls_1308_);
return v___x_1339_;
}
}
}
v___jp_1325_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1326_ = lean_array_get_size(v_decls_1308_);
v___x_1327_ = lean_mk_empty_array_with_capacity(v___x_1326_);
v___x_1328_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1310_, v_decls_1308_, v___x_1326_, v___x_1316_, v___x_1327_);
lean_dec_ref(v_decls_1308_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1328_);
v___x_1330_ = v___x_1323_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_decls_1308_);
v_a_1341_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1320_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1320_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_computeSpecEntries___boxed(lean_object* v_decls_1349_, lean_object* v_autoSpecialize_1350_, lean_object* v_alreadySpecialized_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1349_, v_autoSpecialize_1350_, v_alreadySpecialized_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec_ref(v_alreadySpecialized_1351_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(lean_object* v_upperBound_1358_, lean_object* v___x_1359_, lean_object* v_autoSpecialize_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v_inst_1363_, lean_object* v_R_1364_, lean_object* v_a_1365_, lean_object* v_b_1366_, lean_object* v_c_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v_upperBound_1358_, v___x_1359_, v_autoSpecialize_1360_, v___x_1361_, v___x_1362_, v_a_1365_, v_b_1366_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___boxed(lean_object* v_upperBound_1374_, lean_object* v___x_1375_, lean_object* v_autoSpecialize_1376_, lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v_inst_1379_, lean_object* v_R_1380_, lean_object* v_a_1381_, lean_object* v_b_1382_, lean_object* v_c_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(v_upperBound_1374_, v___x_1375_, v_autoSpecialize_1376_, v___x_1377_, v___x_1378_, v_inst_1379_, v_R_1380_, v_a_1381_, v_b_1382_, v_c_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v___x_1375_);
lean_dec(v_upperBound_1374_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(lean_object* v_alreadySpecialized_1390_, lean_object* v_as_1391_, lean_object* v_i_1392_, lean_object* v_j_1393_, lean_object* v_inv_1394_, lean_object* v_bs_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_1390_, v_as_1391_, v_i_1392_, v_j_1393_, v_bs_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___boxed(lean_object* v_alreadySpecialized_1397_, lean_object* v_as_1398_, lean_object* v_i_1399_, lean_object* v_j_1400_, lean_object* v_inv_1401_, lean_object* v_bs_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(v_alreadySpecialized_1397_, v_as_1398_, v_i_1399_, v_j_1400_, v_inv_1401_, v_bs_1402_);
lean_dec_ref(v_as_1398_);
lean_dec_ref(v_alreadySpecialized_1397_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(lean_object* v_upperBound_1404_, lean_object* v___x_1405_, lean_object* v_inst_1406_, lean_object* v_R_1407_, lean_object* v_a_1408_, lean_object* v_b_1409_, lean_object* v_c_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_1404_, v___x_1405_, v_a_1408_, v_b_1409_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___boxed(lean_object* v_upperBound_1417_, lean_object* v___x_1418_, lean_object* v_inst_1419_, lean_object* v_R_1420_, lean_object* v_a_1421_, lean_object* v_b_1422_, lean_object* v_c_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(v_upperBound_1417_, v___x_1418_, v_inst_1419_, v_R_1420_, v_a_1421_, v_b_1422_, v_c_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec_ref(v___x_1418_);
lean_dec(v_upperBound_1417_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(lean_object* v_upperBound_1430_, lean_object* v_decls_1431_, lean_object* v_alreadySpecialized_1432_, lean_object* v___x_1433_, lean_object* v_a_1434_, lean_object* v_inst_1435_, lean_object* v_R_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_, lean_object* v_c_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_1430_, v_decls_1431_, v_alreadySpecialized_1432_, v___x_1433_, v_a_1434_, v_a_1437_, v_b_1438_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___boxed(lean_object* v_upperBound_1446_, lean_object* v_decls_1447_, lean_object* v_alreadySpecialized_1448_, lean_object* v___x_1449_, lean_object* v_a_1450_, lean_object* v_inst_1451_, lean_object* v_R_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_, lean_object* v_c_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(v_upperBound_1446_, v_decls_1447_, v_alreadySpecialized_1448_, v___x_1449_, v_a_1450_, v_inst_1451_, v_R_1452_, v_a_1453_, v_b_1454_, v_c_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec_ref(v_a_1450_);
lean_dec(v___x_1449_);
lean_dec_ref(v_alreadySpecialized_1448_);
lean_dec_ref(v_decls_1447_);
lean_dec(v_upperBound_1446_);
return v_res_1461_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1462_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
lean_ctor_set(v___x_1467_, 2, v___x_1466_);
lean_ctor_set(v___x_1467_, 3, v___x_1466_);
lean_ctor_set(v___x_1467_, 4, v___x_1465_);
lean_ctor_set(v___x_1467_, 5, v___x_1465_);
lean_ctor_set(v___x_1467_, 6, v___x_1465_);
lean_ctor_set(v___x_1467_, 7, v___x_1465_);
lean_ctor_set(v___x_1467_, 8, v___x_1465_);
lean_ctor_set(v___x_1467_, 9, v___x_1465_);
return v___x_1467_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1468_; double v___x_1469_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_float_of_nat(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(lean_object* v_cls_1473_, lean_object* v_msg_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_options_1480_; lean_object* v_ref_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_options_1480_ = lean_ctor_get(v___y_1477_, 2);
v_ref_1481_ = lean_ctor_get(v___y_1477_, 5);
v___x_1482_ = lean_st_ref_get(v___y_1478_);
v___x_1483_ = lean_st_ref_get(v___y_1476_);
v___x_1484_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1475_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1543_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1543_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1543_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_env_1489_; lean_object* v_lctx_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1541_; 
v_env_1489_ = lean_ctor_get(v___x_1482_, 0);
lean_inc_ref(v_env_1489_);
lean_dec(v___x_1482_);
v_lctx_1490_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1483_, 1);
lean_dec(v_unused_1542_);
v___x_1492_ = v___x_1483_;
v_isShared_1493_ = v_isSharedCheck_1541_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_lctx_1490_);
lean_dec(v___x_1483_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1541_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_traceState_1496_; lean_object* v_env_1497_; lean_object* v_nextMacroScope_1498_; lean_object* v_ngen_1499_; lean_object* v_auxDeclNGen_1500_; lean_object* v_cache_1501_; lean_object* v_messages_1502_; lean_object* v_infoState_1503_; lean_object* v_snapshotTasks_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1540_; 
v___x_1494_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2);
v___x_1495_ = lean_st_ref_take(v___y_1478_);
v_traceState_1496_ = lean_ctor_get(v___x_1495_, 4);
v_env_1497_ = lean_ctor_get(v___x_1495_, 0);
v_nextMacroScope_1498_ = lean_ctor_get(v___x_1495_, 1);
v_ngen_1499_ = lean_ctor_get(v___x_1495_, 2);
v_auxDeclNGen_1500_ = lean_ctor_get(v___x_1495_, 3);
v_cache_1501_ = lean_ctor_get(v___x_1495_, 5);
v_messages_1502_ = lean_ctor_get(v___x_1495_, 6);
v_infoState_1503_ = lean_ctor_get(v___x_1495_, 7);
v_snapshotTasks_1504_ = lean_ctor_get(v___x_1495_, 8);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1506_ = v___x_1495_;
v_isShared_1507_ = v_isSharedCheck_1540_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_snapshotTasks_1504_);
lean_inc(v_infoState_1503_);
lean_inc(v_messages_1502_);
lean_inc(v_cache_1501_);
lean_inc(v_traceState_1496_);
lean_inc(v_auxDeclNGen_1500_);
lean_inc(v_ngen_1499_);
lean_inc(v_nextMacroScope_1498_);
lean_inc(v_env_1497_);
lean_dec(v___x_1495_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1540_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
uint64_t v_tid_1508_; lean_object* v_traces_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1539_; 
v_tid_1508_ = lean_ctor_get_uint64(v_traceState_1496_, sizeof(void*)*1);
v_traces_1509_ = lean_ctor_get(v_traceState_1496_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_traceState_1496_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1511_ = v_traceState_1496_;
v_isShared_1512_ = v_isSharedCheck_1539_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_traces_1509_);
lean_dec(v_traceState_1496_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1539_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1513_ = lean_unbox(v_a_1485_);
lean_dec(v_a_1485_);
v___x_1514_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1490_, v___x_1513_);
lean_dec_ref(v_lctx_1490_);
lean_inc_ref(v_options_1480_);
v___x_1515_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1515_, 0, v_env_1489_);
lean_ctor_set(v___x_1515_, 1, v___x_1494_);
lean_ctor_set(v___x_1515_, 2, v___x_1514_);
lean_ctor_set(v___x_1515_, 3, v_options_1480_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 3);
lean_ctor_set(v___x_1492_, 1, v_msg_1474_);
lean_ctor_set(v___x_1492_, 0, v___x_1515_);
v___x_1517_ = v___x_1492_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_msg_1474_);
v___x_1517_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; double v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3);
v___x_1520_ = 0;
v___x_1521_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4));
v___x_1522_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1522_, 0, v_cls_1473_);
lean_ctor_set(v___x_1522_, 1, v___x_1518_);
lean_ctor_set(v___x_1522_, 2, v___x_1521_);
lean_ctor_set_float(v___x_1522_, sizeof(void*)*3, v___x_1519_);
lean_ctor_set_float(v___x_1522_, sizeof(void*)*3 + 8, v___x_1519_);
lean_ctor_set_uint8(v___x_1522_, sizeof(void*)*3 + 16, v___x_1520_);
v___x_1523_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5));
v___x_1524_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1517_);
lean_ctor_set(v___x_1524_, 2, v___x_1523_);
lean_inc(v_ref_1481_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_ref_1481_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = l_Lean_PersistentArray_push___redArg(v_traces_1509_, v___x_1525_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1526_);
v___x_1528_ = v___x_1511_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1526_);
lean_ctor_set_uint64(v_reuseFailAlloc_1537_, sizeof(void*)*1, v_tid_1508_);
v___x_1528_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 4, v___x_1528_);
v___x_1530_ = v___x_1506_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_env_1497_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_nextMacroScope_1498_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_ngen_1499_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_auxDeclNGen_1500_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1536_, 5, v_cache_1501_);
lean_ctor_set(v_reuseFailAlloc_1536_, 6, v_messages_1502_);
lean_ctor_set(v_reuseFailAlloc_1536_, 7, v_infoState_1503_);
lean_ctor_set(v_reuseFailAlloc_1536_, 8, v_snapshotTasks_1504_);
v___x_1530_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1531_ = lean_st_ref_set(v___y_1478_, v___x_1530_);
v___x_1532_ = lean_box(0);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1532_);
v___x_1534_ = v___x_1487_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
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
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v___x_1483_);
lean_dec(v___x_1482_);
lean_dec_ref(v_msg_1474_);
lean_dec(v_cls_1473_);
v_a_1544_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1484_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1484_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___boxed(lean_object* v_cls_1552_, lean_object* v_msg_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v_cls_1552_, v_msg_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1559_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(lean_object* v_xs_1560_, lean_object* v_ys_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v_zero_1563_; uint8_t v_isZero_1564_; 
v_zero_1563_ = lean_unsigned_to_nat(0u);
v_isZero_1564_ = lean_nat_dec_eq(v_x_1562_, v_zero_1563_);
if (v_isZero_1564_ == 1)
{
lean_dec(v_x_1562_);
return v_isZero_1564_;
}
else
{
lean_object* v_one_1565_; lean_object* v_n_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_one_1565_ = lean_unsigned_to_nat(1u);
v_n_1566_ = lean_nat_sub(v_x_1562_, v_one_1565_);
lean_dec(v_x_1562_);
v___x_1567_ = lean_array_fget_borrowed(v_xs_1560_, v_n_1566_);
v___x_1568_ = lean_array_fget_borrowed(v_ys_1561_, v_n_1566_);
v___x_1569_ = lean_nat_dec_eq(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_dec(v_n_1566_);
return v___x_1569_;
}
else
{
v_x_1562_ = v_n_1566_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg___boxed(lean_object* v_xs_1571_, lean_object* v_ys_1572_, lean_object* v_x_1573_){
_start:
{
uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_res_1574_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1571_, v_ys_1572_, v_x_1573_);
lean_dec_ref(v_ys_1572_);
lean_dec_ref(v_xs_1571_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(lean_object* v_x_1576_, lean_object* v_x_1577_){
_start:
{
if (lean_obj_tag(v_x_1576_) == 0)
{
if (lean_obj_tag(v_x_1577_) == 0)
{
uint8_t v___x_1578_; 
v___x_1578_ = 1;
return v___x_1578_;
}
else
{
uint8_t v___x_1579_; 
v___x_1579_ = 0;
return v___x_1579_;
}
}
else
{
if (lean_obj_tag(v_x_1577_) == 0)
{
uint8_t v___x_1580_; 
v___x_1580_ = 0;
return v___x_1580_;
}
else
{
lean_object* v_val_1581_; lean_object* v_val_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v_val_1581_ = lean_ctor_get(v_x_1576_, 0);
v_val_1582_ = lean_ctor_get(v_x_1577_, 0);
v___x_1583_ = lean_array_get_size(v_val_1581_);
v___x_1584_ = lean_array_get_size(v_val_1582_);
v___x_1585_ = lean_nat_dec_eq(v___x_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
return v___x_1585_;
}
else
{
uint8_t v___x_1586_; 
v___x_1586_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_val_1581_, v_val_1582_, v___x_1583_);
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0___boxed(lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_x_1587_, v_x_1588_);
lean_dec(v_x_1588_);
lean_dec(v_x_1587_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(lean_object* v_x_1593_, lean_object* v_specArgs_x3f_1594_){
_start:
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = ((lean_object*)(l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0));
v___x_1596_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(v_specArgs_x3f_1594_, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed(lean_object* v_x_1597_, lean_object* v_specArgs_x3f_1598_){
_start:
{
uint8_t v_res_1599_; lean_object* v_r_1600_; 
v_res_1599_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(v_x_1597_, v_specArgs_x3f_1598_);
lean_dec(v_specArgs_x3f_1598_);
lean_dec(v_x_1597_);
v_r_1600_ = lean_box(v_res_1599_);
return v_r_1600_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
if (lean_obj_tag(v_a_1601_) == 0)
{
lean_object* v___x_1603_; 
v___x_1603_ = l_List_reverse___redArg(v_a_1602_);
return v___x_1603_;
}
else
{
lean_object* v_head_1604_; lean_object* v_tail_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1622_; 
v_head_1604_ = lean_ctor_get(v_a_1601_, 0);
v_tail_1605_ = lean_ctor_get(v_a_1601_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_a_1601_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1607_ = v_a_1601_;
v_isShared_1608_ = v_isSharedCheck_1622_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_tail_1605_);
lean_inc(v_head_1604_);
lean_dec(v_a_1601_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1622_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___y_1610_; 
switch(lean_obj_tag(v_head_1604_))
{
case 0:
{
uint8_t v_weak_1615_; 
v_weak_1615_ = lean_ctor_get_uint8(v_head_1604_, 0);
lean_dec_ref(v_head_1604_);
if (v_weak_1615_ == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
v___y_1610_ = v___x_1616_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
v___y_1610_ = v___x_1617_;
goto v___jp_1609_;
}
}
case 1:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8);
v___y_1610_ = v___x_1618_;
goto v___jp_1609_;
}
case 2:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11);
v___y_1610_ = v___x_1619_;
goto v___jp_1609_;
}
case 3:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14);
v___y_1610_ = v___x_1620_;
goto v___jp_1609_;
}
default: 
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_obj_once(&l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17, &l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once, _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17);
v___y_1610_ = v___x_1621_;
goto v___jp_1609_;
}
}
v___jp_1609_:
{
lean_object* v___x_1612_; 
lean_inc_ref(v___y_1610_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 1, v_a_1602_);
lean_ctor_set(v___x_1607_, 0, v___y_1610_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___y_1610_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_a_1602_);
v___x_1612_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
v_a_1601_ = v_tail_1605_;
v_a_1602_ = v___x_1612_;
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
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1623_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_1638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7));
v___x_1639_ = l_Lean_Name_append(v___x_1638_, v___x_1637_);
return v___x_1639_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9));
v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(lean_object* v_as_1643_, size_t v_sz_1644_, size_t v_i_1645_, lean_object* v_b_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_a_1653_; uint8_t v___x_1657_; 
v___x_1657_ = lean_usize_dec_lt(v_i_1645_, v_sz_1644_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_b_1646_);
return v___x_1658_;
}
else
{
lean_object* v_a_1659_; lean_object* v_declName_1660_; lean_object* v_paramsInfo_1661_; lean_object* v___x_1662_; lean_object* v___y_1664_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v_a_1659_ = lean_array_uget_borrowed(v_as_1643_, v_i_1645_);
v_declName_1660_ = lean_ctor_get(v_a_1659_, 0);
v_paramsInfo_1661_ = lean_ctor_get(v_a_1659_, 1);
v___x_1662_ = lean_box(0);
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = lean_array_get_size(v_paramsInfo_1661_);
v___x_1691_ = lean_nat_dec_lt(v___x_1689_, v___x_1690_);
if (v___x_1691_ == 0)
{
v_a_1653_ = v___x_1662_;
goto v___jp_1652_;
}
else
{
if (v___x_1691_ == 0)
{
v_a_1653_ = v___x_1662_;
goto v___jp_1652_;
}
else
{
size_t v___x_1692_; size_t v___x_1693_; uint8_t v___x_1694_; 
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = lean_usize_of_nat(v___x_1690_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_paramsInfo_1661_, v___x_1692_, v___x_1693_);
if (v___x_1694_ == 0)
{
v_a_1653_ = v___x_1662_;
goto v___jp_1652_;
}
else
{
lean_object* v_options_1695_; uint8_t v_hasTrace_1696_; 
v_options_1695_ = lean_ctor_get(v___y_1649_, 2);
v_hasTrace_1696_ = lean_ctor_get_uint8(v_options_1695_, sizeof(void*)*1);
if (v_hasTrace_1696_ == 0)
{
v___y_1664_ = v___y_1650_;
goto v___jp_1663_;
}
else
{
lean_object* v_inheritedTraceOptions_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_inheritedTraceOptions_1697_ = lean_ctor_get(v___y_1649_, 13);
v___x_1698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_1699_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8);
v___x_1700_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1697_, v_options_1695_, v___x_1699_);
if (v___x_1700_ == 0)
{
v___y_1664_ = v___y_1650_;
goto v___jp_1663_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_inc(v_declName_1660_);
v___x_1701_ = l_Lean_MessageData_ofName(v_declName_1660_);
v___x_1702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
lean_inc_ref(v_paramsInfo_1661_);
v___x_1704_ = lean_array_to_list(v_paramsInfo_1661_);
v___x_1705_ = lean_box(0);
v___x_1706_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(v___x_1704_, v___x_1705_);
v___x_1707_ = l_Lean_MessageData_ofList(v___x_1706_);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1703_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v___x_1698_, v___x_1708_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_dec_ref(v___x_1709_);
v___y_1664_ = v___y_1650_;
goto v___jp_1663_;
}
else
{
return v___x_1709_;
}
}
}
}
}
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v_env_1666_; lean_object* v_nextMacroScope_1667_; lean_object* v_ngen_1668_; lean_object* v_auxDeclNGen_1669_; lean_object* v_traceState_1670_; lean_object* v_messages_1671_; lean_object* v_infoState_1672_; lean_object* v_snapshotTasks_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1687_; 
v___x_1665_ = lean_st_ref_take(v___y_1664_);
v_env_1666_ = lean_ctor_get(v___x_1665_, 0);
v_nextMacroScope_1667_ = lean_ctor_get(v___x_1665_, 1);
v_ngen_1668_ = lean_ctor_get(v___x_1665_, 2);
v_auxDeclNGen_1669_ = lean_ctor_get(v___x_1665_, 3);
v_traceState_1670_ = lean_ctor_get(v___x_1665_, 4);
v_messages_1671_ = lean_ctor_get(v___x_1665_, 6);
v_infoState_1672_ = lean_ctor_get(v___x_1665_, 7);
v_snapshotTasks_1673_ = lean_ctor_get(v___x_1665_, 8);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v___x_1665_, 5);
lean_dec(v_unused_1688_);
v___x_1675_ = v___x_1665_;
v_isShared_1676_ = v_isSharedCheck_1687_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_snapshotTasks_1673_);
lean_inc(v_infoState_1672_);
lean_inc(v_messages_1671_);
lean_inc(v_traceState_1670_);
lean_inc(v_auxDeclNGen_1669_);
lean_inc(v_ngen_1668_);
lean_inc(v_nextMacroScope_1667_);
lean_inc(v_env_1666_);
lean_dec(v___x_1665_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1687_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v_toEnvExtension_1678_; lean_object* v_asyncMode_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1677_ = l_Lean_Compiler_LCNF_specExtension;
v_toEnvExtension_1678_ = lean_ctor_get(v___x_1677_, 0);
v_asyncMode_1679_ = lean_ctor_get(v_toEnvExtension_1678_, 2);
v___x_1680_ = lean_box(0);
lean_inc(v_a_1659_);
v___x_1681_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1677_, v_env_1666_, v_a_1659_, v_asyncMode_1679_, v___x_1680_);
v___x_1682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 5, v___x_1682_);
lean_ctor_set(v___x_1675_, 0, v___x_1681_);
v___x_1684_ = v___x_1675_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_nextMacroScope_1667_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_ngen_1668_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_auxDeclNGen_1669_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_traceState_1670_);
lean_ctor_set(v_reuseFailAlloc_1686_, 5, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1686_, 6, v_messages_1671_);
lean_ctor_set(v_reuseFailAlloc_1686_, 7, v_infoState_1672_);
lean_ctor_set(v_reuseFailAlloc_1686_, 8, v_snapshotTasks_1673_);
v___x_1684_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_st_ref_set(v___y_1664_, v___x_1684_);
v_a_1653_ = v___x_1662_;
goto v___jp_1652_;
}
}
}
}
v___jp_1652_:
{
size_t v___x_1654_; size_t v___x_1655_; 
v___x_1654_ = ((size_t)1ULL);
v___x_1655_ = lean_usize_add(v_i_1645_, v___x_1654_);
v_i_1645_ = v___x_1655_;
v_b_1646_ = v_a_1653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___boxed(lean_object* v_as_1710_, lean_object* v_sz_1711_, lean_object* v_i_1712_, lean_object* v_b_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
size_t v_sz_boxed_1719_; size_t v_i_boxed_1720_; lean_object* v_res_1721_; 
v_sz_boxed_1719_ = lean_unbox_usize(v_sz_1711_);
lean_dec(v_sz_1711_);
v_i_boxed_1720_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_as_1710_, v_sz_boxed_1719_, v_i_boxed_1720_, v_b_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec_ref(v_as_1710_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries(lean_object* v_decls_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___f_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___f_1729_ = ((lean_object*)(l_Lean_Compiler_LCNF_saveSpecEntries___closed__0));
v___x_1730_ = lean_array_get_size(v_decls_1723_);
v___x_1731_ = 0;
v___x_1732_ = lean_box(v___x_1731_);
v___x_1733_ = lean_mk_array(v___x_1730_, v___x_1732_);
v___x_1734_ = l_Lean_Compiler_LCNF_computeSpecEntries(v_decls_1723_, v___f_1729_, v___x_1733_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
lean_dec_ref(v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; size_t v_sz_1737_; size_t v___x_1738_; lean_object* v___x_1739_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = lean_box(0);
v_sz_1737_ = lean_array_size(v_a_1735_);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_a_1735_, v_sz_1737_, v___x_1738_, v___x_1736_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
lean_dec(v_a_1735_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1739_, 0);
lean_dec(v_unused_1747_);
v___x_1741_ = v___x_1739_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_dec(v___x_1739_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1736_);
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1736_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
return v___x_1739_;
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_a_1748_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1734_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1734_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveSpecEntries___boxed(lean_object* v_decls_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_Compiler_LCNF_saveSpecEntries(v_decls_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
return v_res_1762_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(lean_object* v_xs_1763_, lean_object* v_ys_1764_, lean_object* v_hsz_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
uint8_t v___x_1768_; 
v___x_1768_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_1763_, v_ys_1764_, v_x_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___boxed(lean_object* v_xs_1769_, lean_object* v_ys_1770_, lean_object* v_hsz_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
uint8_t v_res_1774_; lean_object* v_r_1775_; 
v_res_1774_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(v_xs_1769_, v_ys_1770_, v_hsz_1771_, v_x_1772_, v_x_1773_);
lean_dec_ref(v_ys_1770_);
lean_dec_ref(v_xs_1769_);
v_r_1775_ = lean_box(v_res_1774_);
return v_r_1775_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(lean_object* v_as_1776_, lean_object* v_k_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_m_1782_; lean_object* v_a_1783_; uint8_t v___x_1784_; 
v___x_1780_ = lean_nat_add(v_x_1778_, v_x_1779_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v_m_1782_ = lean_nat_shiftr(v___x_1780_, v___x_1781_);
lean_dec(v___x_1780_);
v_a_1783_ = lean_array_fget_borrowed(v_as_1776_, v_m_1782_);
v___x_1784_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_a_1783_, v_k_1777_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
lean_dec(v_x_1779_);
v___x_1785_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_k_1777_, v_a_1783_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; 
lean_dec(v_m_1782_);
lean_dec(v_x_1778_);
lean_inc(v_a_1783_);
v___x_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_a_1783_);
return v___x_1786_;
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_nat_dec_eq(v_m_1782_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = lean_nat_sub(v_m_1782_, v___x_1781_);
lean_dec(v_m_1782_);
v___x_1790_ = lean_nat_dec_lt(v___x_1789_, v_x_1778_);
if (v___x_1790_ == 0)
{
v_x_1779_ = v___x_1789_;
goto _start;
}
else
{
lean_object* v___x_1792_; 
lean_dec(v___x_1789_);
lean_dec(v_x_1778_);
v___x_1792_ = lean_box(0);
return v___x_1792_;
}
}
else
{
lean_object* v___x_1793_; 
lean_dec(v_m_1782_);
lean_dec(v_x_1778_);
v___x_1793_ = lean_box(0);
return v___x_1793_;
}
}
}
else
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
lean_dec(v_x_1778_);
v___x_1794_ = lean_nat_add(v_m_1782_, v___x_1781_);
lean_dec(v_m_1782_);
v___x_1795_ = lean_nat_dec_le(v___x_1794_, v_x_1779_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; 
lean_dec(v___x_1794_);
lean_dec(v_x_1779_);
v___x_1796_ = lean_box(0);
return v___x_1796_;
}
else
{
v_x_1778_ = v___x_1794_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg___boxed(lean_object* v_as_1798_, lean_object* v_k_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v_as_1798_, v_k_1799_, v_x_1800_, v_x_1801_);
lean_dec_ref(v_k_1799_);
lean_dec_ref(v_as_1798_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1803_, lean_object* v_vals_1804_, lean_object* v_i_1805_, lean_object* v_k_1806_){
_start:
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = lean_array_get_size(v_keys_1803_);
v___x_1808_ = lean_nat_dec_lt(v_i_1805_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_dec(v_i_1805_);
v___x_1809_ = lean_box(0);
return v___x_1809_;
}
else
{
lean_object* v_k_x27_1810_; uint8_t v___x_1811_; 
v_k_x27_1810_ = lean_array_fget_borrowed(v_keys_1803_, v_i_1805_);
v___x_1811_ = lean_name_eq(v_k_1806_, v_k_x27_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_nat_add(v_i_1805_, v___x_1812_);
lean_dec(v_i_1805_);
v_i_1805_ = v___x_1813_;
goto _start;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_array_fget_borrowed(v_vals_1804_, v_i_1805_);
lean_dec(v_i_1805_);
lean_inc(v___x_1815_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1817_, lean_object* v_vals_1818_, lean_object* v_i_1819_, lean_object* v_k_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1817_, v_vals_1818_, v_i_1819_, v_k_1820_);
lean_dec(v_k_1820_);
lean_dec_ref(v_vals_1818_);
lean_dec_ref(v_keys_1817_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_1822_, size_t v_x_1823_, lean_object* v_x_1824_){
_start:
{
if (lean_obj_tag(v_x_1822_) == 0)
{
lean_object* v_es_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1846_; 
v_es_1825_ = lean_ctor_get(v_x_1822_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_x_1822_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1827_ = v_x_1822_;
v_isShared_1828_ = v_isSharedCheck_1846_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_es_1825_);
lean_dec(v_x_1822_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1846_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; size_t v___x_1830_; size_t v___x_1831_; size_t v___x_1832_; lean_object* v_j_1833_; lean_object* v___x_1834_; 
v___x_1829_ = lean_box(2);
v___x_1830_ = ((size_t)5ULL);
v___x_1831_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
v___x_1832_ = lean_usize_land(v_x_1823_, v___x_1831_);
v_j_1833_ = lean_usize_to_nat(v___x_1832_);
v___x_1834_ = lean_array_get(v___x_1829_, v_es_1825_, v_j_1833_);
lean_dec(v_j_1833_);
lean_dec_ref(v_es_1825_);
switch(lean_obj_tag(v___x_1834_))
{
case 0:
{
lean_object* v_key_1835_; lean_object* v_val_1836_; uint8_t v___x_1837_; 
v_key_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_key_1835_);
v_val_1836_ = lean_ctor_get(v___x_1834_, 1);
lean_inc(v_val_1836_);
lean_dec_ref(v___x_1834_);
v___x_1837_ = lean_name_eq(v_x_1824_, v_key_1835_);
lean_dec(v_key_1835_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_dec(v_val_1836_);
lean_del_object(v___x_1827_);
v___x_1838_ = lean_box(0);
return v___x_1838_;
}
else
{
lean_object* v___x_1840_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 1);
lean_ctor_set(v___x_1827_, 0, v_val_1836_);
v___x_1840_ = v___x_1827_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_val_1836_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
case 1:
{
lean_object* v_node_1842_; size_t v___x_1843_; 
lean_del_object(v___x_1827_);
v_node_1842_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_node_1842_);
lean_dec_ref(v___x_1834_);
v___x_1843_ = lean_usize_shift_right(v_x_1823_, v___x_1830_);
v_x_1822_ = v_node_1842_;
v_x_1823_ = v___x_1843_;
goto _start;
}
default: 
{
lean_object* v___x_1845_; 
lean_del_object(v___x_1827_);
v___x_1845_ = lean_box(0);
return v___x_1845_;
}
}
}
}
else
{
lean_object* v_ks_1847_; lean_object* v_vs_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_ks_1847_ = lean_ctor_get(v_x_1822_, 0);
lean_inc_ref(v_ks_1847_);
v_vs_1848_ = lean_ctor_get(v_x_1822_, 1);
lean_inc_ref(v_vs_1848_);
lean_dec_ref(v_x_1822_);
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1850_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1847_, v_vs_1848_, v___x_1849_, v_x_1824_);
lean_dec_ref(v_vs_1848_);
lean_dec_ref(v_ks_1847_);
return v___x_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_){
_start:
{
size_t v_x_413__boxed_1854_; lean_object* v_res_1855_; 
v_x_413__boxed_1854_ = lean_unbox_usize(v_x_1852_);
lean_dec(v_x_1852_);
v_res_1855_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1851_, v_x_413__boxed_1854_, v_x_1853_);
lean_dec(v_x_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
uint64_t v___y_1859_; 
if (lean_obj_tag(v_x_1857_) == 0)
{
uint64_t v___x_1862_; 
v___x_1862_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1859_ = v___x_1862_;
goto v___jp_1858_;
}
else
{
uint64_t v_hash_1863_; 
v_hash_1863_ = lean_ctor_get_uint64(v_x_1857_, sizeof(void*)*2);
v___y_1859_ = v_hash_1863_;
goto v___jp_1858_;
}
v___jp_1858_:
{
size_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_uint64_to_usize(v___y_1859_);
v___x_1861_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1856_, v___x_1860_, v_x_1857_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg___boxed(lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_1864_, v_x_1865_);
lean_dec(v_x_1865_);
return v_res_1866_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
v___x_1868_ = lean_box(0);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v___x_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(lean_object* v_env_1870_, lean_object* v_declName_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1881_; 
v___x_1872_ = lean_obj_once(&l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0, &l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0);
v___x_1873_ = l_Lean_Compiler_LCNF_specExtension;
v___x_1881_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1870_, v_declName_1871_);
if (lean_obj_tag(v___x_1881_) == 0)
{
goto v___jp_1874_;
}
else
{
lean_object* v_val_1882_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v_val_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_val_1882_);
lean_dec_ref(v___x_1881_);
v___x_1896_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1872_, v___x_1873_, v_env_1870_, v_val_1882_);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_array_get_size(v___x_1896_);
v___x_1899_ = lean_nat_dec_lt(v___x_1897_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_dec_ref(v___x_1896_);
goto v___jp_1883_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1900_ = lean_unsigned_to_nat(1u);
v___x_1901_ = lean_nat_sub(v___x_1898_, v___x_1900_);
v___x_1902_ = lean_nat_dec_le(v___x_1897_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_dec(v___x_1901_);
lean_dec_ref(v___x_1896_);
goto v___jp_1883_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1904_ = 0;
lean_inc(v_declName_1871_);
v___x_1905_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1905_, 0, v_declName_1871_);
lean_ctor_set(v___x_1905_, 1, v___x_1903_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*2, v___x_1904_);
v___x_1906_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_1896_, v___x_1905_, v___x_1897_, v___x_1901_);
lean_dec_ref(v___x_1905_);
lean_dec_ref(v___x_1896_);
if (lean_obj_tag(v___x_1906_) == 0)
{
goto v___jp_1883_;
}
else
{
lean_dec(v_val_1882_);
lean_dec(v_declName_1871_);
lean_dec_ref(v_env_1870_);
return v___x_1906_;
}
}
}
v___jp_1883_:
{
uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1884_ = 0;
v___x_1885_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1872_, v___x_1873_, v_env_1870_, v_val_1882_, v___x_1884_);
lean_dec(v_val_1882_);
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = lean_array_get_size(v___x_1885_);
v___x_1888_ = lean_nat_dec_lt(v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_dec_ref(v___x_1885_);
goto v___jp_1874_;
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1889_ = lean_unsigned_to_nat(1u);
v___x_1890_ = lean_nat_sub(v___x_1887_, v___x_1889_);
v___x_1891_ = lean_nat_dec_le(v___x_1886_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_dec(v___x_1890_);
lean_dec_ref(v___x_1885_);
goto v___jp_1874_;
}
else
{
lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0));
v___x_1893_ = 0;
lean_inc(v_declName_1871_);
v___x_1894_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1894_, 0, v_declName_1871_);
lean_ctor_set(v___x_1894_, 1, v___x_1892_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*2, v___x_1893_);
v___x_1895_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_1885_, v___x_1894_, v___x_1886_, v___x_1890_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v___x_1885_);
if (lean_obj_tag(v___x_1895_) == 0)
{
goto v___jp_1874_;
}
else
{
lean_dec(v_declName_1871_);
lean_dec_ref(v_env_1870_);
return v___x_1895_;
}
}
}
}
}
v___jp_1874_:
{
lean_object* v_toEnvExtension_1875_; lean_object* v_asyncMode_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_snd_1879_; lean_object* v___x_1880_; 
v_toEnvExtension_1875_ = lean_ctor_get(v___x_1873_, 0);
v_asyncMode_1876_ = lean_ctor_get(v_toEnvExtension_1875_, 2);
v___x_1877_ = lean_box(0);
v___x_1878_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1872_, v___x_1873_, v_env_1870_, v_asyncMode_1876_, v___x_1877_);
v_snd_1879_ = lean_ctor_get(v___x_1878_, 1);
lean_inc(v_snd_1879_);
lean_dec(v___x_1878_);
v___x_1880_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_snd_1879_, v_declName_1871_);
lean_dec(v_declName_1871_);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(lean_object* v_00_u03b2_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_1908_, v_x_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_1911_, lean_object* v_x_1912_, lean_object* v_x_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(v_00_u03b2_1911_, v_x_1912_, v_x_1913_);
lean_dec(v_x_1913_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(lean_object* v_as_1915_, lean_object* v_k_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v_as_1915_, v_k_1916_, v_x_1917_, v_x_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___boxed(lean_object* v_as_1921_, lean_object* v_k_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(v_as_1921_, v_k_1922_, v_x_1923_, v_x_1924_, v_x_1925_);
lean_dec_ref(v_k_1922_);
lean_dec_ref(v_as_1921_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1927_, lean_object* v_x_1928_, size_t v_x_1929_, lean_object* v_x_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_1928_, v_x_1929_, v_x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_, lean_object* v_x_1935_){
_start:
{
size_t v_x_591__boxed_1936_; lean_object* v_res_1937_; 
v_x_591__boxed_1936_ = lean_unbox_usize(v_x_1934_);
lean_dec(v_x_1934_);
v_res_1937_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(v_00_u03b2_1932_, v_x_1933_, v_x_591__boxed_1936_, v_x_1935_);
lean_dec(v_x_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1938_, lean_object* v_keys_1939_, lean_object* v_vals_1940_, lean_object* v_heq_1941_, lean_object* v_i_1942_, lean_object* v_k_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1939_, v_vals_1940_, v_i_1942_, v_k_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1945_, lean_object* v_keys_1946_, lean_object* v_vals_1947_, lean_object* v_heq_1948_, lean_object* v_i_1949_, lean_object* v_k_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1945_, v_keys_1946_, v_vals_1947_, v_heq_1948_, v_i_1949_, v_k_1950_);
lean_dec(v_k_1950_);
lean_dec_ref(v_vals_1947_);
lean_dec_ref(v_keys_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0(lean_object* v_declName_1952_, lean_object* v_toPure_1953_, lean_object* v_____do__lift_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_1954_, v_declName_1952_);
v___x_1956_ = lean_apply_2(v_toPure_1953_, lean_box(0), v___x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_declName_1959_){
_start:
{
lean_object* v_toApplicative_1960_; lean_object* v_toBind_1961_; lean_object* v_getEnv_1962_; lean_object* v_toPure_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; 
v_toApplicative_1960_ = lean_ctor_get(v_inst_1957_, 0);
lean_inc_ref(v_toApplicative_1960_);
v_toBind_1961_ = lean_ctor_get(v_inst_1957_, 1);
lean_inc(v_toBind_1961_);
lean_dec_ref(v_inst_1957_);
v_getEnv_1962_ = lean_ctor_get(v_inst_1958_, 0);
lean_inc(v_getEnv_1962_);
lean_dec_ref(v_inst_1958_);
v_toPure_1963_ = lean_ctor_get(v_toApplicative_1960_, 1);
lean_inc(v_toPure_1963_);
lean_dec_ref(v_toApplicative_1960_);
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1964_, 0, v_declName_1959_);
lean_closure_set(v___f_1964_, 1, v_toPure_1963_);
v___x_1965_ = lean_apply_4(v_toBind_1961_, lean_box(0), lean_box(0), v_getEnv_1962_, v___f_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecEntry_x3f(lean_object* v_m_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_declName_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(v_inst_1967_, v_inst_1968_, v_declName_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0(lean_object* v_declName_1971_, lean_object* v_toPure_1972_, lean_object* v_____do__lift_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_1973_, v_declName_1971_);
if (lean_obj_tag(v___x_1974_) == 0)
{
uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = 0;
v___x_1976_ = lean_box(v___x_1975_);
v___x_1977_ = lean_apply_2(v_toPure_1972_, lean_box(0), v___x_1976_);
return v___x_1977_;
}
else
{
uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v___x_1974_);
v___x_1978_ = 1;
v___x_1979_ = lean_box(v___x_1978_);
v___x_1980_ = lean_apply_2(v_toPure_1972_, lean_box(0), v___x_1979_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate___redArg(lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_declName_1983_){
_start:
{
lean_object* v_toApplicative_1984_; lean_object* v_toBind_1985_; lean_object* v_getEnv_1986_; lean_object* v_toPure_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; 
v_toApplicative_1984_ = lean_ctor_get(v_inst_1981_, 0);
lean_inc_ref(v_toApplicative_1984_);
v_toBind_1985_ = lean_ctor_get(v_inst_1981_, 1);
lean_inc(v_toBind_1985_);
lean_dec_ref(v_inst_1981_);
v_getEnv_1986_ = lean_ctor_get(v_inst_1982_, 0);
lean_inc(v_getEnv_1986_);
lean_dec_ref(v_inst_1982_);
v_toPure_1987_ = lean_ctor_get(v_toApplicative_1984_, 1);
lean_inc(v_toPure_1987_);
lean_dec_ref(v_toApplicative_1984_);
v___f_1988_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1988_, 0, v_declName_1983_);
lean_closure_set(v___f_1988_, 1, v_toPure_1987_);
v___x_1989_ = lean_apply_4(v_toBind_1985_, lean_box(0), lean_box(0), v_getEnv_1986_, v___f_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isSpecCandidate(lean_object* v_m_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_declName_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Compiler_LCNF_isSpecCandidate___redArg(v_inst_1991_, v_inst_1992_, v_declName_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5));
v___x_2060_ = 0;
v___x_2061_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_));
v___x_2062_ = l_Lean_registerTraceClass(v___x_2059_, v___x_2060_, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2____boxed(lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
return v_res_2064_;
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
