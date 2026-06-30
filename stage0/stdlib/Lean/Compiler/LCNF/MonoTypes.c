// Lean compiler output
// Module: Lean.Compiler.LCNF.MonoTypes
// Imports: public import Lean.Compiler.LCNF.Util public import Lean.Compiler.LCNF.BaseTypes public import Lean.Compiler.LCNF.Irrelevant
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MonoTypes"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 163, 188, 36, 234, 230, 12, 164)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(15, 104, 138, 221, 40, 128, 66, 209)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 193, 97, 55, 202, 162, 3, 38)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 79, 120, 160, 44, 67, 75, 103)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 5, 59, 84, 4, 22, 180, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "trivialStructureInfoExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(9, 26, 11, 215, 188, 118, 90, 171)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_getParamTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_getParamTypes___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getParamTypes___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_toMonoType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toMonoType___closed__0;
static const lean_string_object l_Lean_Compiler_LCNF_toMonoType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l_Lean_Compiler_LCNF_toMonoType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_toMonoType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.toMonoType.visitApp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Compiler.LCNF.MonoTypes"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lcAny"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "monoTypeExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 30, 14, 157, 163, 232, 91, 18)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoTypeExt;
static lean_once_cell_t l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "` was not compiled; `compileDecls` must run on inductive types first"};
static const lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(lean_object* v_env_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_, lean_object* v_b_5_){
_start:
{
lean_object* v___y_7_; uint8_t v___x_11_; 
v___x_11_ = lean_usize_dec_eq(v_i_3_, v_stop_4_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v_fst_13_; uint8_t v___x_14_; 
v___x_12_ = lean_array_uget_borrowed(v_as_2_, v_i_3_);
v_fst_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_fst_13_);
lean_inc_ref(v_env_1_);
v___x_14_ = l_Lean_Environment_contains(v_env_1_, v_fst_13_, v___x_11_);
if (v___x_14_ == 0)
{
v___y_7_ = v_b_5_;
goto v___jp_6_;
}
else
{
lean_object* v___x_15_; 
lean_inc(v___x_12_);
v___x_15_ = lean_array_push(v_b_5_, v___x_12_);
v___y_7_ = v___x_15_;
goto v___jp_6_;
}
}
else
{
lean_dec_ref(v_env_1_);
return v_b_5_;
}
v___jp_6_:
{
size_t v___x_8_; size_t v___x_9_; 
v___x_8_ = ((size_t)1ULL);
v___x_9_ = lean_usize_add(v_i_3_, v___x_8_);
v_i_3_ = v___x_9_;
v_b_5_ = v___y_7_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_16_, lean_object* v_as_17_, lean_object* v_i_18_, lean_object* v_stop_19_, lean_object* v_b_20_){
_start:
{
size_t v_i_boxed_21_; size_t v_stop_boxed_22_; lean_object* v_res_23_; 
v_i_boxed_21_ = lean_unbox_usize(v_i_18_);
lean_dec(v_i_18_);
v_stop_boxed_22_ = lean_unbox_usize(v_stop_19_);
lean_dec(v_stop_19_);
v_res_23_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(v_env_16_, v_as_17_, v_i_boxed_21_, v_stop_boxed_22_, v_b_20_);
lean_dec_ref(v_as_17_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_24_, lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v_k_26_; lean_object* v_v_27_; lean_object* v_l_28_; lean_object* v_r_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_k_26_ = lean_ctor_get(v_x_25_, 1);
v_v_27_ = lean_ctor_get(v_x_25_, 2);
v_l_28_ = lean_ctor_get(v_x_25_, 3);
v_r_29_ = lean_ctor_get(v_x_25_, 4);
v___x_30_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0_spec__0(v_init_24_, v_l_28_);
lean_inc(v_v_27_);
lean_inc(v_k_26_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v_k_26_);
lean_ctor_set(v___x_31_, 1, v_v_27_);
v___x_32_ = lean_array_push(v___x_30_, v___x_31_);
v_init_24_ = v___x_32_;
v_x_25_ = v_r_29_;
goto _start;
}
else
{
return v_init_24_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0_spec__0(v_init_34_, v_x_35_);
lean_dec(v_x_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(lean_object* v___x_37_, lean_object* v_env_38_, lean_object* v_s_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_40_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_41_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0_spec__0(v___x_40_, v_s_39_);
v___x_42_ = lean_array_get_size(v___x_41_);
v___x_43_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_44_ = lean_nat_dec_lt(v___x_37_, v___x_42_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
lean_dec_ref(v___x_41_);
lean_dec_ref(v_env_38_);
lean_inc_ref_n(v___x_43_, 2);
v___x_45_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_43_);
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = lean_nat_dec_le(v___x_42_, v___x_42_);
if (v___x_46_ == 0)
{
if (v___x_44_ == 0)
{
lean_object* v___x_47_; 
lean_dec_ref(v___x_41_);
lean_dec_ref(v_env_38_);
lean_inc_ref_n(v___x_43_, 2);
v___x_47_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_47_, 0, v___x_43_);
lean_ctor_set(v___x_47_, 1, v___x_43_);
lean_ctor_set(v___x_47_, 2, v___x_43_);
return v___x_47_;
}
else
{
size_t v___x_48_; size_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_48_ = ((size_t)0ULL);
v___x_49_ = lean_usize_of_nat(v___x_42_);
v___x_50_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(v_env_38_, v___x_41_, v___x_48_, v___x_49_, v___x_43_);
lean_dec_ref(v___x_41_);
lean_inc_ref_n(v___x_50_, 2);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
lean_ctor_set(v___x_51_, 2, v___x_50_);
return v___x_51_;
}
}
else
{
size_t v___x_52_; size_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = ((size_t)0ULL);
v___x_53_ = lean_usize_of_nat(v___x_42_);
v___x_54_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(v_env_38_, v___x_41_, v___x_52_, v___x_53_, v___x_43_);
lean_dec_ref(v___x_41_);
lean_inc_ref_n(v___x_54_, 2);
v___x_55_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
lean_ctor_set(v___x_55_, 2, v___x_54_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object* v___x_56_, lean_object* v_env_57_, lean_object* v_s_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(v___x_56_, v_env_57_, v_s_58_);
lean_dec(v_s_58_);
lean_dec(v___x_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___f_99_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_));
v___x_100_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_));
v___x_101_ = lean_box(0);
v___x_102_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_100_, v___x_101_, v___f_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_();
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(lean_object* v_init_105_, lean_object* v_t_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0_spec__0(v_init_105_, v_t_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_108_, lean_object* v_t_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(v_init_108_, v_t_109_);
lean_dec(v_t_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0(lean_object* v_type_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
lean_inc_ref(v_type_111_);
v___x_117_ = l_Lean_Meta_isProp(v_type_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; uint8_t v___x_119_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
v___x_119_ = lean_unbox(v_a_118_);
lean_dec(v_a_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec_ref_known(v___x_117_, 1);
v___x_120_ = l_Lean_Meta_isTypeFormerType(v_type_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
return v___x_120_;
}
else
{
lean_dec_ref(v_type_111_);
return v___x_117_;
}
}
else
{
lean_dec_ref(v_type_111_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0___boxed(lean_object* v_type_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0(v_type_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(lean_object* v_declName_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___f_133_ = ((lean_object*)(l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0));
v___x_134_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
v___x_135_ = l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(v___x_134_, v___f_133_, v_declName_129_, v_a_130_, v_a_131_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___boxed(lean_object* v_declName_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(v_declName_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object* v_declName_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
v___x_146_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(v___x_145_, v_declName_141_, v_a_142_, v_a_143_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___boxed(lean_object* v_declName_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_declName_147_, v_a_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(lean_object* v_type_152_, lean_object* v_r_153_){
_start:
{
if (lean_obj_tag(v_type_152_) == 7)
{
lean_object* v_binderType_154_; lean_object* v_body_155_; lean_object* v___x_156_; 
v_binderType_154_ = lean_ctor_get(v_type_152_, 1);
lean_inc_ref(v_binderType_154_);
v_body_155_ = lean_ctor_get(v_type_152_, 2);
lean_inc_ref(v_body_155_);
lean_dec_ref_known(v_type_152_, 3);
v___x_156_ = lean_array_push(v_r_153_, v_binderType_154_);
v_type_152_ = v_body_155_;
v_r_153_ = v___x_156_;
goto _start;
}
else
{
lean_dec_ref(v_type_152_);
return v_r_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object* v_type_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParamTypes___closed__0));
v___x_162_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(v_type_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___f_168_; lean_object* v___x_3494__overap_169_; lean_object* v___x_170_; 
v___f_168_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0));
v___x_3494__overap_169_ = lean_panic_fn_borrowed(v___f_168_, v_msg_164_);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
v___x_170_ = lean_apply_3(v___x_3494__overap_169_, v___y_165_, v___y_166_, lean_box(0));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___boxed(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(v_msg_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_175_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType___closed__0(void){
_start:
{
lean_object* v___x_176_; lean_object* v_dummy_177_; 
v___x_176_ = lean_box(0);
v_dummy_177_ = l_Lean_Expr_sort___override(v___x_176_);
return v_dummy_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object* v_type_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_type_183_; 
v_type_183_ = l_Lean_Expr_headBeta(v_type_179_);
switch(lean_obj_tag(v_type_183_))
{
case 4:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParamTypes___closed__0));
v___x_185_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_type_183_, v___x_184_, v_a_180_, v_a_181_);
return v___x_185_;
}
case 5:
{
lean_object* v_dummy_186_; lean_object* v_nargs_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_dummy_186_ = lean_obj_once(&l_Lean_Compiler_LCNF_toMonoType___closed__0, &l_Lean_Compiler_LCNF_toMonoType___closed__0_once, _init_l_Lean_Compiler_LCNF_toMonoType___closed__0);
v_nargs_187_ = l_Lean_Expr_getAppNumArgs(v_type_183_);
lean_inc(v_nargs_187_);
v___x_188_ = lean_mk_array(v_nargs_187_, v_dummy_186_);
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = lean_nat_sub(v_nargs_187_, v___x_189_);
lean_dec(v_nargs_187_);
v___x_191_ = l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(v_type_183_, v___x_188_, v___x_190_, v_a_180_, v_a_181_);
return v___x_191_;
}
case 7:
{
lean_object* v_binderName_192_; lean_object* v_binderType_193_; lean_object* v_body_194_; uint8_t v_binderInfo_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_binderName_192_ = lean_ctor_get(v_type_183_, 0);
lean_inc(v_binderName_192_);
v_binderType_193_ = lean_ctor_get(v_type_183_, 1);
lean_inc_ref(v_binderType_193_);
v_body_194_ = lean_ctor_get(v_type_183_, 2);
lean_inc_ref(v_body_194_);
v_binderInfo_195_ = lean_ctor_get_uint8(v_type_183_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_183_, 3);
v___x_196_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_197_ = lean_expr_instantiate1(v_body_194_, v___x_196_);
lean_dec_ref(v_body_194_);
v___x_198_ = l_Lean_Compiler_LCNF_toMonoType(v___x_197_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_225_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_225_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_225_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_225_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___y_204_; lean_object* v___y_205_; 
if (lean_obj_tag(v_a_199_) == 4)
{
lean_object* v_declName_216_; 
v_declName_216_ = lean_ctor_get(v_a_199_, 0);
if (lean_obj_tag(v_declName_216_) == 1)
{
lean_object* v_pre_217_; 
v_pre_217_ = lean_ctor_get(v_declName_216_, 0);
if (lean_obj_tag(v_pre_217_) == 0)
{
lean_object* v_str_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_str_218_ = lean_ctor_get(v_declName_216_, 1);
v___x_219_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_220_ = lean_string_dec_eq(v_str_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_del_object(v___x_201_);
v___y_204_ = v_a_180_;
v___y_205_ = v_a_181_;
goto v___jp_203_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_223_; 
lean_dec_ref_known(v_a_199_, 2);
lean_dec_ref(v_binderType_193_);
lean_dec(v_binderName_192_);
v___x_221_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_221_);
v___x_223_ = v___x_201_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_del_object(v___x_201_);
v___y_204_ = v_a_180_;
v___y_205_ = v_a_181_;
goto v___jp_203_;
}
}
else
{
lean_del_object(v___x_201_);
v___y_204_ = v_a_180_;
v___y_205_ = v_a_181_;
goto v___jp_203_;
}
}
else
{
lean_del_object(v___x_201_);
v___y_204_ = v_a_180_;
v___y_205_ = v_a_181_;
goto v___jp_203_;
}
v___jp_203_:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_193_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = l_Lean_Expr_forallE___override(v_binderName_192_, v_a_207_, v_a_199_, v_binderInfo_195_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
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
lean_dec(v_a_199_);
lean_dec(v_binderName_192_);
return v___x_206_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_193_);
lean_dec(v_binderName_192_);
return v___x_198_;
}
}
case 3:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec_ref_known(v_type_183_, 1);
v___x_226_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
case 10:
{
lean_object* v_data_228_; lean_object* v_expr_229_; lean_object* v___x_230_; 
v_data_228_ = lean_ctor_get(v_type_183_, 0);
lean_inc(v_data_228_);
v_expr_229_ = lean_ctor_get(v_type_183_, 1);
lean_inc_ref(v_expr_229_);
lean_dec_ref_known(v_type_183_, 2);
v___x_230_ = l_Lean_Compiler_LCNF_toMonoType(v_expr_229_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = l_Lean_Expr_mdata___override(v_data_228_, v_a_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_dec(v_data_228_);
return v___x_230_;
}
}
default: 
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_type_183_);
v___x_240_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2));
v___x_246_ = lean_unsigned_to_nat(50u);
v___x_247_ = lean_unsigned_to_nat(82u);
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1));
v___x_249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0));
v___x_250_ = l_mkPanicMessageWithDecl(v___x_249_, v___x_248_, v___x_247_, v___x_246_, v___x_245_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(uint8_t v___x_251_, lean_object* v_as_252_, size_t v_sz_253_, size_t v_i_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_a_260_; uint8_t v___x_264_; 
v___x_264_ = lean_usize_dec_lt(v_i_254_, v_sz_253_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v_b_255_);
return v___x_265_;
}
else
{
lean_object* v_fst_266_; lean_object* v_snd_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_316_; 
v_fst_266_ = lean_ctor_get(v_b_255_, 0);
v_snd_267_ = lean_ctor_get(v_b_255_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_b_255_);
if (v_isSharedCheck_316_ == 0)
{
v___x_269_ = v_b_255_;
v_isShared_270_ = v_isSharedCheck_316_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_snd_267_);
lean_inc(v_fst_266_);
lean_dec(v_b_255_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_316_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; 
lean_inc(v_snd_267_);
v___x_271_ = l_Lean_Expr_headBeta(v_snd_267_);
if (lean_obj_tag(v___x_271_) == 7)
{
lean_object* v_binderType_272_; lean_object* v_body_273_; lean_object* v_a_274_; lean_object* v___x_275_; lean_object* v_result_277_; uint8_t v___y_295_; 
lean_dec(v_snd_267_);
v_binderType_272_ = lean_ctor_get(v___x_271_, 1);
lean_inc_ref(v_binderType_272_);
v_body_273_ = lean_ctor_get(v___x_271_, 2);
lean_inc_ref(v_body_273_);
lean_dec_ref_known(v___x_271_, 3);
v_a_274_ = lean_array_uget_borrowed(v_as_252_, v_i_254_);
lean_inc(v_a_274_);
v___x_275_ = l_Lean_Expr_headBeta(v_a_274_);
switch(lean_obj_tag(v_binderType_272_))
{
case 4:
{
lean_object* v_declName_298_; 
v_declName_298_ = lean_ctor_get(v_binderType_272_, 0);
lean_inc(v_declName_298_);
lean_dec_ref_known(v_binderType_272_, 2);
if (lean_obj_tag(v_declName_298_) == 1)
{
lean_object* v_pre_299_; 
v_pre_299_ = lean_ctor_get(v_declName_298_, 0);
if (lean_obj_tag(v_pre_299_) == 0)
{
lean_object* v_str_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_str_300_ = lean_ctor_get(v_declName_298_, 1);
lean_inc_ref(v_str_300_);
lean_dec_ref_known(v_declName_298_, 2);
v___x_301_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_302_ = lean_string_dec_eq(v_str_300_, v___x_301_);
lean_dec_ref(v_str_300_);
if (v___x_302_ == 0)
{
v___y_295_ = v___x_251_;
goto v___jp_294_;
}
else
{
goto v___jp_282_;
}
}
else
{
lean_dec_ref_known(v_declName_298_, 2);
v___y_295_ = v___x_251_;
goto v___jp_294_;
}
}
else
{
lean_dec(v_declName_298_);
v___y_295_ = v___x_251_;
goto v___jp_294_;
}
}
case 3:
{
lean_dec_ref_known(v_binderType_272_, 1);
goto v___jp_282_;
}
default: 
{
lean_dec_ref(v_binderType_272_);
v___y_295_ = v___x_251_;
goto v___jp_294_;
}
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_expr_instantiate1(v_body_273_, v___x_275_);
lean_dec_ref(v___x_275_);
lean_dec_ref(v_body_273_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_278_);
lean_ctor_set(v___x_269_, 0, v_result_277_);
v___x_280_ = v___x_269_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_result_277_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
v_a_260_ = v___x_280_;
goto v___jp_259_;
}
}
v___jp_282_:
{
lean_object* v___x_283_; 
lean_inc_ref(v___x_275_);
v___x_283_ = l_Lean_Compiler_LCNF_toMonoType(v___x_275_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
v___x_285_ = l_Lean_Expr_app___override(v_fst_266_, v_a_284_);
v_result_277_ = v___x_285_;
goto v___jp_276_;
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v___x_275_);
lean_dec_ref(v_body_273_);
lean_del_object(v___x_269_);
lean_dec(v_fst_266_);
v_a_286_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_283_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_283_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
v___jp_294_:
{
if (v___y_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_297_ = l_Lean_Expr_app___override(v_fst_266_, v___x_296_);
v_result_277_ = v___x_297_;
goto v___jp_276_;
}
else
{
goto v___jp_282_;
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref(v___x_271_);
v___x_303_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3);
v___x_304_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(v___x_303_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_306_; 
lean_dec_ref_known(v___x_304_, 1);
if (v_isShared_270_ == 0)
{
v___x_306_ = v___x_269_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_fst_266_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_snd_267_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
v_a_260_ = v___x_306_;
goto v___jp_259_;
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_del_object(v___x_269_);
lean_dec(v_snd_267_);
lean_dec(v_fst_266_);
v_a_308_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_304_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_304_);
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
}
v___jp_259_:
{
size_t v___x_261_; size_t v___x_262_; 
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_add(v_i_254_, v___x_261_);
v_i_254_ = v___x_262_;
v_b_255_ = v_a_260_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_box(0);
v___x_323_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__3));
v___x_324_ = l_Lean_mkConst(v___x_323_, v___x_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(lean_object* v_f_325_, lean_object* v_args_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
if (lean_obj_tag(v_f_325_) == 4)
{
lean_object* v_declName_330_; lean_object* v_us_331_; lean_object* v___x_332_; lean_object* v___y_334_; lean_object* v___y_335_; 
v_declName_330_ = lean_ctor_get(v_f_325_, 0);
lean_inc(v_declName_330_);
v_us_331_ = lean_ctor_get(v_f_325_, 1);
lean_inc(v_us_331_);
lean_dec_ref_known(v_f_325_, 2);
v___x_332_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_declName_330_) == 1)
{
lean_object* v_pre_395_; 
v_pre_395_ = lean_ctor_get(v_declName_330_, 0);
if (lean_obj_tag(v_pre_395_) == 0)
{
lean_object* v_str_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_str_396_ = lean_ctor_get(v_declName_330_, 1);
v___x_397_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_398_ = lean_string_dec_eq(v_str_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0));
v___x_400_ = lean_string_dec_eq(v_str_396_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__1));
v___x_402_ = lean_string_dec_eq(v_str_396_, v___x_401_);
if (v___x_402_ == 0)
{
v___y_334_ = v_a_327_;
v___y_335_ = v_a_328_;
goto v___jp_333_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref_known(v_declName_330_, 2);
lean_dec(v_us_331_);
lean_dec_ref(v_args_326_);
v___x_403_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4, &l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4_once, _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref_known(v_declName_330_, 2);
lean_dec(v_us_331_);
lean_dec_ref(v_args_326_);
v___x_405_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref_known(v_declName_330_, 2);
lean_dec(v_us_331_);
lean_dec_ref(v_args_326_);
v___x_407_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
else
{
v___y_334_ = v_a_327_;
v___y_335_ = v_a_328_;
goto v___jp_333_;
}
}
else
{
v___y_334_ = v_a_327_;
v___y_335_ = v_a_328_;
goto v___jp_333_;
}
v___jp_333_:
{
lean_object* v___x_336_; 
lean_inc(v_declName_330_);
v___x_336_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_declName_330_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
if (lean_obj_tag(v_a_337_) == 1)
{
lean_object* v_val_338_; lean_object* v_ctorName_339_; lean_object* v_numParams_340_; lean_object* v_fieldIdx_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_us_331_);
lean_dec(v_declName_330_);
v_val_338_ = lean_ctor_get(v_a_337_, 0);
lean_inc(v_val_338_);
lean_dec_ref_known(v_a_337_, 1);
v_ctorName_339_ = lean_ctor_get(v_val_338_, 0);
lean_inc(v_ctorName_339_);
v_numParams_340_ = lean_ctor_get(v_val_338_, 1);
lean_inc(v_numParams_340_);
v_fieldIdx_341_ = lean_ctor_get(v_val_338_, 2);
lean_inc(v_fieldIdx_341_);
lean_dec(v_val_338_);
v___x_342_ = lean_box(0);
v___x_343_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_ctorName_339_, v___x_342_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = l_Array_toSubarray___redArg(v_args_326_, v___x_345_, v_numParams_340_);
v___x_347_ = l_Subarray_copy___redArg(v___x_346_);
v___x_348_ = l_Lean_Compiler_LCNF_instantiateForall(v_a_344_, v___x_347_, v___y_334_, v___y_335_);
lean_dec_ref(v___x_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_349_);
v___x_351_ = lean_array_get(v___x_332_, v___x_350_, v_fieldIdx_341_);
lean_dec(v_fieldIdx_341_);
lean_dec_ref(v___x_350_);
v___x_352_ = l_Lean_Compiler_LCNF_toMonoType(v___x_351_, v___y_334_, v___y_335_);
return v___x_352_;
}
else
{
lean_dec(v_fieldIdx_341_);
return v___x_348_;
}
}
else
{
lean_dec(v_fieldIdx_341_);
lean_dec(v_numParams_340_);
lean_dec_ref(v_args_326_);
return v___x_343_;
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_a_337_);
v___x_353_ = lean_box(0);
lean_inc(v_declName_330_);
v___x_354_ = l_Lean_mkConst(v_declName_330_, v___x_353_);
v___x_355_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_330_, v_us_331_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_386_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_386_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_386_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_386_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v___x_360_; 
v___x_360_ = l_Lean_Expr_isErased(v_a_356_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; size_t v_sz_362_; size_t v___x_363_; lean_object* v___x_364_; 
lean_del_object(v___x_358_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_354_);
lean_ctor_set(v___x_361_, 1, v_a_356_);
v_sz_362_ = lean_array_size(v_args_326_);
v___x_363_ = ((size_t)0ULL);
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(v___x_360_, v_args_326_, v_sz_362_, v___x_363_, v___x_361_, v___y_334_, v___y_335_);
lean_dec_ref(v_args_326_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_fst_369_; lean_object* v___x_371_; 
v_fst_369_ = lean_ctor_get(v_a_365_, 0);
lean_inc(v_fst_369_);
lean_dec(v_a_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v_fst_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_fst_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_364_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_364_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_dec(v_a_356_);
lean_dec_ref(v___x_354_);
lean_dec_ref(v_args_326_);
v___x_382_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_382_);
v___x_384_ = v___x_358_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
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
lean_dec_ref(v___x_354_);
lean_dec_ref(v_args_326_);
return v___x_355_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_us_331_);
lean_dec(v_declName_330_);
lean_dec_ref(v_args_326_);
v_a_387_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_336_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_336_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref(v_args_326_);
lean_dec_ref(v_f_325_);
v___x_409_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
if (lean_obj_tag(v_x_411_) == 5)
{
lean_object* v_fn_417_; lean_object* v_arg_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_fn_417_ = lean_ctor_get(v_x_411_, 0);
lean_inc_ref(v_fn_417_);
v_arg_418_ = lean_ctor_get(v_x_411_, 1);
lean_inc_ref(v_arg_418_);
lean_dec_ref_known(v_x_411_, 2);
v___x_419_ = lean_array_set(v_x_412_, v_x_413_, v_arg_418_);
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_sub(v_x_413_, v___x_420_);
lean_dec(v_x_413_);
v_x_411_ = v_fn_417_;
v_x_412_ = v___x_419_;
v_x_413_ = v___x_421_;
goto _start;
}
else
{
lean_object* v___x_423_; 
lean_dec(v_x_413_);
v___x_423_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_x_411_, v_x_412_, v___y_414_, v___y_415_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3___boxed(lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(v_x_424_, v_x_425_, v_x_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___boxed(lean_object* v_type_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Compiler_LCNF_toMonoType(v_type_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(lean_object* v___x_436_, lean_object* v_as_437_, lean_object* v_sz_438_, lean_object* v_i_439_, lean_object* v_b_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_3962__boxed_444_; size_t v_sz_boxed_445_; size_t v_i_boxed_446_; lean_object* v_res_447_; 
v___x_3962__boxed_444_ = lean_unbox(v___x_436_);
v_sz_boxed_445_ = lean_unbox_usize(v_sz_438_);
lean_dec(v_sz_438_);
v_i_boxed_446_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(v___x_3962__boxed_444_, v_as_437_, v_sz_boxed_445_, v_i_boxed_446_, v_b_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec_ref(v_as_437_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___boxed(lean_object* v_f_448_, lean_object* v_args_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_f_448_, v_args_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(lean_object* v_env_454_, lean_object* v_as_455_, size_t v_i_456_, size_t v_stop_457_, lean_object* v_b_458_){
_start:
{
lean_object* v___y_460_; uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_eq(v_i_456_, v_stop_457_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v_fst_466_; uint8_t v___x_467_; 
v___x_465_ = lean_array_uget_borrowed(v_as_455_, v_i_456_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_fst_466_);
lean_inc_ref(v_env_454_);
v___x_467_ = l_Lean_Environment_contains(v_env_454_, v_fst_466_, v___x_464_);
if (v___x_467_ == 0)
{
v___y_460_ = v_b_458_;
goto v___jp_459_;
}
else
{
lean_object* v___x_468_; 
lean_inc(v___x_465_);
v___x_468_ = lean_array_push(v_b_458_, v___x_465_);
v___y_460_ = v___x_468_;
goto v___jp_459_;
}
}
else
{
lean_dec_ref(v_env_454_);
return v_b_458_;
}
v___jp_459_:
{
size_t v___x_461_; size_t v___x_462_; 
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_add(v_i_456_, v___x_461_);
v_i_456_ = v___x_462_;
v_b_458_ = v___y_460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_469_, lean_object* v_as_470_, lean_object* v_i_471_, lean_object* v_stop_472_, lean_object* v_b_473_){
_start:
{
size_t v_i_boxed_474_; size_t v_stop_boxed_475_; lean_object* v_res_476_; 
v_i_boxed_474_ = lean_unbox_usize(v_i_471_);
lean_dec(v_i_471_);
v_stop_boxed_475_ = lean_unbox_usize(v_stop_472_);
lean_dec(v_stop_472_);
v_res_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(v_env_469_, v_as_470_, v_i_boxed_474_, v_stop_boxed_475_, v_b_473_);
lean_dec_ref(v_as_470_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_object* v_k_479_; lean_object* v_v_480_; lean_object* v_l_481_; lean_object* v_r_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_k_479_ = lean_ctor_get(v_x_478_, 1);
v_v_480_ = lean_ctor_get(v_x_478_, 2);
v_l_481_ = lean_ctor_get(v_x_478_, 3);
v_r_482_ = lean_ctor_get(v_x_478_, 4);
v___x_483_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_477_, v_l_481_);
lean_inc(v_v_480_);
lean_inc(v_k_479_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_k_479_);
lean_ctor_set(v___x_484_, 1, v_v_480_);
v___x_485_ = lean_array_push(v___x_483_, v___x_484_);
v_init_477_ = v___x_485_;
v_x_478_ = v_r_482_;
goto _start;
}
else
{
return v_init_477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_487_, lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_487_, v_x_488_);
lean_dec(v_x_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(lean_object* v_env_496_, lean_object* v_s_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_500_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v___x_499_, v_s_497_);
v___x_501_ = lean_array_get_size(v___x_500_);
v___x_502_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_503_ = lean_nat_dec_lt(v___x_498_, v___x_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec_ref(v___x_500_);
lean_dec_ref(v_env_496_);
v___x_504_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
return v___x_504_;
}
else
{
uint8_t v___x_505_; 
v___x_505_ = lean_nat_dec_le(v___x_501_, v___x_501_);
if (v___x_505_ == 0)
{
if (v___x_503_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v___x_500_);
lean_dec_ref(v_env_496_);
v___x_506_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
return v___x_506_;
}
else
{
size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = ((size_t)0ULL);
v___x_508_ = lean_usize_of_nat(v___x_501_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(v_env_496_, v___x_500_, v___x_507_, v___x_508_, v___x_502_);
lean_dec_ref(v___x_500_);
lean_inc_ref_n(v___x_509_, 2);
v___x_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
lean_ctor_set(v___x_510_, 2, v___x_509_);
return v___x_510_;
}
}
else
{
size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_511_ = ((size_t)0ULL);
v___x_512_ = lean_usize_of_nat(v___x_501_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(v_env_496_, v___x_500_, v___x_511_, v___x_512_, v___x_502_);
lean_dec_ref(v___x_500_);
lean_inc_ref_n(v___x_513_, 2);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object* v_env_515_, lean_object* v_s_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(v_env_515_, v_s_516_);
lean_dec(v_s_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___f_526_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_527_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_528_ = lean_box(0);
v___x_529_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_527_, v___x_528_, v___f_526_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_();
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0(lean_object* v_init_532_, lean_object* v_t_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_532_, v_t_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_535_, lean_object* v_t_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0(v_init_535_, v_t_536_);
lean_dec(v_t_536_);
return v_res_537_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0(void){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType(lean_object* v_declName_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_547_; lean_object* v_env_548_; lean_object* v___x_549_; lean_object* v_toEnvExtension_550_; lean_object* v_asyncMode_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; 
v___x_547_ = lean_st_ref_get(v_a_545_);
v_env_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_547_);
v___x_549_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_550_ = lean_ctor_get(v___x_549_, 0);
v_asyncMode_551_ = lean_ctor_get(v_toEnvExtension_550_, 2);
v___x_552_ = l_Lean_instInhabitedExpr;
v___x_553_ = 0;
lean_inc(v_declName_543_);
v___x_554_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_552_, v___x_549_, v_env_548_, v_declName_543_, v_asyncMode_551_, v___x_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
lean_inc(v_declName_543_);
v___x_556_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_543_, v___x_555_, v_a_544_, v_a_545_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = l_Lean_Compiler_LCNF_toMonoType(v_a_557_, v_a_544_, v_a_545_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_587_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_587_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_587_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_587_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v_env_564_; lean_object* v_nextMacroScope_565_; lean_object* v_ngen_566_; lean_object* v_auxDeclNGen_567_; lean_object* v_traceState_568_; lean_object* v_messages_569_; lean_object* v_infoState_570_; lean_object* v_snapshotTasks_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_585_; 
v___x_563_ = lean_st_ref_take(v_a_545_);
v_env_564_ = lean_ctor_get(v___x_563_, 0);
v_nextMacroScope_565_ = lean_ctor_get(v___x_563_, 1);
v_ngen_566_ = lean_ctor_get(v___x_563_, 2);
v_auxDeclNGen_567_ = lean_ctor_get(v___x_563_, 3);
v_traceState_568_ = lean_ctor_get(v___x_563_, 4);
v_messages_569_ = lean_ctor_get(v___x_563_, 6);
v_infoState_570_ = lean_ctor_get(v___x_563_, 7);
v_snapshotTasks_571_ = lean_ctor_get(v___x_563_, 8);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; 
v_unused_586_ = lean_ctor_get(v___x_563_, 5);
lean_dec(v_unused_586_);
v___x_573_ = v___x_563_;
v_isShared_574_ = v_isSharedCheck_585_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snapshotTasks_571_);
lean_inc(v_infoState_570_);
lean_inc(v_messages_569_);
lean_inc(v_traceState_568_);
lean_inc(v_auxDeclNGen_567_);
lean_inc(v_ngen_566_);
lean_inc(v_nextMacroScope_565_);
lean_inc(v_env_564_);
lean_dec(v___x_563_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_585_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_575_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_549_, v_env_564_, v_declName_543_, v_a_559_);
v___x_576_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 5, v___x_576_);
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_578_ = v___x_573_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_nextMacroScope_565_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_ngen_566_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_auxDeclNGen_567_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_traceState_568_);
lean_ctor_set(v_reuseFailAlloc_584_, 5, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_584_, 6, v_messages_569_);
lean_ctor_set(v_reuseFailAlloc_584_, 7, v_infoState_570_);
lean_ctor_set(v_reuseFailAlloc_584_, 8, v_snapshotTasks_571_);
v___x_578_ = v_reuseFailAlloc_584_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = lean_st_ref_set(v_a_545_, v___x_578_);
v___x_580_ = lean_box(0);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_580_);
v___x_582_ = v___x_561_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_declName_543_);
v_a_588_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_558_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_558_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_declName_543_);
v_a_596_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_556_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_556_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_declName_543_);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___x_554_, 0);
lean_dec(v_unused_612_);
v___x_605_ = v___x_554_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_dec(v___x_554_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = lean_box(0);
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 0);
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___boxed(lean_object* v_declName_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_declName_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___lam__0(lean_object* v___x_618_, lean_object* v_declName_619_, lean_object* v_a_620_, lean_object* v_x_621_){
_start:
{
lean_object* v_addEntryFn_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_addEntryFn_622_ = lean_ctor_get(v___x_618_, 3);
lean_inc(v_addEntryFn_622_);
lean_dec_ref(v___x_618_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_declName_619_);
lean_ctor_set(v___x_623_, 1, v_a_620_);
v___x_624_ = lean_apply_2(v_addEntryFn_622_, v_x_621_, v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_625_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_ctor_set(v___x_630_, 3, v___x_629_);
lean_ctor_set(v___x_630_, 4, v___x_628_);
lean_ctor_set(v___x_630_, 5, v___x_628_);
lean_ctor_set(v___x_630_, 6, v___x_628_);
lean_ctor_set(v___x_630_, 7, v___x_628_);
lean_ctor_set(v___x_630_, 8, v___x_628_);
lean_ctor_set(v___x_630_, 9, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_unsigned_to_nat(32u);
v___x_632_ = lean_mk_empty_array_with_capacity(v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_634_ = ((size_t)5ULL);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_unsigned_to_nat(32u);
v___x_637_ = lean_mk_empty_array_with_capacity(v___x_636_);
v___x_638_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3);
v___x_639_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_635_);
lean_ctor_set(v___x_639_, 3, v___x_635_);
lean_ctor_set_usize(v___x_639_, 4, v___x_634_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_box(1);
v___x_641_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4);
v___x_642_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1);
v___x_643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
lean_ctor_set(v___x_643_, 2, v___x_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(lean_object* v_msgData_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v_env_649_; lean_object* v_options_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_648_ = lean_st_ref_get(v___y_646_);
v_env_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_648_);
v_options_650_ = lean_ctor_get(v___y_645_, 2);
v___x_651_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2);
v___x_652_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_650_);
v___x_653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_653_, 0, v_env_649_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_652_);
lean_ctor_set(v___x_653_, 3, v_options_650_);
v___x_654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_msgData_644_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___boxed(lean_object* v_msgData_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(v_msgData_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_ref_665_; lean_object* v___x_666_; lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_ref_665_ = lean_ctor_get(v___y_662_, 5);
v___x_666_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(v_msg_661_, v___y_662_, v___y_663_);
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_inc(v_ref_665_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_ref_665_);
lean_ctor_set(v___x_671_, 1, v_a_667_);
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 1);
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___boxed(lean_object* v_msg_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v_msg_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object* v_declName_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___x_731_; lean_object* v_env_732_; lean_object* v___x_733_; lean_object* v_toEnvExtension_734_; lean_object* v_asyncMode_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; 
v___x_731_ = lean_st_ref_get(v_a_689_);
v_env_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_env_732_);
lean_dec(v___x_731_);
v___x_733_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_734_ = lean_ctor_get(v___x_733_, 0);
v_asyncMode_735_ = lean_ctor_get(v_toEnvExtension_734_, 2);
v___x_736_ = l_Lean_instInhabitedExpr;
v___x_737_ = 0;
lean_inc(v_declName_687_);
v___x_738_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_736_, v___x_733_, v_env_732_, v_declName_687_, v_asyncMode_735_, v___x_737_);
if (lean_obj_tag(v___x_738_) == 1)
{
lean_object* v_val_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_declName_687_);
v_val_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_val_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set_tag(v___x_741_, 0);
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_val_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v___x_747_; lean_object* v_env_763_; uint8_t v___x_764_; lean_object* v___x_765_; 
lean_dec(v___x_738_);
v___x_747_ = lean_st_ref_get(v_a_689_);
v_env_763_ = lean_ctor_get(v___x_747_, 0);
lean_inc_ref(v_env_763_);
lean_dec(v___x_747_);
v___x_764_ = 0;
lean_inc(v_declName_687_);
v___x_765_ = l_Lean_Environment_find_x3f(v_env_763_, v_declName_687_, v___x_764_);
if (lean_obj_tag(v___x_765_) == 1)
{
lean_object* v_val_766_; 
v_val_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v___x_765_, 1);
switch(lean_obj_tag(v_val_766_))
{
case 5:
{
lean_dec_ref_known(v_val_766_, 1);
goto v___jp_748_;
}
case 6:
{
lean_dec_ref_known(v_val_766_, 1);
goto v___jp_748_;
}
default: 
{
lean_dec(v_val_766_);
v___y_692_ = v_a_688_;
v___y_693_ = v_a_689_;
goto v___jp_691_;
}
}
}
else
{
lean_dec(v___x_765_);
v___y_692_ = v_a_688_;
v___y_693_ = v_a_689_;
goto v___jp_691_;
}
v___jp_748_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v___x_749_ = lean_obj_once(&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1, &l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1_once, _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1);
v___x_750_ = l_Lean_MessageData_ofName(v_declName_687_);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_obj_once(&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3, &l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3_once, _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v___x_753_, v_a_688_, v_a_689_);
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
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
v___jp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_box(0);
lean_inc(v_declName_687_);
v___x_695_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_687_, v___x_694_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = l_Lean_Compiler_LCNF_toMonoType(v_a_696_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_730_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_730_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_730_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_730_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v_env_703_; lean_object* v_nextMacroScope_704_; lean_object* v_ngen_705_; lean_object* v_auxDeclNGen_706_; lean_object* v_traceState_707_; lean_object* v_messages_708_; lean_object* v_infoState_709_; lean_object* v_snapshotTasks_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_728_; 
v___x_702_ = lean_st_ref_take(v___y_693_);
v_env_703_ = lean_ctor_get(v___x_702_, 0);
v_nextMacroScope_704_ = lean_ctor_get(v___x_702_, 1);
v_ngen_705_ = lean_ctor_get(v___x_702_, 2);
v_auxDeclNGen_706_ = lean_ctor_get(v___x_702_, 3);
v_traceState_707_ = lean_ctor_get(v___x_702_, 4);
v_messages_708_ = lean_ctor_get(v___x_702_, 6);
v_infoState_709_ = lean_ctor_get(v___x_702_, 7);
v_snapshotTasks_710_ = lean_ctor_get(v___x_702_, 8);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_702_, 5);
lean_dec(v_unused_729_);
v___x_712_ = v___x_702_;
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snapshotTasks_710_);
lean_inc(v_infoState_709_);
lean_inc(v_messages_708_);
lean_inc(v_traceState_707_);
lean_inc(v_auxDeclNGen_706_);
lean_inc(v_ngen_705_);
lean_inc(v_nextMacroScope_704_);
lean_inc(v_env_703_);
lean_dec(v___x_702_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v_toEnvExtension_715_; lean_object* v_asyncMode_716_; lean_object* v___f_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_714_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_715_ = lean_ctor_get(v___x_714_, 0);
v_asyncMode_716_ = lean_ctor_get(v_toEnvExtension_715_, 2);
lean_inc(v_a_698_);
v___f_717_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___lam__0), 4, 3);
lean_closure_set(v___f_717_, 0, v___x_714_);
lean_closure_set(v___f_717_, 1, v_declName_687_);
lean_closure_set(v___f_717_, 2, v_a_698_);
v___x_718_ = lean_box(0);
v___x_719_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_714_, v_env_703_, v___f_717_, v_asyncMode_716_, v___x_718_);
v___x_720_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 5, v___x_720_);
lean_ctor_set(v___x_712_, 0, v___x_719_);
v___x_722_ = v___x_712_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_nextMacroScope_704_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_ngen_705_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_auxDeclNGen_706_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_traceState_707_);
lean_ctor_set(v_reuseFailAlloc_727_, 5, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_727_, 6, v_messages_708_);
lean_ctor_set(v_reuseFailAlloc_727_, 7, v_infoState_709_);
lean_ctor_set(v_reuseFailAlloc_727_, 8, v_snapshotTasks_710_);
v___x_722_ = v_reuseFailAlloc_727_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_st_ref_set(v___y_693_, v___x_722_);
if (v_isShared_701_ == 0)
{
v___x_725_ = v___x_700_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_698_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
else
{
lean_dec(v_declName_687_);
return v___x_697_;
}
}
else
{
lean_dec(v_declName_687_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___boxed(lean_object* v_declName_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(v_declName_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(lean_object* v_00_u03b1_772_, lean_object* v_msg_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v_msg_773_, v___y_774_, v___y_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___boxed(lean_object* v_00_u03b1_778_, lean_object* v_msg_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(v_00_u03b1_778_, v_msg_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_783_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Irrelevant(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoTypeExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Irrelevant(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
}
#ifdef __cplusplus
}
#endif
