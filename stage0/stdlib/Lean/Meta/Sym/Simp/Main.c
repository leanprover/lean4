// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Main
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.Simp.Simproc import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.Simp.Have import Lean.Meta.Sym.Simp.Forall
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
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(242, 186, 16, 3, 3, 47, 215, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 69, 64, 134, 227, 122, 63, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 138, 18, 6, 80, 119, 92, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__8_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__8_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__8_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__10_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__8_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__10_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__10_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__12_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__10_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 84, 158, 71, 120, 158, 242, 63)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__12_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__12_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__14_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__12_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 26, 240, 230, 40, 246, 104, 165)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__14_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__14_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__16_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__14_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 173, 159, 84, 157, 242, 206, 139)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__16_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__16_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__17_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__16_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(247, 155, 15, 76, 144, 59, 13, 75)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__17_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__17_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__18_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__17_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 236, 234, 229, 132, 157, 220, 243)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__18_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__18_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__19_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__18_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 51, 220, 1, 188, 119, 51, 193)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__19_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__19_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__20_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__19_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 225, 33, 185, 152, 235, 128, 22)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__20_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__20_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__21_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__20_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 205, 190, 94, 250, 112, 139, 24)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__21_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__21_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__22_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__22_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__22_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__23_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__21_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__22_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 198, 249, 116, 103, 109, 185, 157)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__23_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__23_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__24_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__24_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__24_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__25_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__23_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__24_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 117, 150, 162, 230, 34, 31, 227)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__25_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__25_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__26_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__25_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(170, 54, 57, 188, 150, 202, 153, 240)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__26_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__26_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__27_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__26_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 14, 232, 240, 135, 217, 106, 147)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__27_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__27_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__28_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__27_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 131, 247, 225, 188, 12, 226, 127)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__28_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__28_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__29_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__28_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 52, 134, 176, 51, 166, 19, 13)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__29_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__29_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__30_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__29_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 24, 143, 103, 249, 178, 142, 101)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__30_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__30_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__32_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__32_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__32_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__34_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__34_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__34_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "unexpected kernel projection term during simplification"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "\npre-process and fold them as projection applications"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "persistent cache hit: "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "transient cache hit: "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "`simp` failed: maximum number of steps exceeded"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8;
LEAN_EXPORT lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_unsigned_to_nat(2936340881u);
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__30_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_74_ = l_Lean_Name_num___override(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__32_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_77_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_);
v___x_78_ = l_Lean_Name_str___override(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__34_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_81_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_);
v___x_82_ = l_Lean_Name_str___override(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_unsigned_to_nat(2u);
v___x_84_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_);
v___x_85_ = l_Lean_Name_num___override(v___x_84_, v___x_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_88_ = 0;
v___x_89_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_);
v___x_90_ = l_Lean_registerTraceClass(v___x_87_, v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2____boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object* v_d_93_, lean_object* v_e_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___y_103_; lean_object* v___x_106_; uint8_t v_debug_107_; 
v___x_106_ = lean_st_ref_get(v___y_96_);
v_debug_107_ = lean_ctor_get_uint8(v___x_106_, sizeof(void*)*11);
lean_dec(v___x_106_);
if (v_debug_107_ == 0)
{
v___y_103_ = v___y_96_;
goto v___jp_102_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_dec_ref_known(v___x_108_, 1);
v___y_103_ = v___y_96_;
goto v___jp_102_;
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec_ref(v_e_94_);
lean_dec(v_d_93_);
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = l_Lean_Expr_mdata___override(v_d_93_, v_e_94_);
v___x_105_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_104_, v___y_103_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object* v_d_117_, lean_object* v_e_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_117_, v_e_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object* v_d_127_, lean_object* v_e_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_127_, v_e_128_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object* v_d_140_, lean_object* v_e_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(v_d_140_, v_e_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object* v_msgData_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; lean_object* v_env_160_; lean_object* v___x_161_; lean_object* v_toCold_162_; lean_object* v_mctx_163_; lean_object* v_lctx_164_; lean_object* v_options_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_159_ = lean_st_ref_get(v___y_157_);
v_env_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc_ref(v_env_160_);
lean_dec(v___x_159_);
v___x_161_ = lean_st_ref_get(v___y_155_);
v_toCold_162_ = lean_ctor_get(v___y_156_, 0);
v_mctx_163_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_mctx_163_);
lean_dec(v___x_161_);
v_lctx_164_ = lean_ctor_get(v___y_154_, 2);
v_options_165_ = lean_ctor_get(v_toCold_162_, 2);
lean_inc_ref(v_options_165_);
lean_inc_ref(v_lctx_164_);
v___x_166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_166_, 0, v_env_160_);
lean_ctor_set(v___x_166_, 1, v_mctx_163_);
lean_ctor_set(v___x_166_, 2, v_lctx_164_);
lean_ctor_set(v___x_166_, 3, v_options_165_);
v___x_167_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_msgData_153_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object* v_msgData_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msgData_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_192_; 
v_ref_182_ = lean_ctor_get(v___y_179_, 2);
v___x_183_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_192_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_inc(v_ref_182_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_ref_182_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object* v_e_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
switch(lean_obj_tag(v_e_208_))
{
case 5:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_219_;
}
case 6:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_220_;
}
case 7:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_221_;
}
case 8:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_222_;
}
case 10:
{
lean_object* v_data_223_; lean_object* v_expr_224_; lean_object* v___x_225_; 
v_data_223_ = lean_ctor_get(v_e_208_, 0);
lean_inc(v_data_223_);
v_expr_224_ = lean_ctor_get(v_e_208_, 1);
lean_inc_ref(v_expr_224_);
lean_dec_ref_known(v_e_208_, 2);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
lean_inc(v_a_211_);
lean_inc_ref(v_a_210_);
lean_inc(v_a_209_);
v___x_225_ = lean_sym_simp(v_expr_224_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_263_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_263_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_263_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_263_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
if (lean_obj_tag(v_a_226_) == 0)
{
uint8_t v_contextDependent_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_data_223_);
v_contextDependent_230_ = lean_ctor_get_uint8(v_a_226_, 1);
lean_dec_ref_known(v_a_226_, 0);
v___x_231_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_230_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_231_);
v___x_233_ = v___x_228_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v_e_x27_235_; lean_object* v_proof_236_; uint8_t v_contextDependent_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_262_; 
lean_del_object(v___x_228_);
v_e_x27_235_ = lean_ctor_get(v_a_226_, 0);
v_proof_236_ = lean_ctor_get(v_a_226_, 1);
v_contextDependent_237_ = lean_ctor_get_uint8(v_a_226_, sizeof(void*)*2 + 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_a_226_);
if (v_isSharedCheck_262_ == 0)
{
v___x_239_ = v_a_226_;
v_isShared_240_ = v_isSharedCheck_262_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_proof_236_);
lean_inc(v_e_x27_235_);
lean_dec(v_a_226_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_262_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_data_223_, v_e_x27_235_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_253_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_253_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_253_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_253_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
uint8_t v___x_246_; lean_object* v___x_248_; 
v___x_246_ = 0;
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v_a_242_);
v___x_248_ = v___x_239_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_242_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_proof_236_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*2 + 1, v_contextDependent_237_);
v___x_248_ = v_reuseFailAlloc_252_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*2, v___x_246_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_248_);
v___x_250_ = v___x_244_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_del_object(v___x_239_);
lean_dec_ref(v_proof_236_);
v_a_254_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_241_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_241_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
}
else
{
lean_dec(v_data_223_);
return v___x_225_;
}
}
case 11:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_264_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1);
v___x_265_ = l_Lean_indentExpr(v_e_208_);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_268_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_269_;
}
default: 
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref(v_e_208_);
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4));
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object* v_e_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object* v_00_u03b1_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_285_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object* v_00_u03b1_297_, lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(v_00_u03b1_297_, v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object* v_e_312_, lean_object* v_r_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___f_316_; lean_object* v___f_317_; uint8_t v___y_319_; 
v___f_316_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_317_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
if (lean_obj_tag(v_r_313_) == 0)
{
uint8_t v_contextDependent_350_; 
v_contextDependent_350_ = lean_ctor_get_uint8(v_r_313_, 1);
v___y_319_ = v_contextDependent_350_;
goto v___jp_318_;
}
else
{
uint8_t v_contextDependent_351_; 
v_contextDependent_351_ = lean_ctor_get_uint8(v_r_313_, sizeof(void*)*2 + 1);
v___y_319_ = v_contextDependent_351_;
goto v___jp_318_;
}
v___jp_318_:
{
if (v___y_319_ == 0)
{
lean_object* v___x_320_; lean_object* v_numSteps_321_; lean_object* v_persistentCache_322_; lean_object* v_transientCache_323_; lean_object* v_funext_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_334_; 
v___x_320_ = lean_st_ref_take(v_a_314_);
v_numSteps_321_ = lean_ctor_get(v___x_320_, 0);
v_persistentCache_322_ = lean_ctor_get(v___x_320_, 1);
v_transientCache_323_ = lean_ctor_get(v___x_320_, 2);
v_funext_324_ = lean_ctor_get(v___x_320_, 3);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_334_ == 0)
{
v___x_326_ = v___x_320_;
v_isShared_327_ = v_isSharedCheck_334_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_funext_324_);
lean_inc(v_transientCache_323_);
lean_inc(v_persistentCache_322_);
lean_inc(v_numSteps_321_);
lean_dec(v___x_320_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_334_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
lean_inc_ref(v_r_313_);
v___x_328_ = l_Lean_PersistentHashMap_insert___redArg(v___f_316_, v___f_317_, v_persistentCache_322_, v_e_312_, v_r_313_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_numSteps_321_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_transientCache_323_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_funext_324_);
v___x_330_ = v_reuseFailAlloc_333_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_st_ref_put(v_a_314_, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_r_313_);
return v___x_332_;
}
}
}
else
{
lean_object* v___x_335_; lean_object* v_numSteps_336_; lean_object* v_persistentCache_337_; lean_object* v_transientCache_338_; lean_object* v_funext_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_349_; 
v___x_335_ = lean_st_ref_take(v_a_314_);
v_numSteps_336_ = lean_ctor_get(v___x_335_, 0);
v_persistentCache_337_ = lean_ctor_get(v___x_335_, 1);
v_transientCache_338_ = lean_ctor_get(v___x_335_, 2);
v_funext_339_ = lean_ctor_get(v___x_335_, 3);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_349_ == 0)
{
v___x_341_ = v___x_335_;
v_isShared_342_ = v_isSharedCheck_349_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_funext_339_);
lean_inc(v_transientCache_338_);
lean_inc(v_persistentCache_337_);
lean_inc(v_numSteps_336_);
lean_dec(v___x_335_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_349_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_inc_ref(v_r_313_);
v___x_343_ = l_Lean_PersistentHashMap_insert___redArg(v___f_316_, v___f_317_, v_transientCache_338_, v_e_312_, v_r_313_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 2, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_numSteps_336_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_persistentCache_337_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_funext_339_);
v___x_345_ = v_reuseFailAlloc_348_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_st_ref_put(v_a_314_, v___x_345_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_r_313_);
return v___x_347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object* v_e_352_, lean_object* v_r_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(v_e_352_, v_r_353_, v_a_354_);
lean_dec(v_a_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(lean_object* v_e_357_, lean_object* v_r_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___f_369_; lean_object* v___f_370_; uint8_t v___y_372_; 
v___f_369_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_370_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
if (lean_obj_tag(v_r_358_) == 0)
{
uint8_t v_contextDependent_403_; 
v_contextDependent_403_ = lean_ctor_get_uint8(v_r_358_, 1);
v___y_372_ = v_contextDependent_403_;
goto v___jp_371_;
}
else
{
uint8_t v_contextDependent_404_; 
v_contextDependent_404_ = lean_ctor_get_uint8(v_r_358_, sizeof(void*)*2 + 1);
v___y_372_ = v_contextDependent_404_;
goto v___jp_371_;
}
v___jp_371_:
{
if (v___y_372_ == 0)
{
lean_object* v___x_373_; lean_object* v_numSteps_374_; lean_object* v_persistentCache_375_; lean_object* v_transientCache_376_; lean_object* v_funext_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_387_; 
v___x_373_ = lean_st_ref_take(v_a_361_);
v_numSteps_374_ = lean_ctor_get(v___x_373_, 0);
v_persistentCache_375_ = lean_ctor_get(v___x_373_, 1);
v_transientCache_376_ = lean_ctor_get(v___x_373_, 2);
v_funext_377_ = lean_ctor_get(v___x_373_, 3);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_387_ == 0)
{
v___x_379_ = v___x_373_;
v_isShared_380_ = v_isSharedCheck_387_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_funext_377_);
lean_inc(v_transientCache_376_);
lean_inc(v_persistentCache_375_);
lean_inc(v_numSteps_374_);
lean_dec(v___x_373_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_387_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_inc_ref(v_r_358_);
v___x_381_ = l_Lean_PersistentHashMap_insert___redArg(v___f_369_, v___f_370_, v_persistentCache_375_, v_e_357_, v_r_358_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_numSteps_374_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_transientCache_376_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_funext_377_);
v___x_383_ = v_reuseFailAlloc_386_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_st_ref_put(v_a_361_, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_r_358_);
return v___x_385_;
}
}
}
else
{
lean_object* v___x_388_; lean_object* v_numSteps_389_; lean_object* v_persistentCache_390_; lean_object* v_transientCache_391_; lean_object* v_funext_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_402_; 
v___x_388_ = lean_st_ref_take(v_a_361_);
v_numSteps_389_ = lean_ctor_get(v___x_388_, 0);
v_persistentCache_390_ = lean_ctor_get(v___x_388_, 1);
v_transientCache_391_ = lean_ctor_get(v___x_388_, 2);
v_funext_392_ = lean_ctor_get(v___x_388_, 3);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_402_ == 0)
{
v___x_394_ = v___x_388_;
v_isShared_395_ = v_isSharedCheck_402_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_funext_392_);
lean_inc(v_transientCache_391_);
lean_inc(v_persistentCache_390_);
lean_inc(v_numSteps_389_);
lean_dec(v___x_388_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_402_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
lean_inc_ref(v_r_358_);
v___x_396_ = l_Lean_PersistentHashMap_insert___redArg(v___f_369_, v___f_370_, v_transientCache_391_, v_e_357_, v_r_358_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 2, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_numSteps_389_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_persistentCache_390_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_funext_392_);
v___x_398_ = v_reuseFailAlloc_401_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_st_ref_put(v_a_361_, v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_r_358_);
return v___x_400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object* v_e_405_, lean_object* v_r_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(v_e_405_, v_r_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
return v_res_417_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = l_Lean_maxRecDepthErrorMessage;
v___x_424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3);
v___x_426_ = l_Lean_MessageData_ofFormat(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4);
v___x_428_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2));
v___x_429_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(lean_object* v_ref_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_ref_430_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(lean_object* v_ref_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_object* v_00_u03b1_438_, lean_object* v_ref_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_439_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(lean_object* v_00_u03b1_451_, lean_object* v_ref_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(v_00_u03b1_451_, v_ref_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_post_476_; lean_object* v___x_477_; 
v_post_476_ = lean_ctor_get(v___y_466_, 1);
lean_inc_ref(v_post_476_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
lean_inc(v___y_472_);
lean_inc_ref(v___y_471_);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
v___x_477_ = lean_apply_11(v_post_476_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, lean_box(0));
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v_x_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
lean_object* v_ks_495_; lean_object* v_vs_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_522_; 
v_ks_495_ = lean_ctor_get(v_x_491_, 0);
v_vs_496_ = lean_ctor_get(v_x_491_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_x_491_);
if (v_isSharedCheck_522_ == 0)
{
v___x_498_ = v_x_491_;
v_isShared_499_ = v_isSharedCheck_522_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_vs_496_);
lean_inc(v_ks_495_);
lean_dec(v_x_491_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_522_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_array_get_size(v_ks_495_);
v___x_501_ = lean_nat_dec_lt(v_x_492_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec(v_x_492_);
v___x_502_ = lean_array_push(v_ks_495_, v_x_493_);
v___x_503_ = lean_array_push(v_vs_496_, v_x_494_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_503_);
lean_ctor_set(v___x_498_, 0, v___x_502_);
v___x_505_ = v___x_498_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v_k_x27_507_; size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v_k_x27_507_ = lean_array_fget_borrowed(v_ks_495_, v_x_492_);
v___x_508_ = lean_ptr_addr(v_x_493_);
v___x_509_ = lean_ptr_addr(v_k_x27_507_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_512_; 
if (v_isShared_499_ == 0)
{
v___x_512_ = v___x_498_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_ks_495_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_vs_496_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v_x_492_, v___x_513_);
lean_dec(v_x_492_);
v_x_491_ = v___x_512_;
v_x_492_ = v___x_514_;
goto _start;
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_517_ = lean_array_fset(v_ks_495_, v_x_492_, v_x_493_);
v___x_518_ = lean_array_fset(v_vs_496_, v_x_492_, v_x_494_);
lean_dec(v_x_492_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_518_);
lean_ctor_set(v___x_498_, 0, v___x_517_);
v___x_520_ = v___x_498_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_523_, lean_object* v_k_524_, lean_object* v_v_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_n_523_, v___x_526_, v_k_524_, v_v_525_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* v_x_529_, size_t v_x_530_, size_t v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v_es_534_; size_t v___x_535_; size_t v___x_536_; lean_object* v_j_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_es_534_ = lean_ctor_get(v_x_529_, 0);
v___x_535_ = ((size_t)31ULL);
v___x_536_ = lean_usize_land(v_x_530_, v___x_535_);
v_j_537_ = lean_usize_to_nat(v___x_536_);
v___x_538_ = lean_array_get_size(v_es_534_);
v___x_539_ = lean_nat_dec_lt(v_j_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_dec(v_j_537_);
lean_dec(v_x_533_);
lean_dec_ref(v_x_532_);
return v_x_529_;
}
else
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_580_; 
lean_inc_ref(v_es_534_);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_529_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_x_529_, 0);
lean_dec(v_unused_581_);
v___x_541_ = v_x_529_;
v_isShared_542_ = v_isSharedCheck_580_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_x_529_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_580_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_v_543_; lean_object* v___x_544_; lean_object* v_xs_x27_545_; lean_object* v___y_547_; 
v_v_543_ = lean_array_fget(v_es_534_, v_j_537_);
v___x_544_ = lean_box(0);
v_xs_x27_545_ = lean_array_fset(v_es_534_, v_j_537_, v___x_544_);
switch(lean_obj_tag(v_v_543_))
{
case 0:
{
lean_object* v_key_552_; lean_object* v_val_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_565_; 
v_key_552_ = lean_ctor_get(v_v_543_, 0);
v_val_553_ = lean_ctor_get(v_v_543_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_v_543_);
if (v_isSharedCheck_565_ == 0)
{
v___x_555_ = v_v_543_;
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_val_553_);
lean_inc(v_key_552_);
lean_dec(v_v_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_ptr_addr(v_x_532_);
v___x_558_ = lean_ptr_addr(v_key_552_);
v___x_559_ = lean_usize_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_del_object(v___x_555_);
v___x_560_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_552_, v_val_553_, v_x_532_, v_x_533_);
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
v___y_547_ = v___x_561_;
goto v___jp_546_;
}
else
{
lean_object* v___x_563_; 
lean_dec(v_val_553_);
lean_dec(v_key_552_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v_x_533_);
lean_ctor_set(v___x_555_, 0, v_x_532_);
v___x_563_ = v___x_555_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_x_532_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_x_533_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
v___y_547_ = v___x_563_;
goto v___jp_546_;
}
}
}
}
case 1:
{
lean_object* v_node_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_578_; 
v_node_566_ = lean_ctor_get(v_v_543_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_v_543_);
if (v_isSharedCheck_578_ == 0)
{
v___x_568_ = v_v_543_;
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_node_566_);
lean_dec(v_v_543_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_570_ = ((size_t)5ULL);
v___x_571_ = lean_usize_shift_right(v_x_530_, v___x_570_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_x_531_, v___x_572_);
v___x_574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_566_, v___x_571_, v___x_573_, v_x_532_, v_x_533_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_574_);
v___x_576_ = v___x_568_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
v___y_547_ = v___x_576_;
goto v___jp_546_;
}
}
}
default: 
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_x_532_);
lean_ctor_set(v___x_579_, 1, v_x_533_);
v___y_547_ = v___x_579_;
goto v___jp_546_;
}
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_array_fset(v_xs_x27_545_, v_j_537_, v___y_547_);
lean_dec(v_j_537_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_548_);
v___x_550_ = v___x_541_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
else
{
lean_object* v_ks_582_; lean_object* v_vs_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_601_; 
v_ks_582_ = lean_ctor_get(v_x_529_, 0);
v_vs_583_ = lean_ctor_get(v_x_529_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_529_);
if (v_isSharedCheck_601_ == 0)
{
v___x_585_ = v_x_529_;
v_isShared_586_ = v_isSharedCheck_601_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_vs_583_);
lean_inc(v_ks_582_);
lean_dec(v_x_529_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_601_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_ks_582_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_vs_583_);
v___x_588_ = v_reuseFailAlloc_600_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v_newNode_589_; size_t v___x_590_; uint8_t v___x_591_; 
v_newNode_589_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v___x_588_, v_x_532_, v_x_533_);
v___x_590_ = ((size_t)7ULL);
v___x_591_ = lean_usize_dec_le(v___x_590_, v_x_531_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_589_);
v___x_593_ = lean_unsigned_to_nat(4u);
v___x_594_ = lean_nat_dec_lt(v___x_592_, v___x_593_);
lean_dec(v___x_592_);
if (v___x_594_ == 0)
{
lean_object* v_ks_595_; lean_object* v_vs_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_ks_595_ = lean_ctor_get(v_newNode_589_, 0);
lean_inc_ref(v_ks_595_);
v_vs_596_ = lean_ctor_get(v_newNode_589_, 1);
lean_inc_ref(v_vs_596_);
lean_dec_ref(v_newNode_589_);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
v___x_599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_x_531_, v_ks_595_, v_vs_596_, v___x_597_, v___x_598_);
lean_dec_ref(v_vs_596_);
lean_dec_ref(v_ks_595_);
return v___x_599_;
}
else
{
return v_newNode_589_;
}
}
else
{
return v_newNode_589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_602_, lean_object* v_keys_603_, lean_object* v_vals_604_, lean_object* v_i_605_, lean_object* v_entries_606_){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_array_get_size(v_keys_603_);
v___x_608_ = lean_nat_dec_lt(v_i_605_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_i_605_);
return v_entries_606_;
}
else
{
lean_object* v_k_609_; lean_object* v_v_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; uint64_t v___x_614_; size_t v_h_615_; size_t v___x_616_; lean_object* v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v_h_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_k_609_ = lean_array_fget_borrowed(v_keys_603_, v_i_605_);
v_v_610_ = lean_array_fget_borrowed(v_vals_604_, v_i_605_);
v___x_611_ = lean_ptr_addr(v_k_609_);
v___x_612_ = ((size_t)3ULL);
v___x_613_ = lean_usize_shift_right(v___x_611_, v___x_612_);
v___x_614_ = lean_usize_to_uint64(v___x_613_);
v_h_615_ = lean_uint64_to_usize(v___x_614_);
v___x_616_ = ((size_t)5ULL);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_sub(v_depth_602_, v___x_618_);
v___x_620_ = lean_usize_mul(v___x_616_, v___x_619_);
v_h_621_ = lean_usize_shift_right(v_h_615_, v___x_620_);
v___x_622_ = lean_nat_add(v_i_605_, v___x_617_);
lean_dec(v_i_605_);
lean_inc(v_v_610_);
lean_inc(v_k_609_);
v___x_623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_606_, v_h_621_, v_depth_602_, v_k_609_, v_v_610_);
v_i_605_ = v___x_622_;
v_entries_606_ = v___x_623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_625_, lean_object* v_keys_626_, lean_object* v_vals_627_, lean_object* v_i_628_, lean_object* v_entries_629_){
_start:
{
size_t v_depth_boxed_630_; lean_object* v_res_631_; 
v_depth_boxed_630_ = lean_unbox_usize(v_depth_625_);
lean_dec(v_depth_625_);
v_res_631_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_630_, v_keys_626_, v_vals_627_, v_i_628_, v_entries_629_);
lean_dec_ref(v_vals_627_);
lean_dec_ref(v_keys_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
size_t v_x_109779__boxed_637_; size_t v_x_109780__boxed_638_; lean_object* v_res_639_; 
v_x_109779__boxed_637_ = lean_unbox_usize(v_x_633_);
lean_dec(v_x_633_);
v_x_109780__boxed_638_ = lean_unbox_usize(v_x_634_);
lean_dec(v_x_634_);
v_res_639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_632_, v_x_109779__boxed_637_, v_x_109780__boxed_638_, v_x_635_, v_x_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
size_t v___x_643_; size_t v___x_644_; size_t v___x_645_; uint64_t v___x_646_; size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___x_643_ = lean_ptr_addr(v_x_641_);
v___x_644_ = ((size_t)3ULL);
v___x_645_ = lean_usize_shift_right(v___x_643_, v___x_644_);
v___x_646_ = lean_usize_to_uint64(v___x_645_);
v___x_647_ = lean_uint64_to_usize(v___x_646_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_640_, v___x_647_, v___x_648_, v_x_641_, v_x_642_);
return v___x_649_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_650_; double v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_float_of_nat(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* v_cls_655_, lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_ref_662_; lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_708_; 
v_ref_662_ = lean_ctor_get(v___y_659_, 2);
v___x_663_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_708_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_708_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_708_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v_traceState_669_; lean_object* v_env_670_; lean_object* v_nextMacroScope_671_; lean_object* v_ngen_672_; lean_object* v_auxDeclNGen_673_; lean_object* v_cache_674_; lean_object* v_messages_675_; lean_object* v_infoState_676_; lean_object* v_snapshotTasks_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_707_; 
v___x_668_ = lean_st_ref_take(v___y_660_);
v_traceState_669_ = lean_ctor_get(v___x_668_, 4);
v_env_670_ = lean_ctor_get(v___x_668_, 0);
v_nextMacroScope_671_ = lean_ctor_get(v___x_668_, 1);
v_ngen_672_ = lean_ctor_get(v___x_668_, 2);
v_auxDeclNGen_673_ = lean_ctor_get(v___x_668_, 3);
v_cache_674_ = lean_ctor_get(v___x_668_, 5);
v_messages_675_ = lean_ctor_get(v___x_668_, 6);
v_infoState_676_ = lean_ctor_get(v___x_668_, 7);
v_snapshotTasks_677_ = lean_ctor_get(v___x_668_, 8);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_707_ == 0)
{
v___x_679_ = v___x_668_;
v_isShared_680_ = v_isSharedCheck_707_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snapshotTasks_677_);
lean_inc(v_infoState_676_);
lean_inc(v_messages_675_);
lean_inc(v_cache_674_);
lean_inc(v_traceState_669_);
lean_inc(v_auxDeclNGen_673_);
lean_inc(v_ngen_672_);
lean_inc(v_nextMacroScope_671_);
lean_inc(v_env_670_);
lean_dec(v___x_668_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_707_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
uint64_t v_tid_681_; lean_object* v_traces_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_706_; 
v_tid_681_ = lean_ctor_get_uint64(v_traceState_669_, sizeof(void*)*1);
v_traces_682_ = lean_ctor_get(v_traceState_669_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v_traceState_669_);
if (v_isSharedCheck_706_ == 0)
{
v___x_684_ = v_traceState_669_;
v_isShared_685_ = v_isSharedCheck_706_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_traces_682_);
lean_dec(v_traceState_669_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_706_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; double v___x_687_; uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_686_ = lean_box(0);
v___x_687_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0);
v___x_688_ = 0;
v___x_689_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1));
v___x_690_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_690_, 0, v_cls_655_);
lean_ctor_set(v___x_690_, 1, v___x_686_);
lean_ctor_set(v___x_690_, 2, v___x_689_);
lean_ctor_set_float(v___x_690_, sizeof(void*)*3, v___x_687_);
lean_ctor_set_float(v___x_690_, sizeof(void*)*3 + 8, v___x_687_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*3 + 16, v___x_688_);
v___x_691_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2));
v___x_692_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v_a_664_);
lean_ctor_set(v___x_692_, 2, v___x_691_);
lean_inc(v_ref_662_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_ref_662_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_PersistentArray_push___redArg(v_traces_682_, v___x_693_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_694_);
v___x_696_ = v___x_684_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_694_);
lean_ctor_set_uint64(v_reuseFailAlloc_705_, sizeof(void*)*1, v_tid_681_);
v___x_696_ = v_reuseFailAlloc_705_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 4, v___x_696_);
v___x_698_ = v___x_679_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_env_670_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_nextMacroScope_671_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_ngen_672_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_auxDeclNGen_673_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_704_, 5, v_cache_674_);
lean_ctor_set(v_reuseFailAlloc_704_, 6, v_messages_675_);
lean_ctor_set(v_reuseFailAlloc_704_, 7, v_infoState_676_);
lean_ctor_set(v_reuseFailAlloc_704_, 8, v_snapshotTasks_677_);
v___x_698_ = v_reuseFailAlloc_704_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = lean_st_ref_put(v___y_660_, v___x_698_);
v___x_700_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_700_);
v___x_702_ = v___x_666_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* v_cls_709_, lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_709_, v_msg_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_717_, lean_object* v_vals_718_, lean_object* v_i_719_, lean_object* v_k_720_){
_start:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_array_get_size(v_keys_717_);
v___x_722_ = lean_nat_dec_lt(v_i_719_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec(v_i_719_);
v___x_723_ = lean_box(0);
return v___x_723_;
}
else
{
lean_object* v_k_x27_724_; size_t v___x_725_; size_t v___x_726_; uint8_t v___x_727_; 
v_k_x27_724_ = lean_array_fget_borrowed(v_keys_717_, v_i_719_);
v___x_725_ = lean_ptr_addr(v_k_720_);
v___x_726_ = lean_ptr_addr(v_k_x27_724_);
v___x_727_ = lean_usize_dec_eq(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_i_719_, v___x_728_);
lean_dec(v_i_719_);
v_i_719_ = v___x_729_;
goto _start;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_array_fget_borrowed(v_vals_718_, v_i_719_);
lean_dec(v_i_719_);
lean_inc(v___x_731_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_733_, lean_object* v_vals_734_, lean_object* v_i_735_, lean_object* v_k_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_733_, v_vals_734_, v_i_735_, v_k_736_);
lean_dec_ref(v_k_736_);
lean_dec_ref(v_vals_734_);
lean_dec_ref(v_keys_733_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* v_x_738_, size_t v_x_739_, lean_object* v_x_740_){
_start:
{
if (lean_obj_tag(v_x_738_) == 0)
{
lean_object* v_es_741_; lean_object* v___x_742_; size_t v___x_743_; size_t v___x_744_; lean_object* v_j_745_; lean_object* v___x_746_; 
v_es_741_ = lean_ctor_get(v_x_738_, 0);
v___x_742_ = lean_box(2);
v___x_743_ = ((size_t)31ULL);
v___x_744_ = lean_usize_land(v_x_739_, v___x_743_);
v_j_745_ = lean_usize_to_nat(v___x_744_);
v___x_746_ = lean_array_get_borrowed(v___x_742_, v_es_741_, v_j_745_);
lean_dec(v_j_745_);
switch(lean_obj_tag(v___x_746_))
{
case 0:
{
lean_object* v_key_747_; lean_object* v_val_748_; size_t v___x_749_; size_t v___x_750_; uint8_t v___x_751_; 
v_key_747_ = lean_ctor_get(v___x_746_, 0);
v_val_748_ = lean_ctor_get(v___x_746_, 1);
v___x_749_ = lean_ptr_addr(v_x_740_);
v___x_750_ = lean_ptr_addr(v_key_747_);
v___x_751_ = lean_usize_dec_eq(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
v___x_752_ = lean_box(0);
return v___x_752_;
}
else
{
lean_object* v___x_753_; 
lean_inc(v_val_748_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v_val_748_);
return v___x_753_;
}
}
case 1:
{
lean_object* v_node_754_; size_t v___x_755_; size_t v___x_756_; 
v_node_754_ = lean_ctor_get(v___x_746_, 0);
v___x_755_ = ((size_t)5ULL);
v___x_756_ = lean_usize_shift_right(v_x_739_, v___x_755_);
v_x_738_ = v_node_754_;
v_x_739_ = v___x_756_;
goto _start;
}
default: 
{
lean_object* v___x_758_; 
v___x_758_ = lean_box(0);
return v___x_758_;
}
}
}
else
{
lean_object* v_ks_759_; lean_object* v_vs_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_ks_759_ = lean_ctor_get(v_x_738_, 0);
v_vs_760_ = lean_ctor_get(v_x_738_, 1);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_ks_759_, v_vs_760_, v___x_761_, v_x_740_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
size_t v_x_110081__boxed_766_; lean_object* v_res_767_; 
v_x_110081__boxed_766_ = lean_unbox_usize(v_x_764_);
lean_dec(v_x_764_);
v_res_767_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_763_, v_x_110081__boxed_766_, v_x_765_);
lean_dec_ref(v_x_765_);
lean_dec_ref(v_x_763_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; uint64_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
v___x_770_ = lean_ptr_addr(v_x_769_);
v___x_771_ = ((size_t)3ULL);
v___x_772_ = lean_usize_shift_right(v___x_770_, v___x_771_);
v___x_773_ = lean_usize_to_uint64(v___x_772_);
v___x_774_ = lean_uint64_to_usize(v___x_773_);
v___x_775_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_768_, v___x_774_, v_x_769_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_776_, v_x_777_);
lean_dec_ref(v_x_777_);
lean_dec_ref(v_x_776_);
return v_res_778_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_783_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1));
v___x_784_ = l_Lean_Name_append(v___x_783_, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* lean_sym_simp(lean_object* v_e_u2081_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; uint8_t v___y_843_; uint8_t v___y_844_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; uint8_t v___y_850_; uint8_t v___y_851_; lean_object* v_e_u2082_854_; lean_object* v_h_u2081_855_; uint8_t v_cd_u2081_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; uint8_t v___y_974_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; uint8_t v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; uint8_t v___y_987_; lean_object* v___y_988_; uint8_t v___y_989_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; uint8_t v___y_1000_; lean_object* v___y_1001_; lean_object* v_a_1002_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; uint8_t v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; uint8_t v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; uint8_t v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1035_; lean_object* v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; uint8_t v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; uint8_t v___y_1047_; lean_object* v___y_1048_; uint8_t v___y_1049_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; uint8_t v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; uint8_t v___y_1064_; lean_object* v___y_1065_; uint8_t v___y_1066_; lean_object* v_toCold_1068_; lean_object* v_currRecDepth_1069_; lean_object* v_ref_1070_; uint8_t v_diag_1071_; uint8_t v_suppressElabErrors_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1371_; 
v_toCold_1068_ = lean_ctor_get(v_a_802_, 0);
v_currRecDepth_1069_ = lean_ctor_get(v_a_802_, 1);
v_ref_1070_ = lean_ctor_get(v_a_802_, 2);
v_diag_1071_ = lean_ctor_get_uint8(v_a_802_, sizeof(void*)*3);
v_suppressElabErrors_1072_ = lean_ctor_get_uint8(v_a_802_, sizeof(void*)*3 + 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_802_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1074_ = v_a_802_;
v_isShared_1075_ = v_isSharedCheck_1371_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_ref_1070_);
lean_inc(v_currRecDepth_1069_);
lean_inc(v_toCold_1068_);
lean_dec(v_a_802_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1371_;
goto v_resetjp_1073_;
}
v___jp_805_:
{
if (v___y_808_ == 0)
{
lean_object* v___x_809_; lean_object* v_numSteps_810_; lean_object* v_persistentCache_811_; lean_object* v_transientCache_812_; lean_object* v_funext_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_823_; 
v___x_809_ = lean_st_ref_take(v___y_807_);
v_numSteps_810_ = lean_ctor_get(v___x_809_, 0);
v_persistentCache_811_ = lean_ctor_get(v___x_809_, 1);
v_transientCache_812_ = lean_ctor_get(v___x_809_, 2);
v_funext_813_ = lean_ctor_get(v___x_809_, 3);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_823_ == 0)
{
v___x_815_ = v___x_809_;
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_funext_813_);
lean_inc(v_transientCache_812_);
lean_inc(v_persistentCache_811_);
lean_inc(v_numSteps_810_);
lean_dec(v___x_809_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_inc_ref(v___y_806_);
v___x_817_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_811_, v_e_u2081_794_, v___y_806_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_numSteps_810_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_transientCache_812_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_funext_813_);
v___x_819_ = v_reuseFailAlloc_822_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_st_ref_put(v___y_807_, v___x_819_);
lean_dec(v___y_807_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___y_806_);
return v___x_821_;
}
}
}
else
{
lean_object* v___x_824_; lean_object* v_numSteps_825_; lean_object* v_persistentCache_826_; lean_object* v_transientCache_827_; lean_object* v_funext_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_838_; 
v___x_824_ = lean_st_ref_take(v___y_807_);
v_numSteps_825_ = lean_ctor_get(v___x_824_, 0);
v_persistentCache_826_ = lean_ctor_get(v___x_824_, 1);
v_transientCache_827_ = lean_ctor_get(v___x_824_, 2);
v_funext_828_ = lean_ctor_get(v___x_824_, 3);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_838_ == 0)
{
v___x_830_ = v___x_824_;
v_isShared_831_ = v_isSharedCheck_838_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_funext_828_);
lean_inc(v_transientCache_827_);
lean_inc(v_persistentCache_826_);
lean_inc(v_numSteps_825_);
lean_dec(v___x_824_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_838_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
lean_inc_ref(v___y_806_);
v___x_832_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_827_, v_e_u2081_794_, v___y_806_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 2, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_numSteps_825_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_persistentCache_826_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v_funext_828_);
v___x_834_ = v_reuseFailAlloc_837_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_st_ref_put(v___y_807_, v___x_834_);
lean_dec(v___y_807_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___y_806_);
return v___x_836_;
}
}
}
}
v___jp_839_:
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_845_, 0, v___y_841_);
lean_ctor_set(v___x_845_, 1, v___y_840_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*2, v___y_843_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*2 + 1, v___y_844_);
v___y_806_ = v___x_845_;
v___y_807_ = v___y_842_;
v___y_808_ = v___y_844_;
goto v___jp_805_;
}
v___jp_846_:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_852_, 0, v___y_847_);
lean_ctor_set(v___x_852_, 1, v___y_848_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*2, v___y_850_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*2 + 1, v___y_851_);
v___y_806_ = v___x_852_;
v___y_807_ = v___y_849_;
v___y_808_ = v___y_851_;
goto v___jp_805_;
}
v___jp_853_:
{
lean_object* v___x_866_; 
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc(v___y_859_);
lean_inc_ref(v_e_u2082_854_);
v___x_866_ = lean_sym_simp(v_e_u2082_854_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
if (lean_obj_tag(v_a_867_) == 0)
{
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
if (v_cd_u2081_856_ == 0)
{
uint8_t v_done_868_; uint8_t v_contextDependent_869_; 
v_done_868_ = lean_ctor_get_uint8(v_a_867_, 0);
v_contextDependent_869_ = lean_ctor_get_uint8(v_a_867_, 1);
lean_dec_ref_known(v_a_867_, 0);
v___y_840_ = v_h_u2081_855_;
v___y_841_ = v_e_u2082_854_;
v___y_842_ = v___y_859_;
v___y_843_ = v_done_868_;
v___y_844_ = v_contextDependent_869_;
goto v___jp_839_;
}
else
{
uint8_t v_done_870_; 
v_done_870_ = lean_ctor_get_uint8(v_a_867_, 0);
lean_dec_ref_known(v_a_867_, 0);
v___y_840_ = v_h_u2081_855_;
v___y_841_ = v_e_u2082_854_;
v___y_842_ = v___y_859_;
v___y_843_ = v_done_870_;
v___y_844_ = v_cd_u2081_856_;
goto v___jp_839_;
}
}
else
{
lean_object* v_e_x27_871_; lean_object* v_proof_872_; uint8_t v_done_873_; uint8_t v_contextDependent_874_; lean_object* v___x_875_; 
v_e_x27_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc_ref_n(v_e_x27_871_, 2);
v_proof_872_ = lean_ctor_get(v_a_867_, 1);
lean_inc_ref(v_proof_872_);
v_done_873_ = lean_ctor_get_uint8(v_a_867_, sizeof(void*)*2);
v_contextDependent_874_ = lean_ctor_get_uint8(v_a_867_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_867_, 2);
lean_inc_ref(v_e_u2081_794_);
v___x_875_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_794_, v_e_u2082_854_, v_h_u2081_855_, v_e_x27_871_, v_proof_872_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
if (lean_obj_tag(v___x_875_) == 0)
{
if (v_cd_u2081_856_ == 0)
{
lean_object* v_a_876_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___y_847_ = v_e_x27_871_;
v___y_848_ = v_a_876_;
v___y_849_ = v___y_859_;
v___y_850_ = v_done_873_;
v___y_851_ = v_contextDependent_874_;
goto v___jp_846_;
}
else
{
lean_object* v_a_877_; 
v_a_877_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_875_, 1);
v___y_847_ = v_e_x27_871_;
v___y_848_ = v_a_877_;
v___y_849_ = v___y_859_;
v___y_850_ = v_done_873_;
v___y_851_ = v_cd_u2081_856_;
goto v___jp_846_;
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v_e_x27_871_);
lean_dec(v___y_859_);
lean_dec_ref(v_e_u2081_794_);
v_a_878_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_875_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_875_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
else
{
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v_h_u2081_855_);
lean_dec_ref(v_e_u2082_854_);
lean_dec_ref(v_e_u2081_794_);
return v___x_866_;
}
}
v___jp_886_:
{
if (lean_obj_tag(v___y_896_) == 0)
{
uint8_t v_contextDependent_897_; 
lean_dec_ref(v___y_895_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
v_contextDependent_897_ = lean_ctor_get_uint8(v___y_896_, 1);
if (v_contextDependent_897_ == 0)
{
lean_object* v___x_898_; lean_object* v_numSteps_899_; lean_object* v_persistentCache_900_; lean_object* v_transientCache_901_; lean_object* v_funext_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v___x_898_ = lean_st_ref_take(v___y_894_);
v_numSteps_899_ = lean_ctor_get(v___x_898_, 0);
v_persistentCache_900_ = lean_ctor_get(v___x_898_, 1);
v_transientCache_901_ = lean_ctor_get(v___x_898_, 2);
v_funext_902_ = lean_ctor_get(v___x_898_, 3);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v___x_898_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_funext_902_);
lean_inc(v_transientCache_901_);
lean_inc(v_persistentCache_900_);
lean_inc(v_numSteps_899_);
lean_dec(v___x_898_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
lean_inc_ref(v___y_896_);
v___x_906_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_900_, v_e_u2081_794_, v___y_896_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_numSteps_899_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_transientCache_901_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_funext_902_);
v___x_908_ = v_reuseFailAlloc_911_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_st_ref_put(v___y_894_, v___x_908_);
lean_dec(v___y_894_);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___y_896_);
return v___x_910_;
}
}
}
else
{
lean_object* v___x_913_; lean_object* v_numSteps_914_; lean_object* v_persistentCache_915_; lean_object* v_transientCache_916_; lean_object* v_funext_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_927_; 
v___x_913_ = lean_st_ref_take(v___y_894_);
v_numSteps_914_ = lean_ctor_get(v___x_913_, 0);
v_persistentCache_915_ = lean_ctor_get(v___x_913_, 1);
v_transientCache_916_ = lean_ctor_get(v___x_913_, 2);
v_funext_917_ = lean_ctor_get(v___x_913_, 3);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_927_ == 0)
{
v___x_919_ = v___x_913_;
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_funext_917_);
lean_inc(v_transientCache_916_);
lean_inc(v_persistentCache_915_);
lean_inc(v_numSteps_914_);
lean_dec(v___x_913_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_inc_ref(v___y_896_);
v___x_921_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_916_, v_e_u2081_794_, v___y_896_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 2, v___x_921_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_numSteps_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_persistentCache_915_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_funext_917_);
v___x_923_ = v_reuseFailAlloc_926_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_st_ref_put(v___y_894_, v___x_923_);
lean_dec(v___y_894_);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v___y_896_);
return v___x_925_;
}
}
}
}
else
{
uint8_t v_done_928_; 
v_done_928_ = lean_ctor_get_uint8(v___y_896_, sizeof(void*)*2);
if (v_done_928_ == 0)
{
lean_object* v_e_x27_929_; lean_object* v_proof_930_; uint8_t v_contextDependent_931_; 
v_e_x27_929_ = lean_ctor_get(v___y_896_, 0);
lean_inc_ref(v_e_x27_929_);
v_proof_930_ = lean_ctor_get(v___y_896_, 1);
lean_inc_ref(v_proof_930_);
v_contextDependent_931_ = lean_ctor_get_uint8(v___y_896_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v___y_896_, 2);
v_e_u2082_854_ = v_e_x27_929_;
v_h_u2081_855_ = v_proof_930_;
v_cd_u2081_856_ = v_contextDependent_931_;
v___y_857_ = v___y_891_;
v___y_858_ = v___y_889_;
v___y_859_ = v___y_894_;
v___y_860_ = v___y_888_;
v___y_861_ = v___y_892_;
v___y_862_ = v___y_895_;
v___y_863_ = v___y_893_;
v___y_864_ = v___y_890_;
v___y_865_ = v___y_887_;
goto v___jp_853_;
}
else
{
uint8_t v_contextDependent_932_; 
lean_dec_ref(v___y_895_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
v_contextDependent_932_ = lean_ctor_get_uint8(v___y_896_, sizeof(void*)*2 + 1);
if (v_contextDependent_932_ == 0)
{
lean_object* v___x_933_; lean_object* v_numSteps_934_; lean_object* v_persistentCache_935_; lean_object* v_transientCache_936_; lean_object* v_funext_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v___x_933_ = lean_st_ref_take(v___y_894_);
v_numSteps_934_ = lean_ctor_get(v___x_933_, 0);
v_persistentCache_935_ = lean_ctor_get(v___x_933_, 1);
v_transientCache_936_ = lean_ctor_get(v___x_933_, 2);
v_funext_937_ = lean_ctor_get(v___x_933_, 3);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_947_ == 0)
{
v___x_939_ = v___x_933_;
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_funext_937_);
lean_inc(v_transientCache_936_);
lean_inc(v_persistentCache_935_);
lean_inc(v_numSteps_934_);
lean_dec(v___x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_inc_ref(v___y_896_);
v___x_941_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_935_, v_e_u2081_794_, v___y_896_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_numSteps_934_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_transientCache_936_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_funext_937_);
v___x_943_ = v_reuseFailAlloc_946_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_st_ref_put(v___y_894_, v___x_943_);
lean_dec(v___y_894_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___y_896_);
return v___x_945_;
}
}
}
else
{
lean_object* v___x_948_; lean_object* v_numSteps_949_; lean_object* v_persistentCache_950_; lean_object* v_transientCache_951_; lean_object* v_funext_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_962_; 
v___x_948_ = lean_st_ref_take(v___y_894_);
v_numSteps_949_ = lean_ctor_get(v___x_948_, 0);
v_persistentCache_950_ = lean_ctor_get(v___x_948_, 1);
v_transientCache_951_ = lean_ctor_get(v___x_948_, 2);
v_funext_952_ = lean_ctor_get(v___x_948_, 3);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_962_ == 0)
{
v___x_954_ = v___x_948_;
v_isShared_955_ = v_isSharedCheck_962_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_funext_952_);
lean_inc(v_transientCache_951_);
lean_inc(v_persistentCache_950_);
lean_inc(v_numSteps_949_);
lean_dec(v___x_948_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_962_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
lean_inc_ref(v___y_896_);
v___x_956_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_951_, v_e_u2081_794_, v___y_896_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 2, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_numSteps_949_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_persistentCache_950_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_funext_952_);
v___x_958_ = v_reuseFailAlloc_961_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_st_ref_put(v___y_894_, v___x_958_);
lean_dec(v___y_894_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___y_896_);
return v___x_960_;
}
}
}
}
}
}
v___jp_963_:
{
if (v___y_974_ == 0)
{
v___y_887_ = v___y_967_;
v___y_888_ = v___y_966_;
v___y_889_ = v___y_965_;
v___y_890_ = v___y_968_;
v___y_891_ = v___y_969_;
v___y_892_ = v___y_970_;
v___y_893_ = v___y_972_;
v___y_894_ = v___y_971_;
v___y_895_ = v___y_973_;
v___y_896_ = v___y_964_;
goto v___jp_886_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_964_);
v___y_887_ = v___y_967_;
v___y_888_ = v___y_966_;
v___y_889_ = v___y_965_;
v___y_890_ = v___y_968_;
v___y_891_ = v___y_969_;
v___y_892_ = v___y_970_;
v___y_893_ = v___y_972_;
v___y_894_ = v___y_971_;
v___y_895_ = v___y_973_;
v___y_896_ = v___x_975_;
goto v___jp_886_;
}
}
v___jp_976_:
{
if (v___y_989_ == 0)
{
v___y_964_ = v___y_977_;
v___y_965_ = v___y_984_;
v___y_966_ = v___y_985_;
v___y_967_ = v___y_978_;
v___y_968_ = v___y_986_;
v___y_969_ = v___y_979_;
v___y_970_ = v___y_980_;
v___y_971_ = v___y_988_;
v___y_972_ = v___y_981_;
v___y_973_ = v___y_983_;
v___y_974_ = v___y_982_;
goto v___jp_963_;
}
else
{
v___y_964_ = v___y_977_;
v___y_965_ = v___y_984_;
v___y_966_ = v___y_985_;
v___y_967_ = v___y_978_;
v___y_968_ = v___y_986_;
v___y_969_ = v___y_979_;
v___y_970_ = v___y_980_;
v___y_971_ = v___y_988_;
v___y_972_ = v___y_981_;
v___y_973_ = v___y_983_;
v___y_974_ = v___y_987_;
goto v___jp_963_;
}
}
v___jp_990_:
{
if (v___y_1000_ == 0)
{
v___y_887_ = v___y_993_;
v___y_888_ = v___y_992_;
v___y_889_ = v___y_991_;
v___y_890_ = v___y_994_;
v___y_891_ = v___y_996_;
v___y_892_ = v___y_997_;
v___y_893_ = v___y_999_;
v___y_894_ = v___y_998_;
v___y_895_ = v___y_1001_;
v___y_896_ = v_a_1002_;
goto v___jp_886_;
}
else
{
if (lean_obj_tag(v_a_1002_) == 0)
{
uint8_t v_contextDependent_1003_; 
v_contextDependent_1003_ = lean_ctor_get_uint8(v_a_1002_, 1);
v___y_977_ = v_a_1002_;
v___y_978_ = v___y_993_;
v___y_979_ = v___y_996_;
v___y_980_ = v___y_997_;
v___y_981_ = v___y_999_;
v___y_982_ = v___y_1000_;
v___y_983_ = v___y_1001_;
v___y_984_ = v___y_991_;
v___y_985_ = v___y_992_;
v___y_986_ = v___y_994_;
v___y_987_ = v___y_995_;
v___y_988_ = v___y_998_;
v___y_989_ = v_contextDependent_1003_;
goto v___jp_976_;
}
else
{
uint8_t v_contextDependent_1004_; 
v_contextDependent_1004_ = lean_ctor_get_uint8(v_a_1002_, sizeof(void*)*2 + 1);
v___y_977_ = v_a_1002_;
v___y_978_ = v___y_993_;
v___y_979_ = v___y_996_;
v___y_980_ = v___y_997_;
v___y_981_ = v___y_999_;
v___y_982_ = v___y_1000_;
v___y_983_ = v___y_1001_;
v___y_984_ = v___y_991_;
v___y_985_ = v___y_992_;
v___y_986_ = v___y_994_;
v___y_987_ = v___y_995_;
v___y_988_ = v___y_998_;
v___y_989_ = v_contextDependent_1004_;
goto v___jp_976_;
}
}
}
v___jp_1005_:
{
if (lean_obj_tag(v___y_1017_) == 0)
{
lean_object* v_a_1018_; 
v_a_1018_ = lean_ctor_get(v___y_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___y_1017_, 1);
v___y_991_ = v___y_1008_;
v___y_992_ = v___y_1007_;
v___y_993_ = v___y_1006_;
v___y_994_ = v___y_1009_;
v___y_995_ = v___y_1010_;
v___y_996_ = v___y_1011_;
v___y_997_ = v___y_1012_;
v___y_998_ = v___y_1014_;
v___y_999_ = v___y_1013_;
v___y_1000_ = v___y_1015_;
v___y_1001_ = v___y_1016_;
v_a_1002_ = v_a_1018_;
goto v___jp_990_;
}
else
{
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v_e_u2081_794_);
return v___y_1017_;
}
}
v___jp_1019_:
{
if (v___y_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1030_);
v___y_991_ = v___y_1026_;
v___y_992_ = v___y_1027_;
v___y_993_ = v___y_1020_;
v___y_994_ = v___y_1028_;
v___y_995_ = v___y_1029_;
v___y_996_ = v___y_1021_;
v___y_997_ = v___y_1022_;
v___y_998_ = v___y_1031_;
v___y_999_ = v___y_1023_;
v___y_1000_ = v___y_1024_;
v___y_1001_ = v___y_1025_;
v_a_1002_ = v___x_1033_;
goto v___jp_990_;
}
else
{
v___y_991_ = v___y_1026_;
v___y_992_ = v___y_1027_;
v___y_993_ = v___y_1020_;
v___y_994_ = v___y_1028_;
v___y_995_ = v___y_1029_;
v___y_996_ = v___y_1021_;
v___y_997_ = v___y_1022_;
v___y_998_ = v___y_1031_;
v___y_999_ = v___y_1023_;
v___y_1000_ = v___y_1024_;
v___y_1001_ = v___y_1025_;
v_a_1002_ = v___y_1030_;
goto v___jp_990_;
}
}
v___jp_1034_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1050_, 0, v___y_1045_);
lean_ctor_set(v___x_1050_, 1, v___y_1035_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*2, v___y_1037_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*2 + 1, v___y_1049_);
v___y_991_ = v___y_1043_;
v___y_992_ = v___y_1044_;
v___y_993_ = v___y_1036_;
v___y_994_ = v___y_1046_;
v___y_995_ = v___y_1047_;
v___y_996_ = v___y_1038_;
v___y_997_ = v___y_1039_;
v___y_998_ = v___y_1048_;
v___y_999_ = v___y_1040_;
v___y_1000_ = v___y_1041_;
v___y_1001_ = v___y_1042_;
v_a_1002_ = v___x_1050_;
goto v___jp_990_;
}
v___jp_1051_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1067_, 0, v___y_1062_);
lean_ctor_set(v___x_1067_, 1, v___y_1053_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*2, v___y_1058_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*2 + 1, v___y_1066_);
v___y_991_ = v___y_1060_;
v___y_992_ = v___y_1061_;
v___y_993_ = v___y_1052_;
v___y_994_ = v___y_1063_;
v___y_995_ = v___y_1064_;
v___y_996_ = v___y_1054_;
v___y_997_ = v___y_1055_;
v___y_998_ = v___y_1065_;
v___y_999_ = v___y_1056_;
v___y_1000_ = v___y_1057_;
v___y_1001_ = v___y_1059_;
v_a_1002_ = v___x_1067_;
goto v___jp_990_;
}
v_resetjp_1073_:
{
lean_object* v_maxRecDepth_1076_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_maxRecDepth_1076_ = lean_ctor_get(v_toCold_1068_, 3);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_nat_dec_eq(v_maxRecDepth_1076_, v___x_1367_);
if (v___x_1368_ == 0)
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_nat_dec_eq(v_currRecDepth_1069_, v_maxRecDepth_1076_);
if (v___x_1369_ == 0)
{
goto v___jp_1337_;
}
else
{
lean_object* v___x_1370_; 
lean_del_object(v___x_1074_);
lean_dec(v_currRecDepth_1069_);
lean_dec_ref(v_toCold_1068_);
lean_dec(v_a_803_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_e_u2081_794_);
v___x_1370_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_1070_);
return v___x_1370_;
}
}
else
{
goto v___jp_1337_;
}
v___jp_1077_:
{
lean_object* v___x_1088_; lean_object* v_persistentCache_1089_; lean_object* v_transientCache_1090_; lean_object* v_funext_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1216_; 
v___x_1088_ = lean_st_ref_take(v___y_1081_);
v_persistentCache_1089_ = lean_ctor_get(v___x_1088_, 1);
v_transientCache_1090_ = lean_ctor_get(v___x_1088_, 2);
v_funext_1091_ = lean_ctor_get(v___x_1088_, 3);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1088_, 0);
lean_dec(v_unused_1217_);
v___x_1093_ = v___x_1088_;
v_isShared_1094_ = v_isSharedCheck_1216_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_funext_1091_);
lean_inc(v_transientCache_1090_);
lean_inc(v_persistentCache_1089_);
lean_dec(v___x_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1216_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___y_1078_);
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___y_1078_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_persistentCache_1089_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_transientCache_1090_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_funext_1091_);
v___x_1096_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v_pre_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_st_ref_put(v___y_1081_, v___x_1096_);
v_pre_1098_ = lean_ctor_get(v___y_1079_, 0);
lean_inc_ref(v_pre_1098_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v_e_u2081_794_);
v___x_1099_ = lean_apply_11(v_pre_1098_, v_e_u2081_794_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, lean_box(0));
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1214_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1214_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1214_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
if (lean_obj_tag(v_a_1100_) == 0)
{
uint8_t v_done_1104_; 
v_done_1104_ = lean_ctor_get_uint8(v_a_1100_, 0);
if (v_done_1104_ == 0)
{
uint8_t v_contextDependent_1105_; lean_object* v___x_1106_; 
lean_del_object(v___x_1102_);
v_contextDependent_1105_ = lean_ctor_get_uint8(v_a_1100_, 1);
lean_dec_ref_known(v_a_1100_, 0);
lean_inc_ref(v_e_u2081_794_);
v___x_1106_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_u2081_794_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
v___x_1108_ = lean_box(0);
if (lean_obj_tag(v_a_1107_) == 0)
{
uint8_t v_done_1109_; 
v_done_1109_ = lean_ctor_get_uint8(v_a_1107_, 0);
if (v_done_1109_ == 0)
{
uint8_t v_contextDependent_1110_; lean_object* v___x_1111_; 
lean_dec_ref_known(v___x_1106_, 1);
v_contextDependent_1110_ = lean_ctor_get_uint8(v_a_1107_, 1);
lean_dec_ref_known(v_a_1107_, 0);
lean_inc_ref(v_e_u2081_794_);
v___x_1111_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1108_, v_e_u2081_794_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1111_) == 0)
{
if (v_contextDependent_1110_ == 0)
{
lean_object* v_a_1112_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v___y_991_ = v___y_1080_;
v___y_992_ = v___y_1082_;
v___y_993_ = v___y_1087_;
v___y_994_ = v___y_1086_;
v___y_995_ = v_done_1104_;
v___y_996_ = v___y_1079_;
v___y_997_ = v___y_1083_;
v___y_998_ = v___y_1081_;
v___y_999_ = v___y_1085_;
v___y_1000_ = v_contextDependent_1105_;
v___y_1001_ = v___y_1084_;
v_a_1002_ = v_a_1112_;
goto v___jp_990_;
}
else
{
lean_object* v_a_1113_; 
v_a_1113_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1111_, 1);
if (lean_obj_tag(v_a_1113_) == 0)
{
uint8_t v_contextDependent_1114_; 
v_contextDependent_1114_ = lean_ctor_get_uint8(v_a_1113_, 1);
v___y_1020_ = v___y_1087_;
v___y_1021_ = v___y_1079_;
v___y_1022_ = v___y_1083_;
v___y_1023_ = v___y_1085_;
v___y_1024_ = v_contextDependent_1105_;
v___y_1025_ = v___y_1084_;
v___y_1026_ = v___y_1080_;
v___y_1027_ = v___y_1082_;
v___y_1028_ = v___y_1086_;
v___y_1029_ = v_done_1104_;
v___y_1030_ = v_a_1113_;
v___y_1031_ = v___y_1081_;
v___y_1032_ = v_contextDependent_1114_;
goto v___jp_1019_;
}
else
{
uint8_t v_contextDependent_1115_; 
v_contextDependent_1115_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*2 + 1);
v___y_1020_ = v___y_1087_;
v___y_1021_ = v___y_1079_;
v___y_1022_ = v___y_1083_;
v___y_1023_ = v___y_1085_;
v___y_1024_ = v_contextDependent_1105_;
v___y_1025_ = v___y_1084_;
v___y_1026_ = v___y_1080_;
v___y_1027_ = v___y_1082_;
v___y_1028_ = v___y_1086_;
v___y_1029_ = v_done_1104_;
v___y_1030_ = v_a_1113_;
v___y_1031_ = v___y_1081_;
v___y_1032_ = v_contextDependent_1115_;
goto v___jp_1019_;
}
}
}
else
{
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v_e_u2081_794_);
return v___x_1111_;
}
}
else
{
lean_dec_ref_known(v_a_1107_, 0);
v___y_1006_ = v___y_1087_;
v___y_1007_ = v___y_1082_;
v___y_1008_ = v___y_1080_;
v___y_1009_ = v___y_1086_;
v___y_1010_ = v_done_1104_;
v___y_1011_ = v___y_1079_;
v___y_1012_ = v___y_1083_;
v___y_1013_ = v___y_1085_;
v___y_1014_ = v___y_1081_;
v___y_1015_ = v_contextDependent_1105_;
v___y_1016_ = v___y_1084_;
v___y_1017_ = v___x_1106_;
goto v___jp_1005_;
}
}
else
{
uint8_t v_done_1116_; 
v_done_1116_ = lean_ctor_get_uint8(v_a_1107_, sizeof(void*)*2);
if (v_done_1116_ == 0)
{
lean_object* v_e_x27_1117_; lean_object* v_proof_1118_; uint8_t v_contextDependent_1119_; lean_object* v___x_1120_; 
lean_dec_ref_known(v___x_1106_, 1);
v_e_x27_1117_ = lean_ctor_get(v_a_1107_, 0);
lean_inc_ref_n(v_e_x27_1117_, 2);
v_proof_1118_ = lean_ctor_get(v_a_1107_, 1);
lean_inc_ref(v_proof_1118_);
v_contextDependent_1119_ = lean_ctor_get_uint8(v_a_1107_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1107_, 2);
v___x_1120_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1108_, v_e_x27_1117_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
if (lean_obj_tag(v_a_1121_) == 0)
{
if (v_contextDependent_1119_ == 0)
{
uint8_t v_done_1122_; uint8_t v_contextDependent_1123_; 
v_done_1122_ = lean_ctor_get_uint8(v_a_1121_, 0);
v_contextDependent_1123_ = lean_ctor_get_uint8(v_a_1121_, 1);
lean_dec_ref_known(v_a_1121_, 0);
v___y_1035_ = v_proof_1118_;
v___y_1036_ = v___y_1087_;
v___y_1037_ = v_done_1122_;
v___y_1038_ = v___y_1079_;
v___y_1039_ = v___y_1083_;
v___y_1040_ = v___y_1085_;
v___y_1041_ = v_contextDependent_1105_;
v___y_1042_ = v___y_1084_;
v___y_1043_ = v___y_1080_;
v___y_1044_ = v___y_1082_;
v___y_1045_ = v_e_x27_1117_;
v___y_1046_ = v___y_1086_;
v___y_1047_ = v_done_1104_;
v___y_1048_ = v___y_1081_;
v___y_1049_ = v_contextDependent_1123_;
goto v___jp_1034_;
}
else
{
uint8_t v_done_1124_; 
v_done_1124_ = lean_ctor_get_uint8(v_a_1121_, 0);
lean_dec_ref_known(v_a_1121_, 0);
v___y_1035_ = v_proof_1118_;
v___y_1036_ = v___y_1087_;
v___y_1037_ = v_done_1124_;
v___y_1038_ = v___y_1079_;
v___y_1039_ = v___y_1083_;
v___y_1040_ = v___y_1085_;
v___y_1041_ = v_contextDependent_1105_;
v___y_1042_ = v___y_1084_;
v___y_1043_ = v___y_1080_;
v___y_1044_ = v___y_1082_;
v___y_1045_ = v_e_x27_1117_;
v___y_1046_ = v___y_1086_;
v___y_1047_ = v_done_1104_;
v___y_1048_ = v___y_1081_;
v___y_1049_ = v_contextDependent_1119_;
goto v___jp_1034_;
}
}
else
{
lean_object* v_e_x27_1125_; lean_object* v_proof_1126_; uint8_t v_done_1127_; uint8_t v_contextDependent_1128_; lean_object* v___x_1129_; 
v_e_x27_1125_ = lean_ctor_get(v_a_1121_, 0);
lean_inc_ref_n(v_e_x27_1125_, 2);
v_proof_1126_ = lean_ctor_get(v_a_1121_, 1);
lean_inc_ref(v_proof_1126_);
v_done_1127_ = lean_ctor_get_uint8(v_a_1121_, sizeof(void*)*2);
v_contextDependent_1128_ = lean_ctor_get_uint8(v_a_1121_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1121_, 2);
lean_inc_ref(v_e_u2081_794_);
v___x_1129_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_794_, v_e_x27_1117_, v_proof_1118_, v_e_x27_1125_, v_proof_1126_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1129_) == 0)
{
if (v_contextDependent_1119_ == 0)
{
lean_object* v_a_1130_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___y_1052_ = v___y_1087_;
v___y_1053_ = v_a_1130_;
v___y_1054_ = v___y_1079_;
v___y_1055_ = v___y_1083_;
v___y_1056_ = v___y_1085_;
v___y_1057_ = v_contextDependent_1105_;
v___y_1058_ = v_done_1127_;
v___y_1059_ = v___y_1084_;
v___y_1060_ = v___y_1080_;
v___y_1061_ = v___y_1082_;
v___y_1062_ = v_e_x27_1125_;
v___y_1063_ = v___y_1086_;
v___y_1064_ = v_done_1104_;
v___y_1065_ = v___y_1081_;
v___y_1066_ = v_contextDependent_1128_;
goto v___jp_1051_;
}
else
{
lean_object* v_a_1131_; 
v_a_1131_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1129_, 1);
v___y_1052_ = v___y_1087_;
v___y_1053_ = v_a_1131_;
v___y_1054_ = v___y_1079_;
v___y_1055_ = v___y_1083_;
v___y_1056_ = v___y_1085_;
v___y_1057_ = v_contextDependent_1105_;
v___y_1058_ = v_done_1127_;
v___y_1059_ = v___y_1084_;
v___y_1060_ = v___y_1080_;
v___y_1061_ = v___y_1082_;
v___y_1062_ = v_e_x27_1125_;
v___y_1063_ = v___y_1086_;
v___y_1064_ = v_done_1104_;
v___y_1065_ = v___y_1081_;
v___y_1066_ = v_contextDependent_1119_;
goto v___jp_1051_;
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_e_x27_1125_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v_e_u2081_794_);
v_a_1132_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1129_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1129_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1118_);
lean_dec_ref(v_e_x27_1117_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v_e_u2081_794_);
return v___x_1120_;
}
}
else
{
lean_dec_ref_known(v_a_1107_, 2);
v___y_1006_ = v___y_1087_;
v___y_1007_ = v___y_1082_;
v___y_1008_ = v___y_1080_;
v___y_1009_ = v___y_1086_;
v___y_1010_ = v_done_1104_;
v___y_1011_ = v___y_1079_;
v___y_1012_ = v___y_1083_;
v___y_1013_ = v___y_1085_;
v___y_1014_ = v___y_1081_;
v___y_1015_ = v_contextDependent_1105_;
v___y_1016_ = v___y_1084_;
v___y_1017_ = v___x_1106_;
goto v___jp_1005_;
}
}
}
else
{
v___y_1006_ = v___y_1087_;
v___y_1007_ = v___y_1082_;
v___y_1008_ = v___y_1080_;
v___y_1009_ = v___y_1086_;
v___y_1010_ = v_done_1104_;
v___y_1011_ = v___y_1079_;
v___y_1012_ = v___y_1083_;
v___y_1013_ = v___y_1085_;
v___y_1014_ = v___y_1081_;
v___y_1015_ = v_contextDependent_1105_;
v___y_1016_ = v___y_1084_;
v___y_1017_ = v___x_1106_;
goto v___jp_1005_;
}
}
else
{
uint8_t v_contextDependent_1140_; 
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
v_contextDependent_1140_ = lean_ctor_get_uint8(v_a_1100_, 1);
if (v_contextDependent_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v_numSteps_1142_; lean_object* v_persistentCache_1143_; lean_object* v_transientCache_1144_; lean_object* v_funext_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1157_; 
v___x_1141_ = lean_st_ref_take(v___y_1081_);
v_numSteps_1142_ = lean_ctor_get(v___x_1141_, 0);
v_persistentCache_1143_ = lean_ctor_get(v___x_1141_, 1);
v_transientCache_1144_ = lean_ctor_get(v___x_1141_, 2);
v_funext_1145_ = lean_ctor_get(v___x_1141_, 3);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1147_ = v___x_1141_;
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_funext_1145_);
lean_inc(v_transientCache_1144_);
lean_inc(v_persistentCache_1143_);
lean_inc(v_numSteps_1142_);
lean_dec(v___x_1141_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_inc_ref(v_a_1100_);
v___x_1149_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1143_, v_e_u2081_794_, v_a_1100_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_numSteps_1142_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_transientCache_1144_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_funext_1145_);
v___x_1151_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_st_ref_put(v___y_1081_, v___x_1151_);
lean_dec(v___y_1081_);
if (v_isShared_1103_ == 0)
{
v___x_1154_ = v___x_1102_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1100_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v_numSteps_1159_; lean_object* v_persistentCache_1160_; lean_object* v_transientCache_1161_; lean_object* v_funext_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1174_; 
v___x_1158_ = lean_st_ref_take(v___y_1081_);
v_numSteps_1159_ = lean_ctor_get(v___x_1158_, 0);
v_persistentCache_1160_ = lean_ctor_get(v___x_1158_, 1);
v_transientCache_1161_ = lean_ctor_get(v___x_1158_, 2);
v_funext_1162_ = lean_ctor_get(v___x_1158_, 3);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1164_ = v___x_1158_;
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_funext_1162_);
lean_inc(v_transientCache_1161_);
lean_inc(v_persistentCache_1160_);
lean_inc(v_numSteps_1159_);
lean_dec(v___x_1158_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_inc_ref(v_a_1100_);
v___x_1166_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1161_, v_e_u2081_794_, v_a_1100_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 2, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_numSteps_1159_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_persistentCache_1160_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_funext_1162_);
v___x_1168_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_st_ref_put(v___y_1081_, v___x_1168_);
lean_dec(v___y_1081_);
if (v_isShared_1103_ == 0)
{
v___x_1171_ = v___x_1102_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1100_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
else
{
uint8_t v_done_1175_; 
v_done_1175_ = lean_ctor_get_uint8(v_a_1100_, sizeof(void*)*2);
if (v_done_1175_ == 0)
{
lean_object* v_e_x27_1176_; lean_object* v_proof_1177_; uint8_t v_contextDependent_1178_; 
lean_del_object(v___x_1102_);
v_e_x27_1176_ = lean_ctor_get(v_a_1100_, 0);
lean_inc_ref(v_e_x27_1176_);
v_proof_1177_ = lean_ctor_get(v_a_1100_, 1);
lean_inc_ref(v_proof_1177_);
v_contextDependent_1178_ = lean_ctor_get_uint8(v_a_1100_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1100_, 2);
v_e_u2082_854_ = v_e_x27_1176_;
v_h_u2081_855_ = v_proof_1177_;
v_cd_u2081_856_ = v_contextDependent_1178_;
v___y_857_ = v___y_1079_;
v___y_858_ = v___y_1080_;
v___y_859_ = v___y_1081_;
v___y_860_ = v___y_1082_;
v___y_861_ = v___y_1083_;
v___y_862_ = v___y_1084_;
v___y_863_ = v___y_1085_;
v___y_864_ = v___y_1086_;
v___y_865_ = v___y_1087_;
goto v___jp_853_;
}
else
{
uint8_t v_contextDependent_1179_; 
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
v_contextDependent_1179_ = lean_ctor_get_uint8(v_a_1100_, sizeof(void*)*2 + 1);
if (v_contextDependent_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v_numSteps_1181_; lean_object* v_persistentCache_1182_; lean_object* v_transientCache_1183_; lean_object* v_funext_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1196_; 
v___x_1180_ = lean_st_ref_take(v___y_1081_);
v_numSteps_1181_ = lean_ctor_get(v___x_1180_, 0);
v_persistentCache_1182_ = lean_ctor_get(v___x_1180_, 1);
v_transientCache_1183_ = lean_ctor_get(v___x_1180_, 2);
v_funext_1184_ = lean_ctor_get(v___x_1180_, 3);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1186_ = v___x_1180_;
v_isShared_1187_ = v_isSharedCheck_1196_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_funext_1184_);
lean_inc(v_transientCache_1183_);
lean_inc(v_persistentCache_1182_);
lean_inc(v_numSteps_1181_);
lean_dec(v___x_1180_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1196_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_inc_ref(v_a_1100_);
v___x_1188_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1182_, v_e_u2081_794_, v_a_1100_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1188_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_numSteps_1181_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_transientCache_1183_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_funext_1184_);
v___x_1190_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_st_ref_put(v___y_1081_, v___x_1190_);
lean_dec(v___y_1081_);
if (v_isShared_1103_ == 0)
{
v___x_1193_ = v___x_1102_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1100_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v___x_1197_; lean_object* v_numSteps_1198_; lean_object* v_persistentCache_1199_; lean_object* v_transientCache_1200_; lean_object* v_funext_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1213_; 
v___x_1197_ = lean_st_ref_take(v___y_1081_);
v_numSteps_1198_ = lean_ctor_get(v___x_1197_, 0);
v_persistentCache_1199_ = lean_ctor_get(v___x_1197_, 1);
v_transientCache_1200_ = lean_ctor_get(v___x_1197_, 2);
v_funext_1201_ = lean_ctor_get(v___x_1197_, 3);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1203_ = v___x_1197_;
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_funext_1201_);
lean_inc(v_transientCache_1200_);
lean_inc(v_persistentCache_1199_);
lean_inc(v_numSteps_1198_);
lean_dec(v___x_1197_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
lean_inc_ref(v_a_1100_);
v___x_1205_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1200_, v_e_u2081_794_, v_a_1100_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 2, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_numSteps_1198_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_persistentCache_1199_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_funext_1201_);
v___x_1207_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = lean_st_ref_put(v___y_1081_, v___x_1207_);
lean_dec(v___y_1081_);
if (v_isShared_1103_ == 0)
{
v___x_1210_ = v___x_1102_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1100_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
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
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v_e_u2081_794_);
return v___x_1099_;
}
}
}
}
v___jp_1218_:
{
lean_object* v___x_1230_; lean_object* v_persistentCache_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_st_ref_get(v___y_1223_);
v_persistentCache_1231_ = lean_ctor_get(v___x_1230_, 1);
lean_inc_ref(v_persistentCache_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_persistentCache_1231_, v_e_u2081_794_);
lean_dec_ref(v_persistentCache_1231_);
if (lean_obj_tag(v___x_1232_) == 1)
{
lean_object* v_toCold_1233_; lean_object* v_options_1234_; uint8_t v_hasTrace_1235_; 
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v___y_1219_);
v_toCold_1233_ = lean_ctor_get(v___y_1228_, 0);
v_options_1234_ = lean_ctor_get(v_toCold_1233_, 2);
v_hasTrace_1235_ = lean_ctor_get_uint8(v_options_1234_, sizeof(void*)*1);
if (v_hasTrace_1235_ == 0)
{
lean_object* v_val_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v_e_u2081_794_);
v_val_1236_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1232_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_val_1236_);
lean_dec(v___x_1232_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 0);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_val_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v_val_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1275_; 
v_val_1244_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1246_ = v___x_1232_;
v_isShared_1247_ = v_isSharedCheck_1275_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_val_1244_);
lean_dec(v___x_1232_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1275_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_inheritedTraceOptions_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_inheritedTraceOptions_1248_ = lean_ctor_get(v_toCold_1233_, 11);
v___x_1249_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1250_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1251_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1248_, v_options_1234_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v_e_u2081_794_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 0);
v___x_1253_ = v___x_1246_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_val_1244_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_del_object(v___x_1246_);
v___x_1255_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4);
v___x_1256_ = l_Lean_MessageData_ofExpr(v_e_u2081_794_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1249_, v___x_1257_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1266_);
v___x_1260_ = v___x_1258_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v___x_1258_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_val_1244_);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_val_1244_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_val_1244_);
v_a_1267_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1258_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1258_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v_transientCache_1277_; lean_object* v___x_1278_; 
lean_dec(v___x_1232_);
v___x_1276_ = lean_st_ref_get(v___y_1223_);
v_transientCache_1277_ = lean_ctor_get(v___x_1276_, 2);
lean_inc_ref(v_transientCache_1277_);
lean_dec(v___x_1276_);
v___x_1278_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_transientCache_1277_, v_e_u2081_794_);
lean_dec_ref(v_transientCache_1277_);
if (lean_obj_tag(v___x_1278_) == 1)
{
lean_object* v_toCold_1279_; lean_object* v_options_1280_; uint8_t v_hasTrace_1281_; 
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v___y_1219_);
v_toCold_1279_ = lean_ctor_get(v___y_1228_, 0);
v_options_1280_ = lean_ctor_get(v_toCold_1279_, 2);
v_hasTrace_1281_ = lean_ctor_get_uint8(v_options_1280_, sizeof(void*)*1);
if (v_hasTrace_1281_ == 0)
{
lean_object* v_val_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v_e_u2081_794_);
v_val_1282_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1278_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_val_1282_);
lean_dec(v___x_1278_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 0);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_val_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_object* v_val_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1321_; 
v_val_1290_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1292_ = v___x_1278_;
v_isShared_1293_ = v_isSharedCheck_1321_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_val_1290_);
lean_dec(v___x_1278_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1321_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_inheritedTraceOptions_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_inheritedTraceOptions_1294_ = lean_ctor_get(v_toCold_1279_, 11);
v___x_1295_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1296_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1297_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1294_, v_options_1280_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1299_; 
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v_e_u2081_794_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set_tag(v___x_1292_, 0);
v___x_1299_ = v___x_1292_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_val_1290_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_del_object(v___x_1292_);
v___x_1301_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6);
v___x_1302_ = l_Lean_MessageData_ofExpr(v_e_u2081_794_);
v___x_1303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1295_, v___x_1303_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v___x_1304_, 0);
lean_dec(v_unused_1312_);
v___x_1306_ = v___x_1304_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v___x_1304_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v_val_1290_);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_val_1290_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_val_1290_);
v_a_1313_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1304_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1304_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
lean_dec(v___x_1278_);
v___x_1322_ = lean_nat_add(v___y_1219_, v___y_1220_);
lean_dec(v___y_1219_);
v___x_1323_ = lean_unsigned_to_nat(1000u);
v___x_1324_ = lean_nat_mod(v___x_1322_, v___x_1323_);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_nat_dec_eq(v___x_1324_, v___x_1325_);
lean_dec(v___x_1324_);
if (v___x_1326_ == 0)
{
v___y_1078_ = v___x_1322_;
v___y_1079_ = v___y_1221_;
v___y_1080_ = v___y_1222_;
v___y_1081_ = v___y_1223_;
v___y_1082_ = v___y_1224_;
v___y_1083_ = v___y_1225_;
v___y_1084_ = v___y_1226_;
v___y_1085_ = v___y_1227_;
v___y_1086_ = v___y_1228_;
v___y_1087_ = v___y_1229_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1328_ = l_Lean_Core_checkSystem(v___x_1327_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_dec_ref_known(v___x_1328_, 1);
v___y_1078_ = v___x_1322_;
v___y_1079_ = v___y_1221_;
v___y_1080_ = v___y_1222_;
v___y_1081_ = v___y_1223_;
v___y_1082_ = v___y_1224_;
v___y_1083_ = v___y_1225_;
v___y_1084_ = v___y_1226_;
v___y_1085_ = v___y_1227_;
v___y_1086_ = v___y_1228_;
v___y_1087_ = v___y_1229_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v___x_1322_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v_e_u2081_794_);
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
}
v___jp_1337_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_st_ref_get(v_a_797_);
v___x_1339_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_796_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v_numSteps_1341_; lean_object* v_maxSteps_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
v_numSteps_1341_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_numSteps_1341_);
lean_dec(v___x_1338_);
v_maxSteps_1342_ = lean_ctor_get(v_a_1340_, 0);
lean_inc(v_maxSteps_1342_);
lean_dec(v_a_1340_);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_nat_add(v_currRecDepth_1069_, v___x_1343_);
lean_dec(v_currRecDepth_1069_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v___x_1344_);
v___x_1346_ = v___x_1074_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_toCold_1068_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_ref_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*3, v_diag_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*3 + 1, v_suppressElabErrors_1072_);
v___x_1346_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_le(v_maxSteps_1342_, v_numSteps_1341_);
lean_dec(v_maxSteps_1342_);
if (v___x_1347_ == 0)
{
v___y_1219_ = v_numSteps_1341_;
v___y_1220_ = v___x_1343_;
v___y_1221_ = v_a_795_;
v___y_1222_ = v_a_796_;
v___y_1223_ = v_a_797_;
v___y_1224_ = v_a_798_;
v___y_1225_ = v_a_799_;
v___y_1226_ = v_a_800_;
v___y_1227_ = v_a_801_;
v___y_1228_ = v___x_1346_;
v___y_1229_ = v_a_803_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_numSteps_1341_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_e_u2081_794_);
v___x_1348_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8);
v___x_1349_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_1348_, v_a_800_, v_a_801_, v___x_1346_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v___x_1346_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v___x_1338_);
lean_del_object(v___x_1074_);
lean_dec(v_ref_1070_);
lean_dec(v_currRecDepth_1069_);
lean_dec_ref(v_toCold_1068_);
lean_dec(v_a_803_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_e_u2081_794_);
v_a_1359_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1339_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1339_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* v_e_u2081_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = lean_sym_simp(v_e_u2081_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* v_00_u03b2_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_1385_, v_x_1386_, v_x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* v_00_u03b2_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_1390_, v_x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* v_00_u03b2_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_1393_, v_x_1394_, v_x_1395_);
lean_dec_ref(v_x_1395_);
lean_dec_ref(v_x_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* v_cls_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_1397_, v_msg_1398_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* v_cls_1410_, lean_object* v_msg_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_1410_, v_msg_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, size_t v_x_1425_, size_t v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_1424_, v_x_1425_, v_x_1426_, v_x_1427_, v_x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
size_t v_x_111293__boxed_1436_; size_t v_x_111294__boxed_1437_; lean_object* v_res_1438_; 
v_x_111293__boxed_1436_ = lean_unbox_usize(v_x_1432_);
lean_dec(v_x_1432_);
v_x_111294__boxed_1437_ = lean_unbox_usize(v_x_1433_);
lean_dec(v_x_1433_);
v_res_1438_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_1430_, v_x_1431_, v_x_111293__boxed_1436_, v_x_111294__boxed_1437_, v_x_1434_, v_x_1435_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* v_00_u03b2_1439_, lean_object* v_x_1440_, size_t v_x_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_1440_, v_x_1441_, v_x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
size_t v_x_111310__boxed_1448_; lean_object* v_res_1449_; 
v_x_111310__boxed_1448_ = lean_unbox_usize(v_x_1446_);
lean_dec(v_x_1446_);
v_res_1449_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_1444_, v_x_1445_, v_x_111310__boxed_1448_, v_x_1447_);
lean_dec_ref(v_x_1447_);
lean_dec_ref(v_x_1445_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1450_, lean_object* v_n_1451_, lean_object* v_k_1452_, lean_object* v_v_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v_n_1451_, v_k_1452_, v_v_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1455_, size_t v_depth_1456_, lean_object* v_keys_1457_, lean_object* v_vals_1458_, lean_object* v_heq_1459_, lean_object* v_i_1460_, lean_object* v_entries_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_1456_, v_keys_1457_, v_vals_1458_, v_i_1460_, v_entries_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1463_, lean_object* v_depth_1464_, lean_object* v_keys_1465_, lean_object* v_vals_1466_, lean_object* v_heq_1467_, lean_object* v_i_1468_, lean_object* v_entries_1469_){
_start:
{
size_t v_depth_boxed_1470_; lean_object* v_res_1471_; 
v_depth_boxed_1470_ = lean_unbox_usize(v_depth_1464_);
lean_dec(v_depth_1464_);
v_res_1471_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(v_00_u03b2_1463_, v_depth_boxed_1470_, v_keys_1465_, v_vals_1466_, v_heq_1467_, v_i_1468_, v_entries_1469_);
lean_dec_ref(v_vals_1466_);
lean_dec_ref(v_keys_1465_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1472_, lean_object* v_keys_1473_, lean_object* v_vals_1474_, lean_object* v_heq_1475_, lean_object* v_i_1476_, lean_object* v_k_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1473_, v_vals_1474_, v_i_1476_, v_k_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1479_, lean_object* v_keys_1480_, lean_object* v_vals_1481_, lean_object* v_heq_1482_, lean_object* v_i_1483_, lean_object* v_k_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(v_00_u03b2_1479_, v_keys_1480_, v_vals_1481_, v_heq_1482_, v_i_1483_, v_k_1484_);
lean_dec_ref(v_k_1484_);
lean_dec_ref(v_vals_1481_);
lean_dec_ref(v_keys_1480_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1487_, v_x_1488_, v_x_1489_, v_x_1490_);
return v___x_1491_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Main(builtin);
}
#ifdef __cplusplus
}
#endif
