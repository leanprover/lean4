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
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
v_debug_107_ = lean_ctor_get_uint8(v___x_106_, sizeof(void*)*10);
lean_dec(v___x_106_);
if (v_debug_107_ == 0)
{
v___y_103_ = v___y_96_;
goto v___jp_102_;
}
else
{
lean_object* v___x_108_; 
lean_inc_ref(v_e_94_);
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
lean_object* v___x_159_; lean_object* v_env_160_; lean_object* v___x_161_; lean_object* v_mctx_162_; lean_object* v_lctx_163_; lean_object* v_options_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_159_ = lean_st_ref_get(v___y_157_);
v_env_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc_ref(v_env_160_);
lean_dec(v___x_159_);
v___x_161_ = lean_st_ref_get(v___y_155_);
v_mctx_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_mctx_162_);
lean_dec(v___x_161_);
v_lctx_163_ = lean_ctor_get(v___y_154_, 2);
v_options_164_ = lean_ctor_get(v___y_156_, 2);
lean_inc_ref(v_options_164_);
lean_inc_ref(v_lctx_163_);
v___x_165_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_165_, 0, v_env_160_);
lean_ctor_set(v___x_165_, 1, v_mctx_162_);
lean_ctor_set(v___x_165_, 2, v_lctx_163_);
lean_ctor_set(v___x_165_, 3, v_options_164_);
v___x_166_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v_msgData_153_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object* v_msgData_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msgData_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_ref_181_; lean_object* v___x_182_; lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_ref_181_ = lean_ctor_get(v___y_178_, 5);
v___x_182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_inc(v_ref_181_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v_ref_181_);
lean_ctor_set(v___x_187_, 1, v_a_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 1);
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_201_ = l_Lean_stringToMessageData(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object* v_e_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
switch(lean_obj_tag(v_e_207_))
{
case 5:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_218_;
}
case 6:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_219_;
}
case 7:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_220_;
}
case 8:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_221_;
}
case 10:
{
lean_object* v_data_222_; lean_object* v_expr_223_; lean_object* v___x_224_; 
v_data_222_ = lean_ctor_get(v_e_207_, 0);
lean_inc(v_data_222_);
v_expr_223_ = lean_ctor_get(v_e_207_, 1);
lean_inc_ref(v_expr_223_);
lean_dec_ref_known(v_e_207_, 2);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
v___x_224_ = lean_sym_simp(v_expr_223_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_262_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_262_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_262_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_262_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
if (lean_obj_tag(v_a_225_) == 0)
{
uint8_t v_contextDependent_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
lean_dec(v_data_222_);
v_contextDependent_229_ = lean_ctor_get_uint8(v_a_225_, 1);
lean_dec_ref_known(v_a_225_, 0);
v___x_230_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_229_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_230_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
else
{
lean_object* v_e_x27_234_; lean_object* v_proof_235_; uint8_t v_contextDependent_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_261_; 
lean_del_object(v___x_227_);
v_e_x27_234_ = lean_ctor_get(v_a_225_, 0);
v_proof_235_ = lean_ctor_get(v_a_225_, 1);
v_contextDependent_236_ = lean_ctor_get_uint8(v_a_225_, sizeof(void*)*2 + 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_a_225_);
if (v_isSharedCheck_261_ == 0)
{
v___x_238_ = v_a_225_;
v_isShared_239_ = v_isSharedCheck_261_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_proof_235_);
lean_inc(v_e_x27_234_);
lean_dec(v_a_225_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_261_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_data_222_, v_e_x27_234_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_252_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_252_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_252_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_252_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
uint8_t v___x_245_; lean_object* v___x_247_; 
v___x_245_ = 0;
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v_a_241_);
v___x_247_ = v___x_238_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_241_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_proof_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*2 + 1, v_contextDependent_236_);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_249_; 
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*2, v___x_245_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_247_);
v___x_249_ = v___x_243_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_del_object(v___x_238_);
lean_dec_ref(v_proof_235_);
v_a_253_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_240_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_240_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
}
else
{
lean_dec(v_data_222_);
return v___x_224_;
}
}
case 11:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_263_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1);
v___x_264_ = l_Lean_indentExpr(v_e_207_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_267_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_268_;
}
default: 
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref(v_e_207_);
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4));
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object* v_e_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object* v_00_u03b1_283_, lean_object* v_msg_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_284_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object* v_00_u03b1_296_, lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(v_00_u03b1_296_, v_msg_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object* v_e_311_, lean_object* v_r_312_, lean_object* v_a_313_){
_start:
{
uint8_t v___y_316_; 
if (lean_obj_tag(v_r_312_) == 0)
{
uint8_t v_contextDependent_351_; 
v_contextDependent_351_ = lean_ctor_get_uint8(v_r_312_, 1);
v___y_316_ = v_contextDependent_351_;
goto v___jp_315_;
}
else
{
uint8_t v_contextDependent_352_; 
v_contextDependent_352_ = lean_ctor_get_uint8(v_r_312_, sizeof(void*)*2 + 1);
v___y_316_ = v_contextDependent_352_;
goto v___jp_315_;
}
v___jp_315_:
{
if (v___y_316_ == 0)
{
lean_object* v___x_317_; lean_object* v_numSteps_318_; lean_object* v_persistentCache_319_; lean_object* v_transientCache_320_; lean_object* v_funext_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_333_; 
v___x_317_ = lean_st_ref_take(v_a_313_);
v_numSteps_318_ = lean_ctor_get(v___x_317_, 0);
v_persistentCache_319_ = lean_ctor_get(v___x_317_, 1);
v_transientCache_320_ = lean_ctor_get(v___x_317_, 2);
v_funext_321_ = lean_ctor_get(v___x_317_, 3);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_333_ == 0)
{
v___x_323_ = v___x_317_;
v_isShared_324_ = v_isSharedCheck_333_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_funext_321_);
lean_inc(v_transientCache_320_);
lean_inc(v_persistentCache_319_);
lean_inc(v_numSteps_318_);
lean_dec(v___x_317_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_333_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___f_325_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_326_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_312_);
v___x_327_ = l_Lean_PersistentHashMap_insert___redArg(v___f_325_, v___f_326_, v_persistentCache_319_, v_e_311_, v_r_312_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_327_);
v___x_329_ = v___x_323_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_numSteps_318_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_transientCache_320_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_funext_321_);
v___x_329_ = v_reuseFailAlloc_332_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_st_ref_set(v_a_313_, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_r_312_);
return v___x_331_;
}
}
}
else
{
lean_object* v___x_334_; lean_object* v_numSteps_335_; lean_object* v_persistentCache_336_; lean_object* v_transientCache_337_; lean_object* v_funext_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_350_; 
v___x_334_ = lean_st_ref_take(v_a_313_);
v_numSteps_335_ = lean_ctor_get(v___x_334_, 0);
v_persistentCache_336_ = lean_ctor_get(v___x_334_, 1);
v_transientCache_337_ = lean_ctor_get(v___x_334_, 2);
v_funext_338_ = lean_ctor_get(v___x_334_, 3);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_350_ == 0)
{
v___x_340_ = v___x_334_;
v_isShared_341_ = v_isSharedCheck_350_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_funext_338_);
lean_inc(v_transientCache_337_);
lean_inc(v_persistentCache_336_);
lean_inc(v_numSteps_335_);
lean_dec(v___x_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_350_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___f_342_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_343_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_312_);
v___x_344_ = l_Lean_PersistentHashMap_insert___redArg(v___f_342_, v___f_343_, v_transientCache_337_, v_e_311_, v_r_312_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 2, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_numSteps_335_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_persistentCache_336_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_funext_338_);
v___x_346_ = v_reuseFailAlloc_349_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_st_ref_set(v_a_313_, v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_r_312_);
return v___x_348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object* v_e_353_, lean_object* v_r_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(v_e_353_, v_r_354_, v_a_355_);
lean_dec(v_a_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(lean_object* v_e_358_, lean_object* v_r_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
uint8_t v___y_371_; 
if (lean_obj_tag(v_r_359_) == 0)
{
uint8_t v_contextDependent_406_; 
v_contextDependent_406_ = lean_ctor_get_uint8(v_r_359_, 1);
v___y_371_ = v_contextDependent_406_;
goto v___jp_370_;
}
else
{
uint8_t v_contextDependent_407_; 
v_contextDependent_407_ = lean_ctor_get_uint8(v_r_359_, sizeof(void*)*2 + 1);
v___y_371_ = v_contextDependent_407_;
goto v___jp_370_;
}
v___jp_370_:
{
if (v___y_371_ == 0)
{
lean_object* v___x_372_; lean_object* v_numSteps_373_; lean_object* v_persistentCache_374_; lean_object* v_transientCache_375_; lean_object* v_funext_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_388_; 
v___x_372_ = lean_st_ref_take(v_a_362_);
v_numSteps_373_ = lean_ctor_get(v___x_372_, 0);
v_persistentCache_374_ = lean_ctor_get(v___x_372_, 1);
v_transientCache_375_ = lean_ctor_get(v___x_372_, 2);
v_funext_376_ = lean_ctor_get(v___x_372_, 3);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_388_ == 0)
{
v___x_378_ = v___x_372_;
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_funext_376_);
lean_inc(v_transientCache_375_);
lean_inc(v_persistentCache_374_);
lean_inc(v_numSteps_373_);
lean_dec(v___x_372_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___f_380_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_381_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_359_);
v___x_382_ = l_Lean_PersistentHashMap_insert___redArg(v___f_380_, v___f_381_, v_persistentCache_374_, v_e_358_, v_r_359_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_382_);
v___x_384_ = v___x_378_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_numSteps_373_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_transientCache_375_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v_funext_376_);
v___x_384_ = v_reuseFailAlloc_387_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_st_ref_set(v_a_362_, v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_r_359_);
return v___x_386_;
}
}
}
else
{
lean_object* v___x_389_; lean_object* v_numSteps_390_; lean_object* v_persistentCache_391_; lean_object* v_transientCache_392_; lean_object* v_funext_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_405_; 
v___x_389_ = lean_st_ref_take(v_a_362_);
v_numSteps_390_ = lean_ctor_get(v___x_389_, 0);
v_persistentCache_391_ = lean_ctor_get(v___x_389_, 1);
v_transientCache_392_ = lean_ctor_get(v___x_389_, 2);
v_funext_393_ = lean_ctor_get(v___x_389_, 3);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_405_ == 0)
{
v___x_395_ = v___x_389_;
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_funext_393_);
lean_inc(v_transientCache_392_);
lean_inc(v_persistentCache_391_);
lean_inc(v_numSteps_390_);
lean_dec(v___x_389_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___f_397_; lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___f_397_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_398_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_359_);
v___x_399_ = l_Lean_PersistentHashMap_insert___redArg(v___f_397_, v___f_398_, v_transientCache_392_, v_e_358_, v_r_359_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 2, v___x_399_);
v___x_401_ = v___x_395_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_numSteps_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_persistentCache_391_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_funext_393_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_st_ref_set(v_a_362_, v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v_r_359_);
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object* v_e_408_, lean_object* v_r_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(v_e_408_, v_r_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
return v_res_420_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_Lean_maxRecDepthErrorMessage;
v___x_427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3);
v___x_429_ = l_Lean_MessageData_ofFormat(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4);
v___x_431_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2));
v___x_432_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(lean_object* v_ref_433_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_ref_433_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(lean_object* v_ref_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_object* v_00_u03b1_441_, lean_object* v_ref_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_442_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(lean_object* v_00_u03b1_454_, lean_object* v_ref_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(v_00_u03b1_454_, v_ref_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object* v_x_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_post_479_; lean_object* v___x_480_; 
v_post_479_ = lean_ctor_get(v___y_469_, 1);
lean_inc_ref(v_post_479_);
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
v___x_480_ = lean_apply_11(v_post_479_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, lean_box(0));
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object* v_x_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v_x_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
lean_object* v_ks_498_; lean_object* v_vs_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_523_; 
v_ks_498_ = lean_ctor_get(v_x_494_, 0);
v_vs_499_ = lean_ctor_get(v_x_494_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_494_);
if (v_isSharedCheck_523_ == 0)
{
v___x_501_ = v_x_494_;
v_isShared_502_ = v_isSharedCheck_523_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_vs_499_);
lean_inc(v_ks_498_);
lean_dec(v_x_494_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_523_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_array_get_size(v_ks_498_);
v___x_504_ = lean_nat_dec_lt(v_x_495_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec(v_x_495_);
v___x_505_ = lean_array_push(v_ks_498_, v_x_496_);
v___x_506_ = lean_array_push(v_vs_499_, v_x_497_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_506_);
lean_ctor_set(v___x_501_, 0, v___x_505_);
v___x_508_ = v___x_501_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
else
{
lean_object* v_k_x27_510_; uint8_t v___x_511_; 
v_k_x27_510_ = lean_array_fget_borrowed(v_ks_498_, v_x_495_);
v___x_511_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_496_, v_k_x27_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_513_; 
if (v_isShared_502_ == 0)
{
v___x_513_ = v___x_501_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_ks_498_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_vs_499_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_x_495_, v___x_514_);
lean_dec(v_x_495_);
v_x_494_ = v___x_513_;
v_x_495_ = v___x_515_;
goto _start;
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_518_ = lean_array_fset(v_ks_498_, v_x_495_, v_x_496_);
v___x_519_ = lean_array_fset(v_vs_499_, v_x_495_, v_x_497_);
lean_dec(v_x_495_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_519_);
lean_ctor_set(v___x_501_, 0, v___x_518_);
v___x_521_ = v___x_501_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_524_, lean_object* v_k_525_, lean_object* v_v_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_n_524_, v___x_527_, v_k_525_, v_v_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* v_x_530_, size_t v_x_531_, size_t v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_530_) == 0)
{
lean_object* v_es_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v_j_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_es_535_ = lean_ctor_get(v_x_530_, 0);
v___x_536_ = ((size_t)31ULL);
v___x_537_ = lean_usize_land(v_x_531_, v___x_536_);
v_j_538_ = lean_usize_to_nat(v___x_537_);
v___x_539_ = lean_array_get_size(v_es_535_);
v___x_540_ = lean_nat_dec_lt(v_j_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_dec(v_j_538_);
lean_dec(v_x_534_);
lean_dec_ref(v_x_533_);
return v_x_530_;
}
else
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_579_; 
lean_inc_ref(v_es_535_);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_530_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v_x_530_, 0);
lean_dec(v_unused_580_);
v___x_542_ = v_x_530_;
v_isShared_543_ = v_isSharedCheck_579_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_x_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_579_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_v_544_; lean_object* v___x_545_; lean_object* v_xs_x27_546_; lean_object* v___y_548_; 
v_v_544_ = lean_array_fget(v_es_535_, v_j_538_);
v___x_545_ = lean_box(0);
v_xs_x27_546_ = lean_array_fset(v_es_535_, v_j_538_, v___x_545_);
switch(lean_obj_tag(v_v_544_))
{
case 0:
{
lean_object* v_key_553_; lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_564_; 
v_key_553_ = lean_ctor_get(v_v_544_, 0);
v_val_554_ = lean_ctor_get(v_v_544_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_v_544_);
if (v_isSharedCheck_564_ == 0)
{
v___x_556_ = v_v_544_;
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_inc(v_key_553_);
lean_dec(v_v_544_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
uint8_t v___x_558_; 
v___x_558_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_533_, v_key_553_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_del_object(v___x_556_);
v___x_559_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_553_, v_val_554_, v_x_533_, v_x_534_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
v___y_548_ = v___x_560_;
goto v___jp_547_;
}
else
{
lean_object* v___x_562_; 
lean_dec(v_val_554_);
lean_dec(v_key_553_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_x_534_);
lean_ctor_set(v___x_556_, 0, v_x_533_);
v___x_562_ = v___x_556_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_x_533_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_x_534_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v___y_548_ = v___x_562_;
goto v___jp_547_;
}
}
}
}
case 1:
{
lean_object* v_node_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_577_; 
v_node_565_ = lean_ctor_get(v_v_544_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_v_544_);
if (v_isSharedCheck_577_ == 0)
{
v___x_567_ = v_v_544_;
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_node_565_);
lean_dec(v_v_544_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_569_ = ((size_t)5ULL);
v___x_570_ = lean_usize_shift_right(v_x_531_, v___x_569_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_x_532_, v___x_571_);
v___x_573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_565_, v___x_570_, v___x_572_, v_x_533_, v_x_534_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_573_);
v___x_575_ = v___x_567_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
v___y_548_ = v___x_575_;
goto v___jp_547_;
}
}
}
default: 
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_x_533_);
lean_ctor_set(v___x_578_, 1, v_x_534_);
v___y_548_ = v___x_578_;
goto v___jp_547_;
}
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_array_fset(v_xs_x27_546_, v_j_538_, v___y_548_);
lean_dec(v_j_538_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_549_);
v___x_551_ = v___x_542_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
else
{
lean_object* v_ks_581_; lean_object* v_vs_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_602_; 
v_ks_581_ = lean_ctor_get(v_x_530_, 0);
v_vs_582_ = lean_ctor_get(v_x_530_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_x_530_);
if (v_isSharedCheck_602_ == 0)
{
v___x_584_ = v_x_530_;
v_isShared_585_ = v_isSharedCheck_602_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_vs_582_);
lean_inc(v_ks_581_);
lean_dec(v_x_530_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_602_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_ks_581_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_vs_582_);
v___x_587_ = v_reuseFailAlloc_601_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v_newNode_588_; uint8_t v___y_590_; size_t v___x_596_; uint8_t v___x_597_; 
v_newNode_588_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v___x_587_, v_x_533_, v_x_534_);
v___x_596_ = ((size_t)7ULL);
v___x_597_ = lean_usize_dec_le(v___x_596_, v_x_532_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_588_);
v___x_599_ = lean_unsigned_to_nat(4u);
v___x_600_ = lean_nat_dec_lt(v___x_598_, v___x_599_);
lean_dec(v___x_598_);
v___y_590_ = v___x_600_;
goto v___jp_589_;
}
else
{
v___y_590_ = v___x_597_;
goto v___jp_589_;
}
v___jp_589_:
{
if (v___y_590_ == 0)
{
lean_object* v_ks_591_; lean_object* v_vs_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_ks_591_ = lean_ctor_get(v_newNode_588_, 0);
lean_inc_ref(v_ks_591_);
v_vs_592_ = lean_ctor_get(v_newNode_588_, 1);
lean_inc_ref(v_vs_592_);
lean_dec_ref(v_newNode_588_);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
v___x_595_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_x_532_, v_ks_591_, v_vs_592_, v___x_593_, v___x_594_);
lean_dec_ref(v_vs_592_);
lean_dec_ref(v_ks_591_);
return v___x_595_;
}
else
{
return v_newNode_588_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_603_, lean_object* v_keys_604_, lean_object* v_vals_605_, lean_object* v_i_606_, lean_object* v_entries_607_){
_start:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_array_get_size(v_keys_604_);
v___x_609_ = lean_nat_dec_lt(v_i_606_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v_i_606_);
return v_entries_607_;
}
else
{
lean_object* v_k_610_; lean_object* v_v_611_; uint64_t v___x_612_; size_t v_h_613_; size_t v___x_614_; lean_object* v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; size_t v_h_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_k_610_ = lean_array_fget_borrowed(v_keys_604_, v_i_606_);
v_v_611_ = lean_array_fget_borrowed(v_vals_605_, v_i_606_);
v___x_612_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_610_);
v_h_613_ = lean_uint64_to_usize(v___x_612_);
v___x_614_ = ((size_t)5ULL);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_sub(v_depth_603_, v___x_616_);
v___x_618_ = lean_usize_mul(v___x_614_, v___x_617_);
v_h_619_ = lean_usize_shift_right(v_h_613_, v___x_618_);
v___x_620_ = lean_nat_add(v_i_606_, v___x_615_);
lean_dec(v_i_606_);
lean_inc(v_v_611_);
lean_inc(v_k_610_);
v___x_621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_607_, v_h_619_, v_depth_603_, v_k_610_, v_v_611_);
v_i_606_ = v___x_620_;
v_entries_607_ = v___x_621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_623_, lean_object* v_keys_624_, lean_object* v_vals_625_, lean_object* v_i_626_, lean_object* v_entries_627_){
_start:
{
size_t v_depth_boxed_628_; lean_object* v_res_629_; 
v_depth_boxed_628_ = lean_unbox_usize(v_depth_623_);
lean_dec(v_depth_623_);
v_res_629_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_628_, v_keys_624_, v_vals_625_, v_i_626_, v_entries_627_);
lean_dec_ref(v_vals_625_);
lean_dec_ref(v_keys_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
size_t v_x_114328__boxed_635_; size_t v_x_114329__boxed_636_; lean_object* v_res_637_; 
v_x_114328__boxed_635_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_x_114329__boxed_636_ = lean_unbox_usize(v_x_632_);
lean_dec(v_x_632_);
v_res_637_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_630_, v_x_114328__boxed_635_, v_x_114329__boxed_636_, v_x_633_, v_x_634_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
uint64_t v___x_641_; size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_641_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_639_);
v___x_642_ = lean_uint64_to_usize(v___x_641_);
v___x_643_ = ((size_t)1ULL);
v___x_644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_638_, v___x_642_, v___x_643_, v_x_639_, v_x_640_);
return v___x_644_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_645_; double v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_float_of_nat(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* v_cls_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_ref_657_; lean_object* v___x_658_; lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_703_; 
v_ref_657_ = lean_ctor_get(v___y_654_, 5);
v___x_658_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_703_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_703_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_703_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v_traceState_664_; lean_object* v_env_665_; lean_object* v_nextMacroScope_666_; lean_object* v_ngen_667_; lean_object* v_auxDeclNGen_668_; lean_object* v_cache_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_702_; 
v___x_663_ = lean_st_ref_take(v___y_655_);
v_traceState_664_ = lean_ctor_get(v___x_663_, 4);
v_env_665_ = lean_ctor_get(v___x_663_, 0);
v_nextMacroScope_666_ = lean_ctor_get(v___x_663_, 1);
v_ngen_667_ = lean_ctor_get(v___x_663_, 2);
v_auxDeclNGen_668_ = lean_ctor_get(v___x_663_, 3);
v_cache_669_ = lean_ctor_get(v___x_663_, 5);
v_messages_670_ = lean_ctor_get(v___x_663_, 6);
v_infoState_671_ = lean_ctor_get(v___x_663_, 7);
v_snapshotTasks_672_ = lean_ctor_get(v___x_663_, 8);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_702_ == 0)
{
v___x_674_ = v___x_663_;
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snapshotTasks_672_);
lean_inc(v_infoState_671_);
lean_inc(v_messages_670_);
lean_inc(v_cache_669_);
lean_inc(v_traceState_664_);
lean_inc(v_auxDeclNGen_668_);
lean_inc(v_ngen_667_);
lean_inc(v_nextMacroScope_666_);
lean_inc(v_env_665_);
lean_dec(v___x_663_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
uint64_t v_tid_676_; lean_object* v_traces_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_701_; 
v_tid_676_ = lean_ctor_get_uint64(v_traceState_664_, sizeof(void*)*1);
v_traces_677_ = lean_ctor_get(v_traceState_664_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_traceState_664_);
if (v_isSharedCheck_701_ == 0)
{
v___x_679_ = v_traceState_664_;
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_traces_677_);
lean_dec(v_traceState_664_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; double v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0);
v___x_683_ = 0;
v___x_684_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1));
v___x_685_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_685_, 0, v_cls_650_);
lean_ctor_set(v___x_685_, 1, v___x_681_);
lean_ctor_set(v___x_685_, 2, v___x_684_);
lean_ctor_set_float(v___x_685_, sizeof(void*)*3, v___x_682_);
lean_ctor_set_float(v___x_685_, sizeof(void*)*3 + 8, v___x_682_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*3 + 16, v___x_683_);
v___x_686_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2));
v___x_687_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v_a_659_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
lean_inc(v_ref_657_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_ref_657_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_PersistentArray_push___redArg(v_traces_677_, v___x_688_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_689_);
v___x_691_ = v___x_679_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_689_);
lean_ctor_set_uint64(v_reuseFailAlloc_700_, sizeof(void*)*1, v_tid_676_);
v___x_691_ = v_reuseFailAlloc_700_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 4, v___x_691_);
v___x_693_ = v___x_674_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_env_665_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_nextMacroScope_666_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_ngen_667_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_auxDeclNGen_668_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_699_, 5, v_cache_669_);
lean_ctor_set(v_reuseFailAlloc_699_, 6, v_messages_670_);
lean_ctor_set(v_reuseFailAlloc_699_, 7, v_infoState_671_);
lean_ctor_set(v_reuseFailAlloc_699_, 8, v_snapshotTasks_672_);
v___x_693_ = v_reuseFailAlloc_699_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = lean_st_ref_set(v___y_655_, v___x_693_);
v___x_695_ = lean_box(0);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_695_);
v___x_697_ = v___x_661_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* v_cls_704_, lean_object* v_msg_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_704_, v_msg_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_712_, lean_object* v_vals_713_, lean_object* v_i_714_, lean_object* v_k_715_){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_array_get_size(v_keys_712_);
v___x_717_ = lean_nat_dec_lt(v_i_714_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec(v_i_714_);
v___x_718_ = lean_box(0);
return v___x_718_;
}
else
{
lean_object* v_k_x27_719_; uint8_t v___x_720_; 
v_k_x27_719_ = lean_array_fget_borrowed(v_keys_712_, v_i_714_);
v___x_720_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_715_, v_k_x27_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_i_714_, v___x_721_);
lean_dec(v_i_714_);
v_i_714_ = v___x_722_;
goto _start;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_array_fget_borrowed(v_vals_713_, v_i_714_);
lean_dec(v_i_714_);
lean_inc(v___x_724_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_726_, lean_object* v_vals_727_, lean_object* v_i_728_, lean_object* v_k_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_726_, v_vals_727_, v_i_728_, v_k_729_);
lean_dec_ref(v_k_729_);
lean_dec_ref(v_vals_727_);
lean_dec_ref(v_keys_726_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* v_x_731_, size_t v_x_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_731_) == 0)
{
lean_object* v_es_734_; lean_object* v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v_j_738_; lean_object* v___x_739_; 
v_es_734_ = lean_ctor_get(v_x_731_, 0);
v___x_735_ = lean_box(2);
v___x_736_ = ((size_t)31ULL);
v___x_737_ = lean_usize_land(v_x_732_, v___x_736_);
v_j_738_ = lean_usize_to_nat(v___x_737_);
v___x_739_ = lean_array_get_borrowed(v___x_735_, v_es_734_, v_j_738_);
lean_dec(v_j_738_);
switch(lean_obj_tag(v___x_739_))
{
case 0:
{
lean_object* v_key_740_; lean_object* v_val_741_; uint8_t v___x_742_; 
v_key_740_ = lean_ctor_get(v___x_739_, 0);
v_val_741_ = lean_ctor_get(v___x_739_, 1);
v___x_742_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_733_, v_key_740_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
v___x_743_ = lean_box(0);
return v___x_743_;
}
else
{
lean_object* v___x_744_; 
lean_inc(v_val_741_);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_val_741_);
return v___x_744_;
}
}
case 1:
{
lean_object* v_node_745_; size_t v___x_746_; size_t v___x_747_; 
v_node_745_ = lean_ctor_get(v___x_739_, 0);
v___x_746_ = ((size_t)5ULL);
v___x_747_ = lean_usize_shift_right(v_x_732_, v___x_746_);
v_x_731_ = v_node_745_;
v_x_732_ = v___x_747_;
goto _start;
}
default: 
{
lean_object* v___x_749_; 
v___x_749_ = lean_box(0);
return v___x_749_;
}
}
}
else
{
lean_object* v_ks_750_; lean_object* v_vs_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_ks_750_ = lean_ctor_get(v_x_731_, 0);
v_vs_751_ = lean_ctor_get(v_x_731_, 1);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_ks_750_, v_vs_751_, v___x_752_, v_x_733_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
size_t v_x_114617__boxed_757_; lean_object* v_res_758_; 
v_x_114617__boxed_757_ = lean_unbox_usize(v_x_755_);
lean_dec(v_x_755_);
v_res_758_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_754_, v_x_114617__boxed_757_, v_x_756_);
lean_dec_ref(v_x_756_);
lean_dec_ref(v_x_754_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
uint64_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_760_);
v___x_762_ = lean_uint64_to_usize(v___x_761_);
v___x_763_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_759_, v___x_762_, v_x_760_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_764_, v_x_765_);
lean_dec_ref(v_x_765_);
lean_dec_ref(v_x_764_);
return v_res_766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1));
v___x_772_ = l_Lean_Name_append(v___x_771_, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* lean_sym_simp(lean_object* v_e_u2081_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___y_794_; lean_object* v___y_795_; uint8_t v___y_796_; uint8_t v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; uint8_t v___y_832_; lean_object* v___y_835_; lean_object* v___y_836_; uint8_t v___y_837_; lean_object* v___y_838_; uint8_t v___y_839_; lean_object* v_e_u2082_842_; lean_object* v_h_u2081_843_; uint8_t v_cd_u2081_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; uint8_t v___y_962_; uint8_t v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; uint8_t v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; uint8_t v___y_977_; uint8_t v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; uint8_t v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v_a_990_; lean_object* v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; uint8_t v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; uint8_t v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; uint8_t v___y_1020_; uint8_t v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; uint8_t v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; uint8_t v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; uint8_t v___y_1037_; uint8_t v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; uint8_t v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; uint8_t v___y_1053_; uint8_t v___y_1054_; lean_object* v_fileName_1056_; lean_object* v_fileMap_1057_; lean_object* v_options_1058_; lean_object* v_currRecDepth_1059_; lean_object* v_maxRecDepth_1060_; lean_object* v_ref_1061_; lean_object* v_currNamespace_1062_; lean_object* v_openDecls_1063_; lean_object* v_initHeartbeats_1064_; lean_object* v_maxHeartbeats_1065_; lean_object* v_quotContext_1066_; lean_object* v_currMacroScope_1067_; uint8_t v_diag_1068_; lean_object* v_cancelTk_x3f_1069_; uint8_t v_suppressElabErrors_1070_; lean_object* v_inheritedTraceOptions_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1367_; 
v_fileName_1056_ = lean_ctor_get(v_a_790_, 0);
v_fileMap_1057_ = lean_ctor_get(v_a_790_, 1);
v_options_1058_ = lean_ctor_get(v_a_790_, 2);
v_currRecDepth_1059_ = lean_ctor_get(v_a_790_, 3);
v_maxRecDepth_1060_ = lean_ctor_get(v_a_790_, 4);
v_ref_1061_ = lean_ctor_get(v_a_790_, 5);
v_currNamespace_1062_ = lean_ctor_get(v_a_790_, 6);
v_openDecls_1063_ = lean_ctor_get(v_a_790_, 7);
v_initHeartbeats_1064_ = lean_ctor_get(v_a_790_, 8);
v_maxHeartbeats_1065_ = lean_ctor_get(v_a_790_, 9);
v_quotContext_1066_ = lean_ctor_get(v_a_790_, 10);
v_currMacroScope_1067_ = lean_ctor_get(v_a_790_, 11);
v_diag_1068_ = lean_ctor_get_uint8(v_a_790_, sizeof(void*)*14);
v_cancelTk_x3f_1069_ = lean_ctor_get(v_a_790_, 12);
v_suppressElabErrors_1070_ = lean_ctor_get_uint8(v_a_790_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1071_ = lean_ctor_get(v_a_790_, 13);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1073_ = v_a_790_;
v_isShared_1074_ = v_isSharedCheck_1367_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_inheritedTraceOptions_1071_);
lean_inc(v_cancelTk_x3f_1069_);
lean_inc(v_currMacroScope_1067_);
lean_inc(v_quotContext_1066_);
lean_inc(v_maxHeartbeats_1065_);
lean_inc(v_initHeartbeats_1064_);
lean_inc(v_openDecls_1063_);
lean_inc(v_currNamespace_1062_);
lean_inc(v_ref_1061_);
lean_inc(v_maxRecDepth_1060_);
lean_inc(v_currRecDepth_1059_);
lean_inc(v_options_1058_);
lean_inc(v_fileMap_1057_);
lean_inc(v_fileName_1056_);
lean_dec(v_a_790_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1367_;
goto v_resetjp_1072_;
}
v___jp_793_:
{
if (v___y_796_ == 0)
{
lean_object* v___x_797_; lean_object* v_numSteps_798_; lean_object* v_persistentCache_799_; lean_object* v_transientCache_800_; lean_object* v_funext_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_811_; 
v___x_797_ = lean_st_ref_take(v___y_795_);
v_numSteps_798_ = lean_ctor_get(v___x_797_, 0);
v_persistentCache_799_ = lean_ctor_get(v___x_797_, 1);
v_transientCache_800_ = lean_ctor_get(v___x_797_, 2);
v_funext_801_ = lean_ctor_get(v___x_797_, 3);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_811_ == 0)
{
v___x_803_ = v___x_797_;
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_funext_801_);
lean_inc(v_transientCache_800_);
lean_inc(v_persistentCache_799_);
lean_inc(v_numSteps_798_);
lean_dec(v___x_797_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_inc_ref(v___y_794_);
v___x_805_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_799_, v_e_u2081_782_, v___y_794_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_numSteps_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_transientCache_800_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_funext_801_);
v___x_807_ = v_reuseFailAlloc_810_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_st_ref_set(v___y_795_, v___x_807_);
lean_dec(v___y_795_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___y_794_);
return v___x_809_;
}
}
}
else
{
lean_object* v___x_812_; lean_object* v_numSteps_813_; lean_object* v_persistentCache_814_; lean_object* v_transientCache_815_; lean_object* v_funext_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_826_; 
v___x_812_ = lean_st_ref_take(v___y_795_);
v_numSteps_813_ = lean_ctor_get(v___x_812_, 0);
v_persistentCache_814_ = lean_ctor_get(v___x_812_, 1);
v_transientCache_815_ = lean_ctor_get(v___x_812_, 2);
v_funext_816_ = lean_ctor_get(v___x_812_, 3);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_826_ == 0)
{
v___x_818_ = v___x_812_;
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_funext_816_);
lean_inc(v_transientCache_815_);
lean_inc(v_persistentCache_814_);
lean_inc(v_numSteps_813_);
lean_dec(v___x_812_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
lean_inc_ref(v___y_794_);
v___x_820_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_815_, v_e_u2081_782_, v___y_794_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 2, v___x_820_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_numSteps_813_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_persistentCache_814_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_funext_816_);
v___x_822_ = v_reuseFailAlloc_825_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_st_ref_set(v___y_795_, v___x_822_);
lean_dec(v___y_795_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___y_794_);
return v___x_824_;
}
}
}
}
v___jp_827_:
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_833_, 0, v___y_829_);
lean_ctor_set(v___x_833_, 1, v___y_831_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*2, v___y_828_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*2 + 1, v___y_832_);
v___y_794_ = v___x_833_;
v___y_795_ = v___y_830_;
v___y_796_ = v___y_832_;
goto v___jp_793_;
}
v___jp_834_:
{
lean_object* v___x_840_; 
v___x_840_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_840_, 0, v___y_835_);
lean_ctor_set(v___x_840_, 1, v___y_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*2, v___y_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*2 + 1, v___y_839_);
v___y_794_ = v___x_840_;
v___y_795_ = v___y_838_;
v___y_796_ = v___y_839_;
goto v___jp_793_;
}
v___jp_841_:
{
lean_object* v___x_854_; 
lean_inc(v___y_853_);
lean_inc_ref(v___y_852_);
lean_inc(v___y_851_);
lean_inc_ref(v___y_850_);
lean_inc(v___y_849_);
lean_inc(v___y_847_);
lean_inc_ref(v_e_u2082_842_);
v___x_854_ = lean_sym_simp(v_e_u2082_842_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
if (lean_obj_tag(v_a_855_) == 0)
{
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
if (v_cd_u2081_844_ == 0)
{
uint8_t v_done_856_; uint8_t v_contextDependent_857_; 
v_done_856_ = lean_ctor_get_uint8(v_a_855_, 0);
v_contextDependent_857_ = lean_ctor_get_uint8(v_a_855_, 1);
lean_dec_ref_known(v_a_855_, 0);
v___y_828_ = v_done_856_;
v___y_829_ = v_e_u2082_842_;
v___y_830_ = v___y_847_;
v___y_831_ = v_h_u2081_843_;
v___y_832_ = v_contextDependent_857_;
goto v___jp_827_;
}
else
{
uint8_t v_done_858_; 
v_done_858_ = lean_ctor_get_uint8(v_a_855_, 0);
lean_dec_ref_known(v_a_855_, 0);
v___y_828_ = v_done_858_;
v___y_829_ = v_e_u2082_842_;
v___y_830_ = v___y_847_;
v___y_831_ = v_h_u2081_843_;
v___y_832_ = v_cd_u2081_844_;
goto v___jp_827_;
}
}
else
{
lean_object* v_e_x27_859_; lean_object* v_proof_860_; uint8_t v_done_861_; uint8_t v_contextDependent_862_; lean_object* v___x_863_; 
v_e_x27_859_ = lean_ctor_get(v_a_855_, 0);
lean_inc_ref_n(v_e_x27_859_, 2);
v_proof_860_ = lean_ctor_get(v_a_855_, 1);
lean_inc_ref(v_proof_860_);
v_done_861_ = lean_ctor_get_uint8(v_a_855_, sizeof(void*)*2);
v_contextDependent_862_ = lean_ctor_get_uint8(v_a_855_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_855_, 2);
lean_inc_ref(v_e_u2081_782_);
v___x_863_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_782_, v_e_u2082_842_, v_h_u2081_843_, v_e_x27_859_, v_proof_860_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
if (lean_obj_tag(v___x_863_) == 0)
{
if (v_cd_u2081_844_ == 0)
{
lean_object* v_a_864_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___y_835_ = v_e_x27_859_;
v___y_836_ = v_a_864_;
v___y_837_ = v_done_861_;
v___y_838_ = v___y_847_;
v___y_839_ = v_contextDependent_862_;
goto v___jp_834_;
}
else
{
lean_object* v_a_865_; 
v_a_865_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_863_, 1);
v___y_835_ = v_e_x27_859_;
v___y_836_ = v_a_865_;
v___y_837_ = v_done_861_;
v___y_838_ = v___y_847_;
v___y_839_ = v_cd_u2081_844_;
goto v___jp_834_;
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v_e_x27_859_);
lean_dec(v___y_847_);
lean_dec_ref(v_e_u2081_782_);
v_a_866_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_863_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_863_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
else
{
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec(v___y_847_);
lean_dec_ref(v_h_u2081_843_);
lean_dec_ref(v_e_u2082_842_);
lean_dec_ref(v_e_u2081_782_);
return v___x_854_;
}
}
v___jp_874_:
{
if (lean_obj_tag(v___y_884_) == 0)
{
uint8_t v_contextDependent_885_; 
lean_dec(v___y_883_);
lean_dec(v___y_881_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v___y_875_);
v_contextDependent_885_ = lean_ctor_get_uint8(v___y_884_, 1);
if (v_contextDependent_885_ == 0)
{
lean_object* v___x_886_; lean_object* v_numSteps_887_; lean_object* v_persistentCache_888_; lean_object* v_transientCache_889_; lean_object* v_funext_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_900_; 
v___x_886_ = lean_st_ref_take(v___y_882_);
v_numSteps_887_ = lean_ctor_get(v___x_886_, 0);
v_persistentCache_888_ = lean_ctor_get(v___x_886_, 1);
v_transientCache_889_ = lean_ctor_get(v___x_886_, 2);
v_funext_890_ = lean_ctor_get(v___x_886_, 3);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_900_ == 0)
{
v___x_892_ = v___x_886_;
v_isShared_893_ = v_isSharedCheck_900_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_funext_890_);
lean_inc(v_transientCache_889_);
lean_inc(v_persistentCache_888_);
lean_inc(v_numSteps_887_);
lean_dec(v___x_886_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_900_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
lean_inc_ref(v___y_884_);
v___x_894_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_888_, v_e_u2081_782_, v___y_884_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v___x_894_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_numSteps_887_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_transientCache_889_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_funext_890_);
v___x_896_ = v_reuseFailAlloc_899_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_st_ref_set(v___y_882_, v___x_896_);
lean_dec(v___y_882_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___y_884_);
return v___x_898_;
}
}
}
else
{
lean_object* v___x_901_; lean_object* v_numSteps_902_; lean_object* v_persistentCache_903_; lean_object* v_transientCache_904_; lean_object* v_funext_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_915_; 
v___x_901_ = lean_st_ref_take(v___y_882_);
v_numSteps_902_ = lean_ctor_get(v___x_901_, 0);
v_persistentCache_903_ = lean_ctor_get(v___x_901_, 1);
v_transientCache_904_ = lean_ctor_get(v___x_901_, 2);
v_funext_905_ = lean_ctor_get(v___x_901_, 3);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_915_ == 0)
{
v___x_907_ = v___x_901_;
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_funext_905_);
lean_inc(v_transientCache_904_);
lean_inc(v_persistentCache_903_);
lean_inc(v_numSteps_902_);
lean_dec(v___x_901_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_inc_ref(v___y_884_);
v___x_909_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_904_, v_e_u2081_782_, v___y_884_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 2, v___x_909_);
v___x_911_ = v___x_907_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_numSteps_902_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_persistentCache_903_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_funext_905_);
v___x_911_ = v_reuseFailAlloc_914_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_st_ref_set(v___y_882_, v___x_911_);
lean_dec(v___y_882_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___y_884_);
return v___x_913_;
}
}
}
}
else
{
uint8_t v_done_916_; 
v_done_916_ = lean_ctor_get_uint8(v___y_884_, sizeof(void*)*2);
if (v_done_916_ == 0)
{
lean_object* v_e_x27_917_; lean_object* v_proof_918_; uint8_t v_contextDependent_919_; 
v_e_x27_917_ = lean_ctor_get(v___y_884_, 0);
lean_inc_ref(v_e_x27_917_);
v_proof_918_ = lean_ctor_get(v___y_884_, 1);
lean_inc_ref(v_proof_918_);
v_contextDependent_919_ = lean_ctor_get_uint8(v___y_884_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v___y_884_, 2);
v_e_u2082_842_ = v_e_x27_917_;
v_h_u2081_843_ = v_proof_918_;
v_cd_u2081_844_ = v_contextDependent_919_;
v___y_845_ = v___y_880_;
v___y_846_ = v___y_878_;
v___y_847_ = v___y_882_;
v___y_848_ = v___y_877_;
v___y_849_ = v___y_883_;
v___y_850_ = v___y_876_;
v___y_851_ = v___y_881_;
v___y_852_ = v___y_875_;
v___y_853_ = v___y_879_;
goto v___jp_841_;
}
else
{
uint8_t v_contextDependent_920_; 
lean_dec(v___y_883_);
lean_dec(v___y_881_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v___y_875_);
v_contextDependent_920_ = lean_ctor_get_uint8(v___y_884_, sizeof(void*)*2 + 1);
if (v_contextDependent_920_ == 0)
{
lean_object* v___x_921_; lean_object* v_numSteps_922_; lean_object* v_persistentCache_923_; lean_object* v_transientCache_924_; lean_object* v_funext_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_935_; 
v___x_921_ = lean_st_ref_take(v___y_882_);
v_numSteps_922_ = lean_ctor_get(v___x_921_, 0);
v_persistentCache_923_ = lean_ctor_get(v___x_921_, 1);
v_transientCache_924_ = lean_ctor_get(v___x_921_, 2);
v_funext_925_ = lean_ctor_get(v___x_921_, 3);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_935_ == 0)
{
v___x_927_ = v___x_921_;
v_isShared_928_ = v_isSharedCheck_935_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_funext_925_);
lean_inc(v_transientCache_924_);
lean_inc(v_persistentCache_923_);
lean_inc(v_numSteps_922_);
lean_dec(v___x_921_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_935_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_inc_ref(v___y_884_);
v___x_929_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_923_, v_e_u2081_782_, v___y_884_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v___x_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_numSteps_922_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_transientCache_924_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_funext_925_);
v___x_931_ = v_reuseFailAlloc_934_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_st_ref_set(v___y_882_, v___x_931_);
lean_dec(v___y_882_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___y_884_);
return v___x_933_;
}
}
}
else
{
lean_object* v___x_936_; lean_object* v_numSteps_937_; lean_object* v_persistentCache_938_; lean_object* v_transientCache_939_; lean_object* v_funext_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_950_; 
v___x_936_ = lean_st_ref_take(v___y_882_);
v_numSteps_937_ = lean_ctor_get(v___x_936_, 0);
v_persistentCache_938_ = lean_ctor_get(v___x_936_, 1);
v_transientCache_939_ = lean_ctor_get(v___x_936_, 2);
v_funext_940_ = lean_ctor_get(v___x_936_, 3);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_950_ == 0)
{
v___x_942_ = v___x_936_;
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_funext_940_);
lean_inc(v_transientCache_939_);
lean_inc(v_persistentCache_938_);
lean_inc(v_numSteps_937_);
lean_dec(v___x_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
lean_inc_ref(v___y_884_);
v___x_944_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_939_, v_e_u2081_782_, v___y_884_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 2, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_numSteps_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_persistentCache_938_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_funext_940_);
v___x_946_ = v_reuseFailAlloc_949_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_st_ref_set(v___y_882_, v___x_946_);
lean_dec(v___y_882_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___y_884_);
return v___x_948_;
}
}
}
}
}
}
v___jp_951_:
{
if (v___y_962_ == 0)
{
v___y_875_ = v___y_952_;
v___y_876_ = v___y_953_;
v___y_877_ = v___y_954_;
v___y_878_ = v___y_955_;
v___y_879_ = v___y_956_;
v___y_880_ = v___y_957_;
v___y_881_ = v___y_959_;
v___y_882_ = v___y_960_;
v___y_883_ = v___y_961_;
v___y_884_ = v___y_958_;
goto v___jp_874_;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_958_);
v___y_875_ = v___y_952_;
v___y_876_ = v___y_953_;
v___y_877_ = v___y_954_;
v___y_878_ = v___y_955_;
v___y_879_ = v___y_956_;
v___y_880_ = v___y_957_;
v___y_881_ = v___y_959_;
v___y_882_ = v___y_960_;
v___y_883_ = v___y_961_;
v___y_884_ = v___x_963_;
goto v___jp_874_;
}
}
v___jp_964_:
{
if (v___y_977_ == 0)
{
v___y_952_ = v___y_974_;
v___y_953_ = v___y_966_;
v___y_954_ = v___y_967_;
v___y_955_ = v___y_975_;
v___y_956_ = v___y_968_;
v___y_957_ = v___y_969_;
v___y_958_ = v___y_970_;
v___y_959_ = v___y_972_;
v___y_960_ = v___y_976_;
v___y_961_ = v___y_973_;
v___y_962_ = v___y_971_;
goto v___jp_951_;
}
else
{
v___y_952_ = v___y_974_;
v___y_953_ = v___y_966_;
v___y_954_ = v___y_967_;
v___y_955_ = v___y_975_;
v___y_956_ = v___y_968_;
v___y_957_ = v___y_969_;
v___y_958_ = v___y_970_;
v___y_959_ = v___y_972_;
v___y_960_ = v___y_976_;
v___y_961_ = v___y_973_;
v___y_962_ = v___y_965_;
goto v___jp_951_;
}
}
v___jp_978_:
{
if (v___y_986_ == 0)
{
v___y_875_ = v___y_980_;
v___y_876_ = v___y_981_;
v___y_877_ = v___y_982_;
v___y_878_ = v___y_983_;
v___y_879_ = v___y_984_;
v___y_880_ = v___y_985_;
v___y_881_ = v___y_987_;
v___y_882_ = v___y_988_;
v___y_883_ = v___y_989_;
v___y_884_ = v_a_990_;
goto v___jp_874_;
}
else
{
if (lean_obj_tag(v_a_990_) == 0)
{
uint8_t v_contextDependent_991_; 
v_contextDependent_991_ = lean_ctor_get_uint8(v_a_990_, 1);
v___y_965_ = v___y_979_;
v___y_966_ = v___y_981_;
v___y_967_ = v___y_982_;
v___y_968_ = v___y_984_;
v___y_969_ = v___y_985_;
v___y_970_ = v_a_990_;
v___y_971_ = v___y_986_;
v___y_972_ = v___y_987_;
v___y_973_ = v___y_989_;
v___y_974_ = v___y_980_;
v___y_975_ = v___y_983_;
v___y_976_ = v___y_988_;
v___y_977_ = v_contextDependent_991_;
goto v___jp_964_;
}
else
{
uint8_t v_contextDependent_992_; 
v_contextDependent_992_ = lean_ctor_get_uint8(v_a_990_, sizeof(void*)*2 + 1);
v___y_965_ = v___y_979_;
v___y_966_ = v___y_981_;
v___y_967_ = v___y_982_;
v___y_968_ = v___y_984_;
v___y_969_ = v___y_985_;
v___y_970_ = v_a_990_;
v___y_971_ = v___y_986_;
v___y_972_ = v___y_987_;
v___y_973_ = v___y_989_;
v___y_974_ = v___y_980_;
v___y_975_ = v___y_983_;
v___y_976_ = v___y_988_;
v___y_977_ = v_contextDependent_992_;
goto v___jp_964_;
}
}
}
v___jp_993_:
{
if (lean_obj_tag(v___y_1005_) == 0)
{
lean_object* v_a_1006_; 
v_a_1006_ = lean_ctor_get(v___y_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___y_1005_, 1);
v___y_979_ = v___y_995_;
v___y_980_ = v___y_994_;
v___y_981_ = v___y_996_;
v___y_982_ = v___y_997_;
v___y_983_ = v___y_998_;
v___y_984_ = v___y_999_;
v___y_985_ = v___y_1000_;
v___y_986_ = v___y_1001_;
v___y_987_ = v___y_1002_;
v___y_988_ = v___y_1003_;
v___y_989_ = v___y_1004_;
v_a_990_ = v_a_1006_;
goto v___jp_978_;
}
else
{
lean_dec(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec_ref(v___y_994_);
lean_dec_ref(v_e_u2081_782_);
return v___y_1005_;
}
}
v___jp_1007_:
{
if (v___y_1020_ == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1009_);
v___y_979_ = v___y_1008_;
v___y_980_ = v___y_1017_;
v___y_981_ = v___y_1010_;
v___y_982_ = v___y_1011_;
v___y_983_ = v___y_1018_;
v___y_984_ = v___y_1012_;
v___y_985_ = v___y_1013_;
v___y_986_ = v___y_1014_;
v___y_987_ = v___y_1015_;
v___y_988_ = v___y_1019_;
v___y_989_ = v___y_1016_;
v_a_990_ = v___x_1021_;
goto v___jp_978_;
}
else
{
v___y_979_ = v___y_1008_;
v___y_980_ = v___y_1017_;
v___y_981_ = v___y_1010_;
v___y_982_ = v___y_1011_;
v___y_983_ = v___y_1018_;
v___y_984_ = v___y_1012_;
v___y_985_ = v___y_1013_;
v___y_986_ = v___y_1014_;
v___y_987_ = v___y_1015_;
v___y_988_ = v___y_1019_;
v___y_989_ = v___y_1016_;
v_a_990_ = v___y_1009_;
goto v___jp_978_;
}
}
v___jp_1022_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1038_, 0, v___y_1030_);
lean_ctor_set(v___x_1038_, 1, v___y_1035_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*2, v___y_1034_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*2 + 1, v___y_1037_);
v___y_979_ = v___y_1023_;
v___y_980_ = v___y_1032_;
v___y_981_ = v___y_1024_;
v___y_982_ = v___y_1025_;
v___y_983_ = v___y_1033_;
v___y_984_ = v___y_1026_;
v___y_985_ = v___y_1027_;
v___y_986_ = v___y_1028_;
v___y_987_ = v___y_1029_;
v___y_988_ = v___y_1036_;
v___y_989_ = v___y_1031_;
v_a_990_ = v___x_1038_;
goto v___jp_978_;
}
v___jp_1039_:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1055_, 0, v___y_1051_);
lean_ctor_set(v___x_1055_, 1, v___y_1041_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*2, v___y_1053_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*2 + 1, v___y_1054_);
v___y_979_ = v___y_1040_;
v___y_980_ = v___y_1049_;
v___y_981_ = v___y_1042_;
v___y_982_ = v___y_1043_;
v___y_983_ = v___y_1050_;
v___y_984_ = v___y_1044_;
v___y_985_ = v___y_1045_;
v___y_986_ = v___y_1046_;
v___y_987_ = v___y_1047_;
v___y_988_ = v___y_1052_;
v___y_989_ = v___y_1048_;
v_a_990_ = v___x_1055_;
goto v___jp_978_;
}
v_resetjp_1072_:
{
lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_nat_dec_eq(v_maxRecDepth_1060_, v___x_1363_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_eq(v_currRecDepth_1059_, v_maxRecDepth_1060_);
if (v___x_1365_ == 0)
{
goto v___jp_1333_;
}
else
{
lean_object* v___x_1366_; 
lean_del_object(v___x_1073_);
lean_dec_ref(v_inheritedTraceOptions_1071_);
lean_dec(v_cancelTk_x3f_1069_);
lean_dec(v_currMacroScope_1067_);
lean_dec(v_quotContext_1066_);
lean_dec(v_maxHeartbeats_1065_);
lean_dec(v_initHeartbeats_1064_);
lean_dec(v_openDecls_1063_);
lean_dec(v_currNamespace_1062_);
lean_dec(v_maxRecDepth_1060_);
lean_dec(v_currRecDepth_1059_);
lean_dec_ref(v_options_1058_);
lean_dec_ref(v_fileMap_1057_);
lean_dec_ref(v_fileName_1056_);
lean_dec(v_a_791_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_e_u2081_782_);
v___x_1366_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_1061_);
return v___x_1366_;
}
}
else
{
goto v___jp_1333_;
}
v___jp_1075_:
{
lean_object* v___x_1086_; lean_object* v_persistentCache_1087_; lean_object* v_transientCache_1088_; lean_object* v_funext_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1214_; 
v___x_1086_ = lean_st_ref_take(v___y_1079_);
v_persistentCache_1087_ = lean_ctor_get(v___x_1086_, 1);
v_transientCache_1088_ = lean_ctor_get(v___x_1086_, 2);
v_funext_1089_ = lean_ctor_get(v___x_1086_, 3);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v___x_1086_, 0);
lean_dec(v_unused_1215_);
v___x_1091_ = v___x_1086_;
v_isShared_1092_ = v_isSharedCheck_1214_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_funext_1089_);
lean_inc(v_transientCache_1088_);
lean_inc(v_persistentCache_1087_);
lean_dec(v___x_1086_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1214_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___y_1076_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___y_1076_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_persistentCache_1087_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_transientCache_1088_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_funext_1089_);
v___x_1094_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v_pre_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_st_ref_set(v___y_1079_, v___x_1094_);
v_pre_1096_ = lean_ctor_get(v___y_1077_, 0);
lean_inc_ref(v_pre_1096_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v___y_1077_);
lean_inc_ref(v_e_u2081_782_);
v___x_1097_ = lean_apply_11(v_pre_1096_, v_e_u2081_782_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, lean_box(0));
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1212_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1212_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1212_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
if (lean_obj_tag(v_a_1098_) == 0)
{
uint8_t v_done_1102_; 
v_done_1102_ = lean_ctor_get_uint8(v_a_1098_, 0);
if (v_done_1102_ == 0)
{
uint8_t v_contextDependent_1103_; lean_object* v___x_1104_; 
lean_del_object(v___x_1100_);
v_contextDependent_1103_ = lean_ctor_get_uint8(v_a_1098_, 1);
lean_dec_ref_known(v_a_1098_, 0);
lean_inc_ref(v_e_u2081_782_);
v___x_1104_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_u2081_782_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
v___x_1106_ = lean_box(0);
if (lean_obj_tag(v_a_1105_) == 0)
{
uint8_t v_done_1107_; 
v_done_1107_ = lean_ctor_get_uint8(v_a_1105_, 0);
if (v_done_1107_ == 0)
{
uint8_t v_contextDependent_1108_; lean_object* v___x_1109_; 
lean_dec_ref_known(v___x_1104_, 1);
v_contextDependent_1108_ = lean_ctor_get_uint8(v_a_1105_, 1);
lean_dec_ref_known(v_a_1105_, 0);
lean_inc_ref(v_e_u2081_782_);
v___x_1109_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1106_, v_e_u2081_782_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1109_) == 0)
{
if (v_contextDependent_1108_ == 0)
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___y_979_ = v_done_1102_;
v___y_980_ = v___y_1084_;
v___y_981_ = v___y_1082_;
v___y_982_ = v___y_1080_;
v___y_983_ = v___y_1078_;
v___y_984_ = v___y_1085_;
v___y_985_ = v___y_1077_;
v___y_986_ = v_contextDependent_1103_;
v___y_987_ = v___y_1083_;
v___y_988_ = v___y_1079_;
v___y_989_ = v___y_1081_;
v_a_990_ = v_a_1110_;
goto v___jp_978_;
}
else
{
lean_object* v_a_1111_; 
v_a_1111_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1109_, 1);
if (lean_obj_tag(v_a_1111_) == 0)
{
uint8_t v_contextDependent_1112_; 
v_contextDependent_1112_ = lean_ctor_get_uint8(v_a_1111_, 1);
v___y_1008_ = v_done_1102_;
v___y_1009_ = v_a_1111_;
v___y_1010_ = v___y_1082_;
v___y_1011_ = v___y_1080_;
v___y_1012_ = v___y_1085_;
v___y_1013_ = v___y_1077_;
v___y_1014_ = v_contextDependent_1103_;
v___y_1015_ = v___y_1083_;
v___y_1016_ = v___y_1081_;
v___y_1017_ = v___y_1084_;
v___y_1018_ = v___y_1078_;
v___y_1019_ = v___y_1079_;
v___y_1020_ = v_contextDependent_1112_;
goto v___jp_1007_;
}
else
{
uint8_t v_contextDependent_1113_; 
v_contextDependent_1113_ = lean_ctor_get_uint8(v_a_1111_, sizeof(void*)*2 + 1);
v___y_1008_ = v_done_1102_;
v___y_1009_ = v_a_1111_;
v___y_1010_ = v___y_1082_;
v___y_1011_ = v___y_1080_;
v___y_1012_ = v___y_1085_;
v___y_1013_ = v___y_1077_;
v___y_1014_ = v_contextDependent_1103_;
v___y_1015_ = v___y_1083_;
v___y_1016_ = v___y_1081_;
v___y_1017_ = v___y_1084_;
v___y_1018_ = v___y_1078_;
v___y_1019_ = v___y_1079_;
v___y_1020_ = v_contextDependent_1113_;
goto v___jp_1007_;
}
}
}
else
{
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v_e_u2081_782_);
return v___x_1109_;
}
}
else
{
lean_dec_ref_known(v_a_1105_, 0);
v___y_994_ = v___y_1084_;
v___y_995_ = v_done_1102_;
v___y_996_ = v___y_1082_;
v___y_997_ = v___y_1080_;
v___y_998_ = v___y_1078_;
v___y_999_ = v___y_1085_;
v___y_1000_ = v___y_1077_;
v___y_1001_ = v_contextDependent_1103_;
v___y_1002_ = v___y_1083_;
v___y_1003_ = v___y_1079_;
v___y_1004_ = v___y_1081_;
v___y_1005_ = v___x_1104_;
goto v___jp_993_;
}
}
else
{
uint8_t v_done_1114_; 
v_done_1114_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*2);
if (v_done_1114_ == 0)
{
lean_object* v_e_x27_1115_; lean_object* v_proof_1116_; uint8_t v_contextDependent_1117_; lean_object* v___x_1118_; 
lean_dec_ref_known(v___x_1104_, 1);
v_e_x27_1115_ = lean_ctor_get(v_a_1105_, 0);
lean_inc_ref_n(v_e_x27_1115_, 2);
v_proof_1116_ = lean_ctor_get(v_a_1105_, 1);
lean_inc_ref(v_proof_1116_);
v_contextDependent_1117_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1105_, 2);
v___x_1118_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1106_, v_e_x27_1115_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
if (lean_obj_tag(v_a_1119_) == 0)
{
if (v_contextDependent_1117_ == 0)
{
uint8_t v_done_1120_; uint8_t v_contextDependent_1121_; 
v_done_1120_ = lean_ctor_get_uint8(v_a_1119_, 0);
v_contextDependent_1121_ = lean_ctor_get_uint8(v_a_1119_, 1);
lean_dec_ref_known(v_a_1119_, 0);
v___y_1023_ = v_done_1102_;
v___y_1024_ = v___y_1082_;
v___y_1025_ = v___y_1080_;
v___y_1026_ = v___y_1085_;
v___y_1027_ = v___y_1077_;
v___y_1028_ = v_contextDependent_1103_;
v___y_1029_ = v___y_1083_;
v___y_1030_ = v_e_x27_1115_;
v___y_1031_ = v___y_1081_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1078_;
v___y_1034_ = v_done_1120_;
v___y_1035_ = v_proof_1116_;
v___y_1036_ = v___y_1079_;
v___y_1037_ = v_contextDependent_1121_;
goto v___jp_1022_;
}
else
{
uint8_t v_done_1122_; 
v_done_1122_ = lean_ctor_get_uint8(v_a_1119_, 0);
lean_dec_ref_known(v_a_1119_, 0);
v___y_1023_ = v_done_1102_;
v___y_1024_ = v___y_1082_;
v___y_1025_ = v___y_1080_;
v___y_1026_ = v___y_1085_;
v___y_1027_ = v___y_1077_;
v___y_1028_ = v_contextDependent_1103_;
v___y_1029_ = v___y_1083_;
v___y_1030_ = v_e_x27_1115_;
v___y_1031_ = v___y_1081_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1078_;
v___y_1034_ = v_done_1122_;
v___y_1035_ = v_proof_1116_;
v___y_1036_ = v___y_1079_;
v___y_1037_ = v_contextDependent_1117_;
goto v___jp_1022_;
}
}
else
{
lean_object* v_e_x27_1123_; lean_object* v_proof_1124_; uint8_t v_done_1125_; uint8_t v_contextDependent_1126_; lean_object* v___x_1127_; 
v_e_x27_1123_ = lean_ctor_get(v_a_1119_, 0);
lean_inc_ref_n(v_e_x27_1123_, 2);
v_proof_1124_ = lean_ctor_get(v_a_1119_, 1);
lean_inc_ref(v_proof_1124_);
v_done_1125_ = lean_ctor_get_uint8(v_a_1119_, sizeof(void*)*2);
v_contextDependent_1126_ = lean_ctor_get_uint8(v_a_1119_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1119_, 2);
lean_inc_ref(v_e_u2081_782_);
v___x_1127_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_782_, v_e_x27_1115_, v_proof_1116_, v_e_x27_1123_, v_proof_1124_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1127_) == 0)
{
if (v_contextDependent_1117_ == 0)
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___y_1040_ = v_done_1102_;
v___y_1041_ = v_a_1128_;
v___y_1042_ = v___y_1082_;
v___y_1043_ = v___y_1080_;
v___y_1044_ = v___y_1085_;
v___y_1045_ = v___y_1077_;
v___y_1046_ = v_contextDependent_1103_;
v___y_1047_ = v___y_1083_;
v___y_1048_ = v___y_1081_;
v___y_1049_ = v___y_1084_;
v___y_1050_ = v___y_1078_;
v___y_1051_ = v_e_x27_1123_;
v___y_1052_ = v___y_1079_;
v___y_1053_ = v_done_1125_;
v___y_1054_ = v_contextDependent_1126_;
goto v___jp_1039_;
}
else
{
lean_object* v_a_1129_; 
v_a_1129_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1127_, 1);
v___y_1040_ = v_done_1102_;
v___y_1041_ = v_a_1129_;
v___y_1042_ = v___y_1082_;
v___y_1043_ = v___y_1080_;
v___y_1044_ = v___y_1085_;
v___y_1045_ = v___y_1077_;
v___y_1046_ = v_contextDependent_1103_;
v___y_1047_ = v___y_1083_;
v___y_1048_ = v___y_1081_;
v___y_1049_ = v___y_1084_;
v___y_1050_ = v___y_1078_;
v___y_1051_ = v_e_x27_1123_;
v___y_1052_ = v___y_1079_;
v___y_1053_ = v_done_1125_;
v___y_1054_ = v_contextDependent_1117_;
goto v___jp_1039_;
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v_e_x27_1123_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v_e_u2081_782_);
v_a_1130_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1127_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1116_);
lean_dec_ref(v_e_x27_1115_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v_e_u2081_782_);
return v___x_1118_;
}
}
else
{
lean_dec_ref_known(v_a_1105_, 2);
v___y_994_ = v___y_1084_;
v___y_995_ = v_done_1102_;
v___y_996_ = v___y_1082_;
v___y_997_ = v___y_1080_;
v___y_998_ = v___y_1078_;
v___y_999_ = v___y_1085_;
v___y_1000_ = v___y_1077_;
v___y_1001_ = v_contextDependent_1103_;
v___y_1002_ = v___y_1083_;
v___y_1003_ = v___y_1079_;
v___y_1004_ = v___y_1081_;
v___y_1005_ = v___x_1104_;
goto v___jp_993_;
}
}
}
else
{
v___y_994_ = v___y_1084_;
v___y_995_ = v_done_1102_;
v___y_996_ = v___y_1082_;
v___y_997_ = v___y_1080_;
v___y_998_ = v___y_1078_;
v___y_999_ = v___y_1085_;
v___y_1000_ = v___y_1077_;
v___y_1001_ = v_contextDependent_1103_;
v___y_1002_ = v___y_1083_;
v___y_1003_ = v___y_1079_;
v___y_1004_ = v___y_1081_;
v___y_1005_ = v___x_1104_;
goto v___jp_993_;
}
}
else
{
uint8_t v_contextDependent_1138_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
v_contextDependent_1138_ = lean_ctor_get_uint8(v_a_1098_, 1);
if (v_contextDependent_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v_numSteps_1140_; lean_object* v_persistentCache_1141_; lean_object* v_transientCache_1142_; lean_object* v_funext_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1155_; 
v___x_1139_ = lean_st_ref_take(v___y_1079_);
v_numSteps_1140_ = lean_ctor_get(v___x_1139_, 0);
v_persistentCache_1141_ = lean_ctor_get(v___x_1139_, 1);
v_transientCache_1142_ = lean_ctor_get(v___x_1139_, 2);
v_funext_1143_ = lean_ctor_get(v___x_1139_, 3);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1145_ = v___x_1139_;
v_isShared_1146_ = v_isSharedCheck_1155_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_funext_1143_);
lean_inc(v_transientCache_1142_);
lean_inc(v_persistentCache_1141_);
lean_inc(v_numSteps_1140_);
lean_dec(v___x_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1155_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
lean_inc_ref(v_a_1098_);
v___x_1147_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1141_, v_e_u2081_782_, v_a_1098_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_numSteps_1140_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_transientCache_1142_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_funext_1143_);
v___x_1149_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_st_ref_set(v___y_1079_, v___x_1149_);
lean_dec(v___y_1079_);
if (v_isShared_1101_ == 0)
{
v___x_1152_ = v___x_1100_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1098_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v___x_1156_; lean_object* v_numSteps_1157_; lean_object* v_persistentCache_1158_; lean_object* v_transientCache_1159_; lean_object* v_funext_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1172_; 
v___x_1156_ = lean_st_ref_take(v___y_1079_);
v_numSteps_1157_ = lean_ctor_get(v___x_1156_, 0);
v_persistentCache_1158_ = lean_ctor_get(v___x_1156_, 1);
v_transientCache_1159_ = lean_ctor_get(v___x_1156_, 2);
v_funext_1160_ = lean_ctor_get(v___x_1156_, 3);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1162_ = v___x_1156_;
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_funext_1160_);
lean_inc(v_transientCache_1159_);
lean_inc(v_persistentCache_1158_);
lean_inc(v_numSteps_1157_);
lean_dec(v___x_1156_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_inc_ref(v_a_1098_);
v___x_1164_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1159_, v_e_u2081_782_, v_a_1098_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 2, v___x_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_numSteps_1157_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_persistentCache_1158_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_funext_1160_);
v___x_1166_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_st_ref_set(v___y_1079_, v___x_1166_);
lean_dec(v___y_1079_);
if (v_isShared_1101_ == 0)
{
v___x_1169_ = v___x_1100_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1098_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
else
{
uint8_t v_done_1173_; 
v_done_1173_ = lean_ctor_get_uint8(v_a_1098_, sizeof(void*)*2);
if (v_done_1173_ == 0)
{
lean_object* v_e_x27_1174_; lean_object* v_proof_1175_; uint8_t v_contextDependent_1176_; 
lean_del_object(v___x_1100_);
v_e_x27_1174_ = lean_ctor_get(v_a_1098_, 0);
lean_inc_ref(v_e_x27_1174_);
v_proof_1175_ = lean_ctor_get(v_a_1098_, 1);
lean_inc_ref(v_proof_1175_);
v_contextDependent_1176_ = lean_ctor_get_uint8(v_a_1098_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1098_, 2);
v_e_u2082_842_ = v_e_x27_1174_;
v_h_u2081_843_ = v_proof_1175_;
v_cd_u2081_844_ = v_contextDependent_1176_;
v___y_845_ = v___y_1077_;
v___y_846_ = v___y_1078_;
v___y_847_ = v___y_1079_;
v___y_848_ = v___y_1080_;
v___y_849_ = v___y_1081_;
v___y_850_ = v___y_1082_;
v___y_851_ = v___y_1083_;
v___y_852_ = v___y_1084_;
v___y_853_ = v___y_1085_;
goto v___jp_841_;
}
else
{
uint8_t v_contextDependent_1177_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
v_contextDependent_1177_ = lean_ctor_get_uint8(v_a_1098_, sizeof(void*)*2 + 1);
if (v_contextDependent_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v_numSteps_1179_; lean_object* v_persistentCache_1180_; lean_object* v_transientCache_1181_; lean_object* v_funext_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1194_; 
v___x_1178_ = lean_st_ref_take(v___y_1079_);
v_numSteps_1179_ = lean_ctor_get(v___x_1178_, 0);
v_persistentCache_1180_ = lean_ctor_get(v___x_1178_, 1);
v_transientCache_1181_ = lean_ctor_get(v___x_1178_, 2);
v_funext_1182_ = lean_ctor_get(v___x_1178_, 3);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1184_ = v___x_1178_;
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_funext_1182_);
lean_inc(v_transientCache_1181_);
lean_inc(v_persistentCache_1180_);
lean_inc(v_numSteps_1179_);
lean_dec(v___x_1178_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_inc_ref(v_a_1098_);
v___x_1186_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1180_, v_e_u2081_782_, v_a_1098_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 1, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_numSteps_1179_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_transientCache_1181_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_funext_1182_);
v___x_1188_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_st_ref_set(v___y_1079_, v___x_1188_);
lean_dec(v___y_1079_);
if (v_isShared_1101_ == 0)
{
v___x_1191_ = v___x_1100_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1098_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v___x_1195_; lean_object* v_numSteps_1196_; lean_object* v_persistentCache_1197_; lean_object* v_transientCache_1198_; lean_object* v_funext_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1211_; 
v___x_1195_ = lean_st_ref_take(v___y_1079_);
v_numSteps_1196_ = lean_ctor_get(v___x_1195_, 0);
v_persistentCache_1197_ = lean_ctor_get(v___x_1195_, 1);
v_transientCache_1198_ = lean_ctor_get(v___x_1195_, 2);
v_funext_1199_ = lean_ctor_get(v___x_1195_, 3);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1201_ = v___x_1195_;
v_isShared_1202_ = v_isSharedCheck_1211_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_funext_1199_);
lean_inc(v_transientCache_1198_);
lean_inc(v_persistentCache_1197_);
lean_inc(v_numSteps_1196_);
lean_dec(v___x_1195_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1211_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_inc_ref(v_a_1098_);
v___x_1203_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1198_, v_e_u2081_782_, v_a_1098_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 2, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_numSteps_1196_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_persistentCache_1197_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_funext_1199_);
v___x_1205_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_st_ref_set(v___y_1079_, v___x_1205_);
lean_dec(v___y_1079_);
if (v_isShared_1101_ == 0)
{
v___x_1208_ = v___x_1100_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1098_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
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
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v_e_u2081_782_);
return v___x_1097_;
}
}
}
}
v___jp_1216_:
{
lean_object* v___x_1228_; lean_object* v_persistentCache_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_st_ref_get(v___y_1221_);
v_persistentCache_1229_ = lean_ctor_get(v___x_1228_, 1);
lean_inc_ref(v_persistentCache_1229_);
lean_dec(v___x_1228_);
v___x_1230_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_persistentCache_1229_, v_e_u2081_782_);
lean_dec_ref(v_persistentCache_1229_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_options_1231_; uint8_t v_hasTrace_1232_; 
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec(v___y_1217_);
v_options_1231_ = lean_ctor_get(v___y_1226_, 2);
v_hasTrace_1232_ = lean_ctor_get_uint8(v_options_1231_, sizeof(void*)*1);
if (v_hasTrace_1232_ == 0)
{
lean_object* v_val_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v_e_u2081_782_);
v_val_1233_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1230_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_val_1233_);
lean_dec(v___x_1230_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set_tag(v___x_1235_, 0);
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_val_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
else
{
lean_object* v_val_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1272_; 
v_val_1241_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1243_ = v___x_1230_;
v_isShared_1244_ = v_isSharedCheck_1272_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_val_1241_);
lean_dec(v___x_1230_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1272_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_inheritedTraceOptions_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_inheritedTraceOptions_1245_ = lean_ctor_get(v___y_1226_, 13);
v___x_1246_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1247_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1248_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1245_, v_options_1231_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1250_; 
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v_e_u2081_782_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 0);
v___x_1250_ = v___x_1243_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_val_1241_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_del_object(v___x_1243_);
v___x_1252_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4);
v___x_1253_ = l_Lean_MessageData_ofExpr(v_e_u2081_782_);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1246_, v___x_1254_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1263_);
v___x_1257_ = v___x_1255_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v___x_1255_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_val_1241_);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_val_1241_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_val_1241_);
v_a_1264_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1255_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1255_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1273_; lean_object* v_transientCache_1274_; lean_object* v___x_1275_; 
lean_dec(v___x_1230_);
v___x_1273_ = lean_st_ref_get(v___y_1221_);
v_transientCache_1274_ = lean_ctor_get(v___x_1273_, 2);
lean_inc_ref(v_transientCache_1274_);
lean_dec(v___x_1273_);
v___x_1275_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_transientCache_1274_, v_e_u2081_782_);
lean_dec_ref(v_transientCache_1274_);
if (lean_obj_tag(v___x_1275_) == 1)
{
lean_object* v_options_1276_; uint8_t v_hasTrace_1277_; 
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec(v___y_1217_);
v_options_1276_ = lean_ctor_get(v___y_1226_, 2);
v_hasTrace_1277_ = lean_ctor_get_uint8(v_options_1276_, sizeof(void*)*1);
if (v_hasTrace_1277_ == 0)
{
lean_object* v_val_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v_e_u2081_782_);
v_val_1278_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1275_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_val_1278_);
lean_dec(v___x_1275_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 0);
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_val_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_val_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1317_; 
v_val_1286_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1288_ = v___x_1275_;
v_isShared_1289_ = v_isSharedCheck_1317_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_val_1286_);
lean_dec(v___x_1275_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1317_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_inheritedTraceOptions_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_inheritedTraceOptions_1290_ = lean_ctor_get(v___y_1226_, 13);
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1292_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1293_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1290_, v_options_1276_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1295_; 
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v_e_u2081_782_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set_tag(v___x_1288_, 0);
v___x_1295_ = v___x_1288_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_val_1286_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_del_object(v___x_1288_);
v___x_1297_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6);
v___x_1298_ = l_Lean_MessageData_ofExpr(v_e_u2081_782_);
v___x_1299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1291_, v___x_1299_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; 
v_unused_1308_ = lean_ctor_get(v___x_1300_, 0);
lean_dec(v_unused_1308_);
v___x_1302_ = v___x_1300_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v___x_1300_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v_val_1286_);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_val_1286_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_val_1286_);
v_a_1309_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1300_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1300_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
lean_dec(v___x_1275_);
v___x_1318_ = lean_nat_add(v___y_1217_, v___y_1218_);
lean_dec(v___y_1217_);
v___x_1319_ = lean_unsigned_to_nat(1000u);
v___x_1320_ = lean_nat_mod(v___x_1318_, v___x_1319_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_nat_dec_eq(v___x_1320_, v___x_1321_);
lean_dec(v___x_1320_);
if (v___x_1322_ == 0)
{
v___y_1076_ = v___x_1318_;
v___y_1077_ = v___y_1219_;
v___y_1078_ = v___y_1220_;
v___y_1079_ = v___y_1221_;
v___y_1080_ = v___y_1222_;
v___y_1081_ = v___y_1223_;
v___y_1082_ = v___y_1224_;
v___y_1083_ = v___y_1225_;
v___y_1084_ = v___y_1226_;
v___y_1085_ = v___y_1227_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1324_ = l_Lean_Core_checkSystem(v___x_1323_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_dec_ref_known(v___x_1324_, 1);
v___y_1076_ = v___x_1318_;
v___y_1077_ = v___y_1219_;
v___y_1078_ = v___y_1220_;
v___y_1079_ = v___y_1221_;
v___y_1080_ = v___y_1222_;
v___y_1081_ = v___y_1223_;
v___y_1082_ = v___y_1224_;
v___y_1083_ = v___y_1225_;
v___y_1084_ = v___y_1226_;
v___y_1085_ = v___y_1227_;
goto v___jp_1075_;
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v___x_1318_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v_e_u2081_782_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
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
}
}
}
v___jp_1333_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_st_ref_get(v_a_785_);
v___x_1335_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_784_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_numSteps_1337_; lean_object* v_maxSteps_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v_numSteps_1337_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_numSteps_1337_);
lean_dec(v___x_1334_);
v_maxSteps_1338_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_maxSteps_1338_);
lean_dec(v_a_1336_);
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_nat_add(v_currRecDepth_1059_, v___x_1339_);
lean_dec(v_currRecDepth_1059_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 3, v___x_1340_);
v___x_1342_ = v___x_1073_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_fileName_1056_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_fileMap_1057_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_options_1058_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v_maxRecDepth_1060_);
lean_ctor_set(v_reuseFailAlloc_1354_, 5, v_ref_1061_);
lean_ctor_set(v_reuseFailAlloc_1354_, 6, v_currNamespace_1062_);
lean_ctor_set(v_reuseFailAlloc_1354_, 7, v_openDecls_1063_);
lean_ctor_set(v_reuseFailAlloc_1354_, 8, v_initHeartbeats_1064_);
lean_ctor_set(v_reuseFailAlloc_1354_, 9, v_maxHeartbeats_1065_);
lean_ctor_set(v_reuseFailAlloc_1354_, 10, v_quotContext_1066_);
lean_ctor_set(v_reuseFailAlloc_1354_, 11, v_currMacroScope_1067_);
lean_ctor_set(v_reuseFailAlloc_1354_, 12, v_cancelTk_x3f_1069_);
lean_ctor_set(v_reuseFailAlloc_1354_, 13, v_inheritedTraceOptions_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*14, v_diag_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*14 + 1, v_suppressElabErrors_1070_);
v___x_1342_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_nat_dec_le(v_maxSteps_1338_, v_numSteps_1337_);
lean_dec(v_maxSteps_1338_);
if (v___x_1343_ == 0)
{
v___y_1217_ = v_numSteps_1337_;
v___y_1218_ = v___x_1339_;
v___y_1219_ = v_a_783_;
v___y_1220_ = v_a_784_;
v___y_1221_ = v_a_785_;
v___y_1222_ = v_a_786_;
v___y_1223_ = v_a_787_;
v___y_1224_ = v_a_788_;
v___y_1225_ = v_a_789_;
v___y_1226_ = v___x_1342_;
v___y_1227_ = v_a_791_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_numSteps_1337_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_e_u2081_782_);
v___x_1344_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8);
v___x_1345_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_1344_, v_a_788_, v_a_789_, v___x_1342_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v___x_1342_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
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
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v___x_1334_);
lean_del_object(v___x_1073_);
lean_dec_ref(v_inheritedTraceOptions_1071_);
lean_dec(v_cancelTk_x3f_1069_);
lean_dec(v_currMacroScope_1067_);
lean_dec(v_quotContext_1066_);
lean_dec(v_maxHeartbeats_1065_);
lean_dec(v_initHeartbeats_1064_);
lean_dec(v_openDecls_1063_);
lean_dec(v_currNamespace_1062_);
lean_dec(v_ref_1061_);
lean_dec(v_maxRecDepth_1060_);
lean_dec(v_currRecDepth_1059_);
lean_dec_ref(v_options_1058_);
lean_dec_ref(v_fileMap_1057_);
lean_dec_ref(v_fileName_1056_);
lean_dec(v_a_791_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_e_u2081_782_);
v_a_1355_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1335_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1335_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* v_e_u2081_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = lean_sym_simp(v_e_u2081_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* v_00_u03b2_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_1381_, v_x_1382_, v_x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* v_00_u03b2_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_1386_, v_x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* v_00_u03b2_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_1389_, v_x_1390_, v_x_1391_);
lean_dec_ref(v_x_1391_);
lean_dec_ref(v_x_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* v_cls_1393_, lean_object* v_msg_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_1393_, v_msg_1394_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* v_cls_1406_, lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_1406_, v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* v_00_u03b2_1419_, lean_object* v_x_1420_, size_t v_x_1421_, size_t v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_1420_, v_x_1421_, v_x_1422_, v_x_1423_, v_x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
size_t v_x_115819__boxed_1432_; size_t v_x_115820__boxed_1433_; lean_object* v_res_1434_; 
v_x_115819__boxed_1432_ = lean_unbox_usize(v_x_1428_);
lean_dec(v_x_1428_);
v_x_115820__boxed_1433_ = lean_unbox_usize(v_x_1429_);
lean_dec(v_x_1429_);
v_res_1434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_1426_, v_x_1427_, v_x_115819__boxed_1432_, v_x_115820__boxed_1433_, v_x_1430_, v_x_1431_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* v_00_u03b2_1435_, lean_object* v_x_1436_, size_t v_x_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_1436_, v_x_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
size_t v_x_115836__boxed_1444_; lean_object* v_res_1445_; 
v_x_115836__boxed_1444_ = lean_unbox_usize(v_x_1442_);
lean_dec(v_x_1442_);
v_res_1445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_1440_, v_x_1441_, v_x_115836__boxed_1444_, v_x_1443_);
lean_dec_ref(v_x_1443_);
lean_dec_ref(v_x_1441_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1446_, lean_object* v_n_1447_, lean_object* v_k_1448_, lean_object* v_v_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v_n_1447_, v_k_1448_, v_v_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1451_, size_t v_depth_1452_, lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_heq_1455_, lean_object* v_i_1456_, lean_object* v_entries_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_1452_, v_keys_1453_, v_vals_1454_, v_i_1456_, v_entries_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1459_, lean_object* v_depth_1460_, lean_object* v_keys_1461_, lean_object* v_vals_1462_, lean_object* v_heq_1463_, lean_object* v_i_1464_, lean_object* v_entries_1465_){
_start:
{
size_t v_depth_boxed_1466_; lean_object* v_res_1467_; 
v_depth_boxed_1466_ = lean_unbox_usize(v_depth_1460_);
lean_dec(v_depth_1460_);
v_res_1467_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(v_00_u03b2_1459_, v_depth_boxed_1466_, v_keys_1461_, v_vals_1462_, v_heq_1463_, v_i_1464_, v_entries_1465_);
lean_dec_ref(v_vals_1462_);
lean_dec_ref(v_keys_1461_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1468_, lean_object* v_keys_1469_, lean_object* v_vals_1470_, lean_object* v_heq_1471_, lean_object* v_i_1472_, lean_object* v_k_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1469_, v_vals_1470_, v_i_1472_, v_k_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1475_, lean_object* v_keys_1476_, lean_object* v_vals_1477_, lean_object* v_heq_1478_, lean_object* v_i_1479_, lean_object* v_k_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(v_00_u03b2_1475_, v_keys_1476_, v_vals_1477_, v_heq_1478_, v_i_1479_, v_k_1480_);
lean_dec_ref(v_k_1480_);
lean_dec_ref(v_vals_1477_);
lean_dec_ref(v_keys_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1483_, v_x_1484_, v_x_1485_, v_x_1486_);
return v___x_1487_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
