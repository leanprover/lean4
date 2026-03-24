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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "persistent cache hit: "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "transient cache hit: "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "`simp` failed: maximum number of steps exceeded"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5;
LEAN_EXPORT lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_debug_107_ = lean_ctor_get_uint8(v___x_106_, sizeof(void*)*7);
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
lean_dec_ref(v___x_108_);
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
lean_dec_ref(v_e_207_);
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
lean_dec_ref(v_a_225_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* v_cls_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_options_427_; uint8_t v_hasTrace_428_; 
v_options_427_ = lean_ctor_get(v___y_425_, 2);
v_hasTrace_428_ = lean_ctor_get_uint8(v_options_427_, sizeof(void*)*1);
if (v_hasTrace_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_cls_424_);
v___x_429_ = lean_box(v_hasTrace_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
else
{
lean_object* v_inheritedTraceOptions_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_inheritedTraceOptions_431_ = lean_ctor_get(v___y_425_, 13);
v___x_432_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1));
v___x_433_ = l_Lean_Name_append(v___x_432_, v_cls_424_);
v___x_434_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_431_, v_options_427_, v___x_433_);
lean_dec(v___x_433_);
v___x_435_ = lean_box(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* v_cls_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_437_, v___y_438_);
lean_dec_ref(v___y_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* v_cls_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_441_, v___y_449_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* v_cls_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
return v_res_464_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = l_Lean_maxRecDepthErrorMessage;
v___x_471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__4(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__3);
v___x_473_ = l_Lean_MessageData_ofFormat(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__4);
v___x_475_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__2));
v___x_476_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg(lean_object* v_ref_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___closed__5);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_ref_477_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg___boxed(lean_object* v_ref_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg(v_ref_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4(lean_object* v_00_u03b1_485_, lean_object* v_ref_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg(v_ref_486_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___boxed(lean_object* v_00_u03b1_498_, lean_object* v_ref_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4(v_00_u03b1_498_, v_ref_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_post_523_; lean_object* v___x_524_; 
v_post_523_ = lean_ctor_get(v___y_513_, 1);
lean_inc_ref(v_post_523_);
lean_inc(v___y_521_);
lean_inc_ref(v___y_520_);
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
v___x_524_ = lean_apply_11(v_post_523_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, lean_box(0));
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object* v_x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v_x_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3_spec__6___redArg(lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_ks_542_; lean_object* v_vs_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_567_; 
v_ks_542_ = lean_ctor_get(v_x_538_, 0);
v_vs_543_ = lean_ctor_get(v_x_538_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_567_ == 0)
{
v___x_545_ = v_x_538_;
v_isShared_546_ = v_isSharedCheck_567_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_vs_543_);
lean_inc(v_ks_542_);
lean_dec(v_x_538_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_567_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_array_get_size(v_ks_542_);
v___x_548_ = lean_nat_dec_lt(v_x_539_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
lean_dec(v_x_539_);
v___x_549_ = lean_array_push(v_ks_542_, v_x_540_);
v___x_550_ = lean_array_push(v_vs_543_, v_x_541_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_550_);
lean_ctor_set(v___x_545_, 0, v___x_549_);
v___x_552_ = v___x_545_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v_k_x27_554_; uint8_t v___x_555_; 
v_k_x27_554_ = lean_array_fget_borrowed(v_ks_542_, v_x_539_);
v___x_555_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_540_, v_k_x27_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_557_; 
if (v_isShared_546_ == 0)
{
v___x_557_ = v___x_545_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_ks_542_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_vs_543_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_add(v_x_539_, v___x_558_);
lean_dec(v_x_539_);
v_x_538_ = v___x_557_;
v_x_539_ = v___x_559_;
goto _start;
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = lean_array_fset(v_ks_542_, v_x_539_, v_x_540_);
v___x_563_ = lean_array_fset(v_vs_543_, v_x_539_, v_x_541_);
lean_dec(v_x_539_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_563_);
lean_ctor_set(v___x_545_, 0, v___x_562_);
v___x_565_ = v___x_545_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(lean_object* v_n_568_, lean_object* v_k_569_, lean_object* v_v_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3_spec__6___redArg(v_n_568_, v___x_571_, v_k_569_, v_v_570_);
return v___x_572_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; 
v___x_573_ = ((size_t)5ULL);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_shift_left(v___x_574_, v___x_573_);
return v___x_575_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; 
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
v___x_578_ = lean_usize_sub(v___x_577_, v___x_576_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* v_x_580_, size_t v_x_581_, size_t v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v_es_585_; size_t v___x_586_; size_t v___x_587_; size_t v___x_588_; size_t v___x_589_; lean_object* v_j_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_es_585_ = lean_ctor_get(v_x_580_, 0);
v___x_586_ = ((size_t)5ULL);
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1);
v___x_589_ = lean_usize_land(v_x_581_, v___x_588_);
v_j_590_ = lean_usize_to_nat(v___x_589_);
v___x_591_ = lean_array_get_size(v_es_585_);
v___x_592_ = lean_nat_dec_lt(v_j_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v_j_590_);
lean_dec(v_x_584_);
lean_dec_ref(v_x_583_);
return v_x_580_;
}
else
{
lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_629_; 
lean_inc_ref(v_es_585_);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_x_580_, 0);
lean_dec(v_unused_630_);
v___x_594_ = v_x_580_;
v_isShared_595_ = v_isSharedCheck_629_;
goto v_resetjp_593_;
}
else
{
lean_dec(v_x_580_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_629_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_v_596_; lean_object* v___x_597_; lean_object* v_xs_x27_598_; lean_object* v___y_600_; 
v_v_596_ = lean_array_fget(v_es_585_, v_j_590_);
v___x_597_ = lean_box(0);
v_xs_x27_598_ = lean_array_fset(v_es_585_, v_j_590_, v___x_597_);
switch(lean_obj_tag(v_v_596_))
{
case 0:
{
lean_object* v_key_605_; lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_616_; 
v_key_605_ = lean_ctor_get(v_v_596_, 0);
v_val_606_ = lean_ctor_get(v_v_596_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_v_596_);
if (v_isSharedCheck_616_ == 0)
{
v___x_608_ = v_v_596_;
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_inc(v_key_605_);
lean_dec(v_v_596_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
uint8_t v___x_610_; 
v___x_610_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_583_, v_key_605_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_del_object(v___x_608_);
v___x_611_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_605_, v_val_606_, v_x_583_, v_x_584_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
v___y_600_ = v___x_612_;
goto v___jp_599_;
}
else
{
lean_object* v___x_614_; 
lean_dec(v_val_606_);
lean_dec(v_key_605_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v_x_584_);
lean_ctor_set(v___x_608_, 0, v_x_583_);
v___x_614_ = v___x_608_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_x_583_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_x_584_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v___y_600_ = v___x_614_;
goto v___jp_599_;
}
}
}
}
case 1:
{
lean_object* v_node_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_627_; 
v_node_617_ = lean_ctor_get(v_v_596_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_v_596_);
if (v_isSharedCheck_627_ == 0)
{
v___x_619_ = v_v_596_;
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_node_617_);
lean_dec(v_v_596_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_621_ = lean_usize_shift_right(v_x_581_, v___x_586_);
v___x_622_ = lean_usize_add(v_x_582_, v___x_587_);
v___x_623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_617_, v___x_621_, v___x_622_, v_x_583_, v_x_584_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_623_);
v___x_625_ = v___x_619_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
v___y_600_ = v___x_625_;
goto v___jp_599_;
}
}
}
default: 
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_x_583_);
lean_ctor_set(v___x_628_, 1, v_x_584_);
v___y_600_ = v___x_628_;
goto v___jp_599_;
}
}
v___jp_599_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_array_fset(v_xs_x27_598_, v_j_590_, v___y_600_);
lean_dec(v_j_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_601_);
v___x_603_ = v___x_594_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
else
{
lean_object* v_ks_631_; lean_object* v_vs_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_652_; 
v_ks_631_ = lean_ctor_get(v_x_580_, 0);
v_vs_632_ = lean_ctor_get(v_x_580_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_652_ == 0)
{
v___x_634_ = v_x_580_;
v_isShared_635_ = v_isSharedCheck_652_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_vs_632_);
lean_inc(v_ks_631_);
lean_dec(v_x_580_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_652_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_ks_631_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_vs_632_);
v___x_637_ = v_reuseFailAlloc_651_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v_newNode_638_; uint8_t v___y_640_; size_t v___x_646_; uint8_t v___x_647_; 
v_newNode_638_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v___x_637_, v_x_583_, v_x_584_);
v___x_646_ = ((size_t)7ULL);
v___x_647_ = lean_usize_dec_le(v___x_646_, v_x_582_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_648_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_638_);
v___x_649_ = lean_unsigned_to_nat(4u);
v___x_650_ = lean_nat_dec_lt(v___x_648_, v___x_649_);
lean_dec(v___x_648_);
v___y_640_ = v___x_650_;
goto v___jp_639_;
}
else
{
v___y_640_ = v___x_647_;
goto v___jp_639_;
}
v___jp_639_:
{
if (v___y_640_ == 0)
{
lean_object* v_ks_641_; lean_object* v_vs_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_ks_641_ = lean_ctor_get(v_newNode_638_, 0);
lean_inc_ref(v_ks_641_);
v_vs_642_ = lean_ctor_get(v_newNode_638_, 1);
lean_inc_ref(v_vs_642_);
lean_dec_ref(v_newNode_638_);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2);
v___x_645_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___redArg(v_x_582_, v_ks_641_, v_vs_642_, v___x_643_, v___x_644_);
lean_dec_ref(v_vs_642_);
lean_dec_ref(v_ks_641_);
return v___x_645_;
}
else
{
return v_newNode_638_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___redArg(size_t v_depth_653_, lean_object* v_keys_654_, lean_object* v_vals_655_, lean_object* v_i_656_, lean_object* v_entries_657_){
_start:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_array_get_size(v_keys_654_);
v___x_659_ = lean_nat_dec_lt(v_i_656_, v___x_658_);
if (v___x_659_ == 0)
{
lean_dec(v_i_656_);
return v_entries_657_;
}
else
{
lean_object* v_k_660_; lean_object* v_v_661_; uint64_t v___x_662_; size_t v_h_663_; size_t v___x_664_; lean_object* v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v_h_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_k_660_ = lean_array_fget_borrowed(v_keys_654_, v_i_656_);
v_v_661_ = lean_array_fget_borrowed(v_vals_655_, v_i_656_);
v___x_662_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_660_);
v_h_663_ = lean_uint64_to_usize(v___x_662_);
v___x_664_ = ((size_t)5ULL);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_sub(v_depth_653_, v___x_666_);
v___x_668_ = lean_usize_mul(v___x_664_, v___x_667_);
v_h_669_ = lean_usize_shift_right(v_h_663_, v___x_668_);
v___x_670_ = lean_nat_add(v_i_656_, v___x_665_);
lean_dec(v_i_656_);
lean_inc(v_v_661_);
lean_inc(v_k_660_);
v___x_671_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_657_, v_h_669_, v_depth_653_, v_k_660_, v_v_661_);
v_i_656_ = v___x_670_;
v_entries_657_ = v___x_671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_depth_673_, lean_object* v_keys_674_, lean_object* v_vals_675_, lean_object* v_i_676_, lean_object* v_entries_677_){
_start:
{
size_t v_depth_boxed_678_; lean_object* v_res_679_; 
v_depth_boxed_678_ = lean_unbox_usize(v_depth_673_);
lean_dec(v_depth_673_);
v_res_679_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___redArg(v_depth_boxed_678_, v_keys_674_, v_vals_675_, v_i_676_, v_entries_677_);
lean_dec_ref(v_vals_675_);
lean_dec_ref(v_keys_674_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
size_t v_x_111461__boxed_685_; size_t v_x_111462__boxed_686_; lean_object* v_res_687_; 
v_x_111461__boxed_685_ = lean_unbox_usize(v_x_681_);
lean_dec(v_x_681_);
v_x_111462__boxed_686_ = lean_unbox_usize(v_x_682_);
lean_dec(v_x_682_);
v_res_687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_680_, v_x_111461__boxed_685_, v_x_111462__boxed_686_, v_x_683_, v_x_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* v_x_688_, lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
uint64_t v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
v___x_691_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_689_);
v___x_692_ = lean_uint64_to_usize(v___x_691_);
v___x_693_ = ((size_t)1ULL);
v___x_694_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_688_, v___x_692_, v___x_693_, v_x_689_, v_x_690_);
return v___x_694_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_695_; double v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_float_of_nat(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(lean_object* v_cls_700_, lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_ref_707_; lean_object* v___x_708_; lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_753_; 
v_ref_707_ = lean_ctor_get(v___y_704_, 5);
v___x_708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_753_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_753_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_753_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v_traceState_714_; lean_object* v_env_715_; lean_object* v_nextMacroScope_716_; lean_object* v_ngen_717_; lean_object* v_auxDeclNGen_718_; lean_object* v_cache_719_; lean_object* v_messages_720_; lean_object* v_infoState_721_; lean_object* v_snapshotTasks_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_752_; 
v___x_713_ = lean_st_ref_take(v___y_705_);
v_traceState_714_ = lean_ctor_get(v___x_713_, 4);
v_env_715_ = lean_ctor_get(v___x_713_, 0);
v_nextMacroScope_716_ = lean_ctor_get(v___x_713_, 1);
v_ngen_717_ = lean_ctor_get(v___x_713_, 2);
v_auxDeclNGen_718_ = lean_ctor_get(v___x_713_, 3);
v_cache_719_ = lean_ctor_get(v___x_713_, 5);
v_messages_720_ = lean_ctor_get(v___x_713_, 6);
v_infoState_721_ = lean_ctor_get(v___x_713_, 7);
v_snapshotTasks_722_ = lean_ctor_get(v___x_713_, 8);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_752_ == 0)
{
v___x_724_ = v___x_713_;
v_isShared_725_ = v_isSharedCheck_752_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snapshotTasks_722_);
lean_inc(v_infoState_721_);
lean_inc(v_messages_720_);
lean_inc(v_cache_719_);
lean_inc(v_traceState_714_);
lean_inc(v_auxDeclNGen_718_);
lean_inc(v_ngen_717_);
lean_inc(v_nextMacroScope_716_);
lean_inc(v_env_715_);
lean_dec(v___x_713_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_752_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
uint64_t v_tid_726_; lean_object* v_traces_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_751_; 
v_tid_726_ = lean_ctor_get_uint64(v_traceState_714_, sizeof(void*)*1);
v_traces_727_ = lean_ctor_get(v_traceState_714_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_traceState_714_);
if (v_isSharedCheck_751_ == 0)
{
v___x_729_ = v_traceState_714_;
v_isShared_730_ = v_isSharedCheck_751_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_traces_727_);
lean_dec(v_traceState_714_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_751_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; double v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_731_ = lean_box(0);
v___x_732_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0);
v___x_733_ = 0;
v___x_734_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1));
v___x_735_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_735_, 0, v_cls_700_);
lean_ctor_set(v___x_735_, 1, v___x_731_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
lean_ctor_set_float(v___x_735_, sizeof(void*)*3, v___x_732_);
lean_ctor_set_float(v___x_735_, sizeof(void*)*3 + 8, v___x_732_);
lean_ctor_set_uint8(v___x_735_, sizeof(void*)*3 + 16, v___x_733_);
v___x_736_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2));
v___x_737_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v_a_709_);
lean_ctor_set(v___x_737_, 2, v___x_736_);
lean_inc(v_ref_707_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_ref_707_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_PersistentArray_push___redArg(v_traces_727_, v___x_738_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_739_);
v___x_741_ = v___x_729_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_739_);
lean_ctor_set_uint64(v_reuseFailAlloc_750_, sizeof(void*)*1, v_tid_726_);
v___x_741_ = v_reuseFailAlloc_750_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 4, v___x_741_);
v___x_743_ = v___x_724_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_env_715_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_nextMacroScope_716_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_ngen_717_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_auxDeclNGen_718_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_749_, 5, v_cache_719_);
lean_ctor_set(v_reuseFailAlloc_749_, 6, v_messages_720_);
lean_ctor_set(v_reuseFailAlloc_749_, 7, v_infoState_721_);
lean_ctor_set(v_reuseFailAlloc_749_, 8, v_snapshotTasks_722_);
v___x_743_ = v_reuseFailAlloc_749_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_744_ = lean_st_ref_set(v___y_705_, v___x_743_);
v___x_745_ = lean_box(0);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_745_);
v___x_747_ = v___x_711_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(lean_object* v_cls_754_, lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_cls_754_, v_msg_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___redArg(lean_object* v_keys_762_, lean_object* v_vals_763_, lean_object* v_i_764_, lean_object* v_k_765_){
_start:
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_array_get_size(v_keys_762_);
v___x_767_ = lean_nat_dec_lt(v_i_764_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec(v_i_764_);
v___x_768_ = lean_box(0);
return v___x_768_;
}
else
{
lean_object* v_k_x27_769_; uint8_t v___x_770_; 
v_k_x27_769_ = lean_array_fget_borrowed(v_keys_762_, v_i_764_);
v___x_770_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_765_, v_k_x27_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_i_764_, v___x_771_);
lean_dec(v_i_764_);
v_i_764_ = v___x_772_;
goto _start;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_array_fget_borrowed(v_vals_763_, v_i_764_);
lean_dec(v_i_764_);
lean_inc(v___x_774_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___redArg___boxed(lean_object* v_keys_776_, lean_object* v_vals_777_, lean_object* v_i_778_, lean_object* v_k_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___redArg(v_keys_776_, v_vals_777_, v_i_778_, v_k_779_);
lean_dec_ref(v_k_779_);
lean_dec_ref(v_vals_777_);
lean_dec_ref(v_keys_776_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* v_x_781_, size_t v_x_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v_es_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_805_; 
v_es_784_ = lean_ctor_get(v_x_781_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_x_781_);
if (v_isSharedCheck_805_ == 0)
{
v___x_786_ = v_x_781_;
v_isShared_787_ = v_isSharedCheck_805_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_es_784_);
lean_dec(v_x_781_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_805_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v_j_792_; lean_object* v___x_793_; 
v___x_788_ = lean_box(2);
v___x_789_ = ((size_t)5ULL);
v___x_790_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1);
v___x_791_ = lean_usize_land(v_x_782_, v___x_790_);
v_j_792_ = lean_usize_to_nat(v___x_791_);
v___x_793_ = lean_array_get(v___x_788_, v_es_784_, v_j_792_);
lean_dec(v_j_792_);
lean_dec_ref(v_es_784_);
switch(lean_obj_tag(v___x_793_))
{
case 0:
{
lean_object* v_key_794_; lean_object* v_val_795_; uint8_t v___x_796_; 
v_key_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_key_794_);
v_val_795_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_val_795_);
lean_dec_ref(v___x_793_);
v___x_796_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_783_, v_key_794_);
lean_dec(v_key_794_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
lean_dec(v_val_795_);
lean_del_object(v___x_786_);
v___x_797_ = lean_box(0);
return v___x_797_;
}
else
{
lean_object* v___x_799_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 1);
lean_ctor_set(v___x_786_, 0, v_val_795_);
v___x_799_ = v___x_786_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_val_795_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
case 1:
{
lean_object* v_node_801_; size_t v___x_802_; 
lean_del_object(v___x_786_);
v_node_801_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_node_801_);
lean_dec_ref(v___x_793_);
v___x_802_ = lean_usize_shift_right(v_x_782_, v___x_789_);
v_x_781_ = v_node_801_;
v_x_782_ = v___x_802_;
goto _start;
}
default: 
{
lean_object* v___x_804_; 
lean_del_object(v___x_786_);
v___x_804_ = lean_box(0);
return v___x_804_;
}
}
}
}
else
{
lean_object* v_ks_806_; lean_object* v_vs_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_ks_806_ = lean_ctor_get(v_x_781_, 0);
lean_inc_ref(v_ks_806_);
v_vs_807_ = lean_ctor_get(v_x_781_, 1);
lean_inc_ref(v_vs_807_);
lean_dec_ref(v_x_781_);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___redArg(v_ks_806_, v_vs_807_, v___x_808_, v_x_783_);
lean_dec_ref(v_vs_807_);
lean_dec_ref(v_ks_806_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
size_t v_x_111762__boxed_813_; lean_object* v_res_814_; 
v_x_111762__boxed_813_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_res_814_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_810_, v_x_111762__boxed_813_, v_x_812_);
lean_dec_ref(v_x_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
uint64_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v___x_817_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_816_);
v___x_818_ = lean_uint64_to_usize(v___x_817_);
v___x_819_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_815_, v___x_818_, v_x_816_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_820_, v_x_821_);
lean_dec_ref(v_x_821_);
return v_res_822_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4));
v___x_831_ = l_Lean_stringToMessageData(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* lean_sym_simp(lean_object* v_e_u2081_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___y_844_; lean_object* v___y_845_; uint8_t v___y_846_; lean_object* v___y_878_; lean_object* v___y_879_; uint8_t v___y_880_; lean_object* v___y_881_; uint8_t v___y_882_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; uint8_t v___y_888_; uint8_t v___y_889_; lean_object* v_e_u2082_892_; lean_object* v_h_u2081_893_; uint8_t v_cd_u2081_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; uint8_t v___y_1012_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; uint8_t v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; uint8_t v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; uint8_t v___y_1027_; lean_object* v___y_1029_; uint8_t v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; uint8_t v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v_a_1040_; lean_object* v___y_1044_; uint8_t v___y_1045_; uint8_t v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; uint8_t v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; uint8_t v___y_1058_; lean_object* v___y_1061_; uint8_t v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; uint8_t v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1075_; lean_object* v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; uint8_t v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; uint8_t v___y_1090_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v_fileName_1106_; lean_object* v_fileMap_1107_; lean_object* v_options_1108_; lean_object* v_currRecDepth_1109_; lean_object* v_maxRecDepth_1110_; lean_object* v_ref_1111_; lean_object* v_currNamespace_1112_; lean_object* v_openDecls_1113_; lean_object* v_initHeartbeats_1114_; lean_object* v_maxHeartbeats_1115_; lean_object* v_quotContext_1116_; lean_object* v_currMacroScope_1117_; uint8_t v_diag_1118_; lean_object* v_cancelTk_x3f_1119_; uint8_t v_suppressElabErrors_1120_; lean_object* v_inheritedTraceOptions_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1400_; 
v_fileName_1106_ = lean_ctor_get(v_a_840_, 0);
v_fileMap_1107_ = lean_ctor_get(v_a_840_, 1);
v_options_1108_ = lean_ctor_get(v_a_840_, 2);
v_currRecDepth_1109_ = lean_ctor_get(v_a_840_, 3);
v_maxRecDepth_1110_ = lean_ctor_get(v_a_840_, 4);
v_ref_1111_ = lean_ctor_get(v_a_840_, 5);
v_currNamespace_1112_ = lean_ctor_get(v_a_840_, 6);
v_openDecls_1113_ = lean_ctor_get(v_a_840_, 7);
v_initHeartbeats_1114_ = lean_ctor_get(v_a_840_, 8);
v_maxHeartbeats_1115_ = lean_ctor_get(v_a_840_, 9);
v_quotContext_1116_ = lean_ctor_get(v_a_840_, 10);
v_currMacroScope_1117_ = lean_ctor_get(v_a_840_, 11);
v_diag_1118_ = lean_ctor_get_uint8(v_a_840_, sizeof(void*)*14);
v_cancelTk_x3f_1119_ = lean_ctor_get(v_a_840_, 12);
v_suppressElabErrors_1120_ = lean_ctor_get_uint8(v_a_840_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1121_ = lean_ctor_get(v_a_840_, 13);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_a_840_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1123_ = v_a_840_;
v_isShared_1124_ = v_isSharedCheck_1400_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_inheritedTraceOptions_1121_);
lean_inc(v_cancelTk_x3f_1119_);
lean_inc(v_currMacroScope_1117_);
lean_inc(v_quotContext_1116_);
lean_inc(v_maxHeartbeats_1115_);
lean_inc(v_initHeartbeats_1114_);
lean_inc(v_openDecls_1113_);
lean_inc(v_currNamespace_1112_);
lean_inc(v_ref_1111_);
lean_inc(v_maxRecDepth_1110_);
lean_inc(v_currRecDepth_1109_);
lean_inc(v_options_1108_);
lean_inc(v_fileMap_1107_);
lean_inc(v_fileName_1106_);
lean_dec(v_a_840_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1400_;
goto v_resetjp_1122_;
}
v___jp_843_:
{
if (v___y_846_ == 0)
{
lean_object* v___x_847_; lean_object* v_numSteps_848_; lean_object* v_persistentCache_849_; lean_object* v_transientCache_850_; lean_object* v_funext_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_861_; 
v___x_847_ = lean_st_ref_take(v___y_844_);
v_numSteps_848_ = lean_ctor_get(v___x_847_, 0);
v_persistentCache_849_ = lean_ctor_get(v___x_847_, 1);
v_transientCache_850_ = lean_ctor_get(v___x_847_, 2);
v_funext_851_ = lean_ctor_get(v___x_847_, 3);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_861_ == 0)
{
v___x_853_ = v___x_847_;
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_funext_851_);
lean_inc(v_transientCache_850_);
lean_inc(v_persistentCache_849_);
lean_inc(v_numSteps_848_);
lean_dec(v___x_847_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
lean_inc_ref(v___y_845_);
v___x_855_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_849_, v_e_u2081_832_, v___y_845_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_numSteps_848_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_transientCache_850_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v_funext_851_);
v___x_857_ = v_reuseFailAlloc_860_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_st_ref_set(v___y_844_, v___x_857_);
lean_dec(v___y_844_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___y_845_);
return v___x_859_;
}
}
}
else
{
lean_object* v___x_862_; lean_object* v_numSteps_863_; lean_object* v_persistentCache_864_; lean_object* v_transientCache_865_; lean_object* v_funext_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_876_; 
v___x_862_ = lean_st_ref_take(v___y_844_);
v_numSteps_863_ = lean_ctor_get(v___x_862_, 0);
v_persistentCache_864_ = lean_ctor_get(v___x_862_, 1);
v_transientCache_865_ = lean_ctor_get(v___x_862_, 2);
v_funext_866_ = lean_ctor_get(v___x_862_, 3);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_876_ == 0)
{
v___x_868_ = v___x_862_;
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_funext_866_);
lean_inc(v_transientCache_865_);
lean_inc(v_persistentCache_864_);
lean_inc(v_numSteps_863_);
lean_dec(v___x_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_inc_ref(v___y_845_);
v___x_870_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_865_, v_e_u2081_832_, v___y_845_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 2, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_numSteps_863_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_persistentCache_864_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_funext_866_);
v___x_872_ = v_reuseFailAlloc_875_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_st_ref_set(v___y_844_, v___x_872_);
lean_dec(v___y_844_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___y_845_);
return v___x_874_;
}
}
}
}
v___jp_877_:
{
lean_object* v___x_883_; 
v___x_883_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_883_, 0, v___y_881_);
lean_ctor_set(v___x_883_, 1, v___y_878_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*2, v___y_880_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*2 + 1, v___y_882_);
v___y_844_ = v___y_879_;
v___y_845_ = v___x_883_;
v___y_846_ = v___y_882_;
goto v___jp_843_;
}
v___jp_884_:
{
lean_object* v___x_890_; 
v___x_890_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_890_, 0, v___y_886_);
lean_ctor_set(v___x_890_, 1, v___y_887_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*2, v___y_888_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*2 + 1, v___y_889_);
v___y_844_ = v___y_885_;
v___y_845_ = v___x_890_;
v___y_846_ = v___y_889_;
goto v___jp_843_;
}
v___jp_891_:
{
lean_object* v___x_904_; 
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
lean_inc(v___y_899_);
lean_inc(v___y_897_);
lean_inc_ref(v_e_u2082_892_);
v___x_904_ = lean_sym_simp(v_e_u2082_892_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v___x_904_);
if (lean_obj_tag(v_a_905_) == 0)
{
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
if (v_cd_u2081_894_ == 0)
{
uint8_t v_done_906_; uint8_t v_contextDependent_907_; 
v_done_906_ = lean_ctor_get_uint8(v_a_905_, 0);
v_contextDependent_907_ = lean_ctor_get_uint8(v_a_905_, 1);
lean_dec_ref(v_a_905_);
v___y_885_ = v___y_897_;
v___y_886_ = v_e_u2082_892_;
v___y_887_ = v_h_u2081_893_;
v___y_888_ = v_done_906_;
v___y_889_ = v_contextDependent_907_;
goto v___jp_884_;
}
else
{
uint8_t v_done_908_; 
v_done_908_ = lean_ctor_get_uint8(v_a_905_, 0);
lean_dec_ref(v_a_905_);
v___y_885_ = v___y_897_;
v___y_886_ = v_e_u2082_892_;
v___y_887_ = v_h_u2081_893_;
v___y_888_ = v_done_908_;
v___y_889_ = v_cd_u2081_894_;
goto v___jp_884_;
}
}
else
{
lean_object* v_e_x27_909_; lean_object* v_proof_910_; uint8_t v_done_911_; uint8_t v_contextDependent_912_; lean_object* v___x_913_; 
v_e_x27_909_ = lean_ctor_get(v_a_905_, 0);
lean_inc_ref(v_e_x27_909_);
v_proof_910_ = lean_ctor_get(v_a_905_, 1);
lean_inc_ref(v_proof_910_);
v_done_911_ = lean_ctor_get_uint8(v_a_905_, sizeof(void*)*2);
v_contextDependent_912_ = lean_ctor_get_uint8(v_a_905_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_905_);
lean_inc_ref(v_e_x27_909_);
lean_inc_ref(v_e_u2081_832_);
v___x_913_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_832_, v_e_u2082_892_, v_h_u2081_893_, v_e_x27_909_, v_proof_910_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
if (lean_obj_tag(v___x_913_) == 0)
{
if (v_cd_u2081_894_ == 0)
{
lean_object* v_a_914_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
v___y_878_ = v_a_914_;
v___y_879_ = v___y_897_;
v___y_880_ = v_done_911_;
v___y_881_ = v_e_x27_909_;
v___y_882_ = v_contextDependent_912_;
goto v___jp_877_;
}
else
{
lean_object* v_a_915_; 
v_a_915_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_913_);
v___y_878_ = v_a_915_;
v___y_879_ = v___y_897_;
v___y_880_ = v_done_911_;
v___y_881_ = v_e_x27_909_;
v___y_882_ = v_cd_u2081_894_;
goto v___jp_877_;
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_e_x27_909_);
lean_dec(v___y_897_);
lean_dec_ref(v_e_u2081_832_);
v_a_916_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_913_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_913_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
else
{
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec(v___y_897_);
lean_dec_ref(v_h_u2081_893_);
lean_dec_ref(v_e_u2082_892_);
lean_dec_ref(v_e_u2081_832_);
return v___x_904_;
}
}
v___jp_924_:
{
if (lean_obj_tag(v___y_934_) == 0)
{
uint8_t v_contextDependent_935_; 
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
v_contextDependent_935_ = lean_ctor_get_uint8(v___y_934_, 1);
if (v_contextDependent_935_ == 0)
{
lean_object* v___x_936_; lean_object* v_numSteps_937_; lean_object* v_persistentCache_938_; lean_object* v_transientCache_939_; lean_object* v_funext_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_950_; 
v___x_936_ = lean_st_ref_take(v___y_929_);
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
lean_inc_ref(v___y_934_);
v___x_944_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_938_, v_e_u2081_832_, v___y_934_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_numSteps_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_transientCache_939_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_funext_940_);
v___x_946_ = v_reuseFailAlloc_949_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_st_ref_set(v___y_929_, v___x_946_);
lean_dec(v___y_929_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___y_934_);
return v___x_948_;
}
}
}
else
{
lean_object* v___x_951_; lean_object* v_numSteps_952_; lean_object* v_persistentCache_953_; lean_object* v_transientCache_954_; lean_object* v_funext_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_965_; 
v___x_951_ = lean_st_ref_take(v___y_929_);
v_numSteps_952_ = lean_ctor_get(v___x_951_, 0);
v_persistentCache_953_ = lean_ctor_get(v___x_951_, 1);
v_transientCache_954_ = lean_ctor_get(v___x_951_, 2);
v_funext_955_ = lean_ctor_get(v___x_951_, 3);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_965_ == 0)
{
v___x_957_ = v___x_951_;
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_funext_955_);
lean_inc(v_transientCache_954_);
lean_inc(v_persistentCache_953_);
lean_inc(v_numSteps_952_);
lean_dec(v___x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_inc_ref(v___y_934_);
v___x_959_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_954_, v_e_u2081_832_, v___y_934_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 2, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_numSteps_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_persistentCache_953_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_funext_955_);
v___x_961_ = v_reuseFailAlloc_964_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_st_ref_set(v___y_929_, v___x_961_);
lean_dec(v___y_929_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___y_934_);
return v___x_963_;
}
}
}
}
else
{
uint8_t v_done_966_; 
v_done_966_ = lean_ctor_get_uint8(v___y_934_, sizeof(void*)*2);
if (v_done_966_ == 0)
{
lean_object* v_e_x27_967_; lean_object* v_proof_968_; uint8_t v_contextDependent_969_; 
v_e_x27_967_ = lean_ctor_get(v___y_934_, 0);
lean_inc_ref(v_e_x27_967_);
v_proof_968_ = lean_ctor_get(v___y_934_, 1);
lean_inc_ref(v_proof_968_);
v_contextDependent_969_ = lean_ctor_get_uint8(v___y_934_, sizeof(void*)*2 + 1);
lean_dec_ref(v___y_934_);
v_e_u2082_892_ = v_e_x27_967_;
v_h_u2081_893_ = v_proof_968_;
v_cd_u2081_894_ = v_contextDependent_969_;
v___y_895_ = v___y_931_;
v___y_896_ = v___y_933_;
v___y_897_ = v___y_929_;
v___y_898_ = v___y_925_;
v___y_899_ = v___y_932_;
v___y_900_ = v___y_927_;
v___y_901_ = v___y_926_;
v___y_902_ = v___y_928_;
v___y_903_ = v___y_930_;
goto v___jp_891_;
}
else
{
uint8_t v_contextDependent_970_; 
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
v_contextDependent_970_ = lean_ctor_get_uint8(v___y_934_, sizeof(void*)*2 + 1);
if (v_contextDependent_970_ == 0)
{
lean_object* v___x_971_; lean_object* v_numSteps_972_; lean_object* v_persistentCache_973_; lean_object* v_transientCache_974_; lean_object* v_funext_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_985_; 
v___x_971_ = lean_st_ref_take(v___y_929_);
v_numSteps_972_ = lean_ctor_get(v___x_971_, 0);
v_persistentCache_973_ = lean_ctor_get(v___x_971_, 1);
v_transientCache_974_ = lean_ctor_get(v___x_971_, 2);
v_funext_975_ = lean_ctor_get(v___x_971_, 3);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_985_ == 0)
{
v___x_977_ = v___x_971_;
v_isShared_978_ = v_isSharedCheck_985_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_funext_975_);
lean_inc(v_transientCache_974_);
lean_inc(v_persistentCache_973_);
lean_inc(v_numSteps_972_);
lean_dec(v___x_971_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_985_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_inc_ref(v___y_934_);
v___x_979_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_973_, v_e_u2081_832_, v___y_934_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v___x_979_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_numSteps_972_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_transientCache_974_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_funext_975_);
v___x_981_ = v_reuseFailAlloc_984_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_st_ref_set(v___y_929_, v___x_981_);
lean_dec(v___y_929_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___y_934_);
return v___x_983_;
}
}
}
else
{
lean_object* v___x_986_; lean_object* v_numSteps_987_; lean_object* v_persistentCache_988_; lean_object* v_transientCache_989_; lean_object* v_funext_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1000_; 
v___x_986_ = lean_st_ref_take(v___y_929_);
v_numSteps_987_ = lean_ctor_get(v___x_986_, 0);
v_persistentCache_988_ = lean_ctor_get(v___x_986_, 1);
v_transientCache_989_ = lean_ctor_get(v___x_986_, 2);
v_funext_990_ = lean_ctor_get(v___x_986_, 3);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_992_ = v___x_986_;
v_isShared_993_ = v_isSharedCheck_1000_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_funext_990_);
lean_inc(v_transientCache_989_);
lean_inc(v_persistentCache_988_);
lean_inc(v_numSteps_987_);
lean_dec(v___x_986_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1000_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
lean_inc_ref(v___y_934_);
v___x_994_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_989_, v_e_u2081_832_, v___y_934_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 2, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_numSteps_987_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_persistentCache_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_funext_990_);
v___x_996_ = v_reuseFailAlloc_999_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_st_ref_set(v___y_929_, v___x_996_);
lean_dec(v___y_929_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___y_934_);
return v___x_998_;
}
}
}
}
}
}
v___jp_1001_:
{
if (v___y_1012_ == 0)
{
v___y_925_ = v___y_1002_;
v___y_926_ = v___y_1003_;
v___y_927_ = v___y_1005_;
v___y_928_ = v___y_1006_;
v___y_929_ = v___y_1007_;
v___y_930_ = v___y_1009_;
v___y_931_ = v___y_1008_;
v___y_932_ = v___y_1010_;
v___y_933_ = v___y_1011_;
v___y_934_ = v___y_1004_;
goto v___jp_924_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1004_);
v___y_925_ = v___y_1002_;
v___y_926_ = v___y_1003_;
v___y_927_ = v___y_1005_;
v___y_928_ = v___y_1006_;
v___y_929_ = v___y_1007_;
v___y_930_ = v___y_1009_;
v___y_931_ = v___y_1008_;
v___y_932_ = v___y_1010_;
v___y_933_ = v___y_1011_;
v___y_934_ = v___x_1013_;
goto v___jp_924_;
}
}
v___jp_1014_:
{
if (v___y_1027_ == 0)
{
v___y_1002_ = v___y_1022_;
v___y_1003_ = v___y_1015_;
v___y_1004_ = v___y_1016_;
v___y_1005_ = v___y_1024_;
v___y_1006_ = v___y_1017_;
v___y_1007_ = v___y_1025_;
v___y_1008_ = v___y_1019_;
v___y_1009_ = v___y_1026_;
v___y_1010_ = v___y_1020_;
v___y_1011_ = v___y_1021_;
v___y_1012_ = v___y_1023_;
goto v___jp_1001_;
}
else
{
v___y_1002_ = v___y_1022_;
v___y_1003_ = v___y_1015_;
v___y_1004_ = v___y_1016_;
v___y_1005_ = v___y_1024_;
v___y_1006_ = v___y_1017_;
v___y_1007_ = v___y_1025_;
v___y_1008_ = v___y_1019_;
v___y_1009_ = v___y_1026_;
v___y_1010_ = v___y_1020_;
v___y_1011_ = v___y_1021_;
v___y_1012_ = v___y_1018_;
goto v___jp_1001_;
}
}
v___jp_1028_:
{
if (v___y_1030_ == 0)
{
v___y_925_ = v___y_1029_;
v___y_926_ = v___y_1031_;
v___y_927_ = v___y_1032_;
v___y_928_ = v___y_1034_;
v___y_929_ = v___y_1035_;
v___y_930_ = v___y_1037_;
v___y_931_ = v___y_1036_;
v___y_932_ = v___y_1038_;
v___y_933_ = v___y_1039_;
v___y_934_ = v_a_1040_;
goto v___jp_924_;
}
else
{
if (lean_obj_tag(v_a_1040_) == 0)
{
uint8_t v_contextDependent_1041_; 
v_contextDependent_1041_ = lean_ctor_get_uint8(v_a_1040_, 1);
v___y_1015_ = v___y_1031_;
v___y_1016_ = v_a_1040_;
v___y_1017_ = v___y_1034_;
v___y_1018_ = v___y_1033_;
v___y_1019_ = v___y_1036_;
v___y_1020_ = v___y_1038_;
v___y_1021_ = v___y_1039_;
v___y_1022_ = v___y_1029_;
v___y_1023_ = v___y_1030_;
v___y_1024_ = v___y_1032_;
v___y_1025_ = v___y_1035_;
v___y_1026_ = v___y_1037_;
v___y_1027_ = v_contextDependent_1041_;
goto v___jp_1014_;
}
else
{
uint8_t v_contextDependent_1042_; 
v_contextDependent_1042_ = lean_ctor_get_uint8(v_a_1040_, sizeof(void*)*2 + 1);
v___y_1015_ = v___y_1031_;
v___y_1016_ = v_a_1040_;
v___y_1017_ = v___y_1034_;
v___y_1018_ = v___y_1033_;
v___y_1019_ = v___y_1036_;
v___y_1020_ = v___y_1038_;
v___y_1021_ = v___y_1039_;
v___y_1022_ = v___y_1029_;
v___y_1023_ = v___y_1030_;
v___y_1024_ = v___y_1032_;
v___y_1025_ = v___y_1035_;
v___y_1026_ = v___y_1037_;
v___y_1027_ = v_contextDependent_1042_;
goto v___jp_1014_;
}
}
}
v___jp_1043_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1059_, 0, v___y_1052_);
lean_ctor_set(v___x_1059_, 1, v___y_1051_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*2, v___y_1045_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*2 + 1, v___y_1058_);
v___y_1029_ = v___y_1053_;
v___y_1030_ = v___y_1054_;
v___y_1031_ = v___y_1044_;
v___y_1032_ = v___y_1055_;
v___y_1033_ = v___y_1046_;
v___y_1034_ = v___y_1047_;
v___y_1035_ = v___y_1056_;
v___y_1036_ = v___y_1048_;
v___y_1037_ = v___y_1057_;
v___y_1038_ = v___y_1049_;
v___y_1039_ = v___y_1050_;
v_a_1040_ = v___x_1059_;
goto v___jp_1028_;
}
v___jp_1060_:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1076_, 0, v___y_1068_);
lean_ctor_set(v___x_1076_, 1, v___y_1074_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*2, v___y_1066_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*2 + 1, v___y_1075_);
v___y_1029_ = v___y_1069_;
v___y_1030_ = v___y_1070_;
v___y_1031_ = v___y_1061_;
v___y_1032_ = v___y_1071_;
v___y_1033_ = v___y_1062_;
v___y_1034_ = v___y_1063_;
v___y_1035_ = v___y_1072_;
v___y_1036_ = v___y_1064_;
v___y_1037_ = v___y_1073_;
v___y_1038_ = v___y_1065_;
v___y_1039_ = v___y_1067_;
v_a_1040_ = v___x_1076_;
goto v___jp_1028_;
}
v___jp_1077_:
{
if (v___y_1090_ == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1078_);
v___y_1029_ = v___y_1085_;
v___y_1030_ = v___y_1086_;
v___y_1031_ = v___y_1079_;
v___y_1032_ = v___y_1087_;
v___y_1033_ = v___y_1080_;
v___y_1034_ = v___y_1081_;
v___y_1035_ = v___y_1088_;
v___y_1036_ = v___y_1082_;
v___y_1037_ = v___y_1089_;
v___y_1038_ = v___y_1083_;
v___y_1039_ = v___y_1084_;
v_a_1040_ = v___x_1091_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v___y_1085_;
v___y_1030_ = v___y_1086_;
v___y_1031_ = v___y_1079_;
v___y_1032_ = v___y_1087_;
v___y_1033_ = v___y_1080_;
v___y_1034_ = v___y_1081_;
v___y_1035_ = v___y_1088_;
v___y_1036_ = v___y_1082_;
v___y_1037_ = v___y_1089_;
v___y_1038_ = v___y_1083_;
v___y_1039_ = v___y_1084_;
v_a_1040_ = v___y_1078_;
goto v___jp_1028_;
}
}
v___jp_1092_:
{
if (lean_obj_tag(v___y_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___y_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___y_1104_);
v___y_1029_ = v___y_1093_;
v___y_1030_ = v___y_1094_;
v___y_1031_ = v___y_1095_;
v___y_1032_ = v___y_1096_;
v___y_1033_ = v___y_1098_;
v___y_1034_ = v___y_1097_;
v___y_1035_ = v___y_1099_;
v___y_1036_ = v___y_1101_;
v___y_1037_ = v___y_1100_;
v___y_1038_ = v___y_1102_;
v___y_1039_ = v___y_1103_;
v_a_1040_ = v_a_1105_;
goto v___jp_1028_;
}
else
{
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1093_);
lean_dec_ref(v_e_u2081_832_);
return v___y_1104_;
}
}
v_resetjp_1122_:
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_nat_dec_eq(v_currRecDepth_1109_, v_maxRecDepth_1110_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_st_ref_get(v_a_835_);
v___x_1127_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_834_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v_numSteps_1129_; lean_object* v_maxSteps_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1389_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1127_);
v_numSteps_1129_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_numSteps_1129_);
lean_dec(v___x_1126_);
v_maxSteps_1130_ = lean_ctor_get(v_a_1128_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_a_1128_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v_a_1128_, 1);
lean_dec(v_unused_1390_);
v___x_1132_ = v_a_1128_;
v_isShared_1133_ = v_isSharedCheck_1389_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_maxSteps_1130_);
lean_dec(v_a_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1389_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_add(v_currRecDepth_1109_, v___x_1275_);
lean_dec(v_currRecDepth_1109_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 3, v___x_1276_);
v___x_1278_ = v___x_1123_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_fileName_1106_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_fileMap_1107_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_options_1108_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v_maxRecDepth_1110_);
lean_ctor_set(v_reuseFailAlloc_1388_, 5, v_ref_1111_);
lean_ctor_set(v_reuseFailAlloc_1388_, 6, v_currNamespace_1112_);
lean_ctor_set(v_reuseFailAlloc_1388_, 7, v_openDecls_1113_);
lean_ctor_set(v_reuseFailAlloc_1388_, 8, v_initHeartbeats_1114_);
lean_ctor_set(v_reuseFailAlloc_1388_, 9, v_maxHeartbeats_1115_);
lean_ctor_set(v_reuseFailAlloc_1388_, 10, v_quotContext_1116_);
lean_ctor_set(v_reuseFailAlloc_1388_, 11, v_currMacroScope_1117_);
lean_ctor_set(v_reuseFailAlloc_1388_, 12, v_cancelTk_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1388_, 13, v_inheritedTraceOptions_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1388_, sizeof(void*)*14, v_diag_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1388_, sizeof(void*)*14 + 1, v_suppressElabErrors_1120_);
v___x_1278_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1277_;
}
v___jp_1134_:
{
lean_object* v___x_1145_; lean_object* v_persistentCache_1146_; lean_object* v_transientCache_1147_; lean_object* v_funext_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1273_; 
v___x_1145_ = lean_st_ref_take(v___y_1138_);
v_persistentCache_1146_ = lean_ctor_get(v___x_1145_, 1);
v_transientCache_1147_ = lean_ctor_get(v___x_1145_, 2);
v_funext_1148_ = lean_ctor_get(v___x_1145_, 3);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v___x_1145_, 0);
lean_dec(v_unused_1274_);
v___x_1150_ = v___x_1145_;
v_isShared_1151_ = v_isSharedCheck_1273_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_funext_1148_);
lean_inc(v_transientCache_1147_);
lean_inc(v_persistentCache_1146_);
lean_dec(v___x_1145_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1273_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___y_1135_);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___y_1135_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_persistentCache_1146_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_transientCache_1147_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_funext_1148_);
v___x_1153_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v_pre_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_st_ref_set(v___y_1138_, v___x_1153_);
v_pre_1155_ = lean_ctor_get(v___y_1136_, 0);
lean_inc_ref(v_pre_1155_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v_e_u2081_832_);
v___x_1156_ = lean_apply_11(v_pre_1155_, v_e_u2081_832_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1271_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1271_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1271_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
if (lean_obj_tag(v_a_1157_) == 0)
{
uint8_t v_done_1161_; 
v_done_1161_ = lean_ctor_get_uint8(v_a_1157_, 0);
if (v_done_1161_ == 0)
{
uint8_t v_contextDependent_1162_; lean_object* v___x_1163_; 
lean_del_object(v___x_1159_);
v_contextDependent_1162_ = lean_ctor_get_uint8(v_a_1157_, 1);
lean_dec_ref(v_a_1157_);
lean_inc_ref(v_e_u2081_832_);
v___x_1163_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_u2081_832_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
v___x_1165_ = lean_box(0);
if (lean_obj_tag(v_a_1164_) == 0)
{
uint8_t v_done_1166_; 
v_done_1166_ = lean_ctor_get_uint8(v_a_1164_, 0);
if (v_done_1166_ == 0)
{
uint8_t v_contextDependent_1167_; lean_object* v___x_1168_; 
lean_dec_ref(v___x_1163_);
v_contextDependent_1167_ = lean_ctor_get_uint8(v_a_1164_, 1);
lean_dec_ref(v_a_1164_);
lean_inc(v___y_1136_);
lean_inc_ref(v_e_u2081_832_);
v___x_1168_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1165_, v_e_u2081_832_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1168_) == 0)
{
if (v_contextDependent_1167_ == 0)
{
lean_object* v_a_1169_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref(v___x_1168_);
v___y_1029_ = v___y_1139_;
v___y_1030_ = v_contextDependent_1162_;
v___y_1031_ = v___y_1142_;
v___y_1032_ = v___y_1141_;
v___y_1033_ = v_done_1161_;
v___y_1034_ = v___y_1143_;
v___y_1035_ = v___y_1138_;
v___y_1036_ = v___y_1136_;
v___y_1037_ = v___y_1144_;
v___y_1038_ = v___y_1140_;
v___y_1039_ = v___y_1137_;
v_a_1040_ = v_a_1169_;
goto v___jp_1028_;
}
else
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___x_1168_);
if (lean_obj_tag(v_a_1170_) == 0)
{
uint8_t v_contextDependent_1171_; 
v_contextDependent_1171_ = lean_ctor_get_uint8(v_a_1170_, 1);
v___y_1078_ = v_a_1170_;
v___y_1079_ = v___y_1142_;
v___y_1080_ = v_done_1161_;
v___y_1081_ = v___y_1143_;
v___y_1082_ = v___y_1136_;
v___y_1083_ = v___y_1140_;
v___y_1084_ = v___y_1137_;
v___y_1085_ = v___y_1139_;
v___y_1086_ = v_contextDependent_1162_;
v___y_1087_ = v___y_1141_;
v___y_1088_ = v___y_1138_;
v___y_1089_ = v___y_1144_;
v___y_1090_ = v_contextDependent_1171_;
goto v___jp_1077_;
}
else
{
uint8_t v_contextDependent_1172_; 
v_contextDependent_1172_ = lean_ctor_get_uint8(v_a_1170_, sizeof(void*)*2 + 1);
v___y_1078_ = v_a_1170_;
v___y_1079_ = v___y_1142_;
v___y_1080_ = v_done_1161_;
v___y_1081_ = v___y_1143_;
v___y_1082_ = v___y_1136_;
v___y_1083_ = v___y_1140_;
v___y_1084_ = v___y_1137_;
v___y_1085_ = v___y_1139_;
v___y_1086_ = v_contextDependent_1162_;
v___y_1087_ = v___y_1141_;
v___y_1088_ = v___y_1138_;
v___y_1089_ = v___y_1144_;
v___y_1090_ = v_contextDependent_1172_;
goto v___jp_1077_;
}
}
}
else
{
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v_e_u2081_832_);
return v___x_1168_;
}
}
else
{
lean_dec_ref(v_a_1164_);
v___y_1093_ = v___y_1139_;
v___y_1094_ = v_contextDependent_1162_;
v___y_1095_ = v___y_1142_;
v___y_1096_ = v___y_1141_;
v___y_1097_ = v___y_1143_;
v___y_1098_ = v_done_1161_;
v___y_1099_ = v___y_1138_;
v___y_1100_ = v___y_1144_;
v___y_1101_ = v___y_1136_;
v___y_1102_ = v___y_1140_;
v___y_1103_ = v___y_1137_;
v___y_1104_ = v___x_1163_;
goto v___jp_1092_;
}
}
else
{
uint8_t v_done_1173_; 
v_done_1173_ = lean_ctor_get_uint8(v_a_1164_, sizeof(void*)*2);
if (v_done_1173_ == 0)
{
lean_object* v_e_x27_1174_; lean_object* v_proof_1175_; uint8_t v_contextDependent_1176_; lean_object* v___x_1177_; 
lean_dec_ref(v___x_1163_);
v_e_x27_1174_ = lean_ctor_get(v_a_1164_, 0);
lean_inc_ref(v_e_x27_1174_);
v_proof_1175_ = lean_ctor_get(v_a_1164_, 1);
lean_inc_ref(v_proof_1175_);
v_contextDependent_1176_ = lean_ctor_get_uint8(v_a_1164_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1164_);
lean_inc(v___y_1136_);
lean_inc_ref(v_e_x27_1174_);
v___x_1177_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1165_, v_e_x27_1174_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
if (lean_obj_tag(v_a_1178_) == 0)
{
if (v_contextDependent_1176_ == 0)
{
uint8_t v_done_1179_; uint8_t v_contextDependent_1180_; 
v_done_1179_ = lean_ctor_get_uint8(v_a_1178_, 0);
v_contextDependent_1180_ = lean_ctor_get_uint8(v_a_1178_, 1);
lean_dec_ref(v_a_1178_);
v___y_1061_ = v___y_1142_;
v___y_1062_ = v_done_1161_;
v___y_1063_ = v___y_1143_;
v___y_1064_ = v___y_1136_;
v___y_1065_ = v___y_1140_;
v___y_1066_ = v_done_1179_;
v___y_1067_ = v___y_1137_;
v___y_1068_ = v_e_x27_1174_;
v___y_1069_ = v___y_1139_;
v___y_1070_ = v_contextDependent_1162_;
v___y_1071_ = v___y_1141_;
v___y_1072_ = v___y_1138_;
v___y_1073_ = v___y_1144_;
v___y_1074_ = v_proof_1175_;
v___y_1075_ = v_contextDependent_1180_;
goto v___jp_1060_;
}
else
{
uint8_t v_done_1181_; 
v_done_1181_ = lean_ctor_get_uint8(v_a_1178_, 0);
lean_dec_ref(v_a_1178_);
v___y_1061_ = v___y_1142_;
v___y_1062_ = v_done_1161_;
v___y_1063_ = v___y_1143_;
v___y_1064_ = v___y_1136_;
v___y_1065_ = v___y_1140_;
v___y_1066_ = v_done_1181_;
v___y_1067_ = v___y_1137_;
v___y_1068_ = v_e_x27_1174_;
v___y_1069_ = v___y_1139_;
v___y_1070_ = v_contextDependent_1162_;
v___y_1071_ = v___y_1141_;
v___y_1072_ = v___y_1138_;
v___y_1073_ = v___y_1144_;
v___y_1074_ = v_proof_1175_;
v___y_1075_ = v_contextDependent_1176_;
goto v___jp_1060_;
}
}
else
{
lean_object* v_e_x27_1182_; lean_object* v_proof_1183_; uint8_t v_done_1184_; uint8_t v_contextDependent_1185_; lean_object* v___x_1186_; 
v_e_x27_1182_ = lean_ctor_get(v_a_1178_, 0);
lean_inc_ref(v_e_x27_1182_);
v_proof_1183_ = lean_ctor_get(v_a_1178_, 1);
lean_inc_ref(v_proof_1183_);
v_done_1184_ = lean_ctor_get_uint8(v_a_1178_, sizeof(void*)*2);
v_contextDependent_1185_ = lean_ctor_get_uint8(v_a_1178_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1178_);
lean_inc_ref(v_e_x27_1182_);
lean_inc_ref(v_e_u2081_832_);
v___x_1186_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_832_, v_e_x27_1174_, v_proof_1175_, v_e_x27_1182_, v_proof_1183_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1186_) == 0)
{
if (v_contextDependent_1176_ == 0)
{
lean_object* v_a_1187_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v___y_1044_ = v___y_1142_;
v___y_1045_ = v_done_1184_;
v___y_1046_ = v_done_1161_;
v___y_1047_ = v___y_1143_;
v___y_1048_ = v___y_1136_;
v___y_1049_ = v___y_1140_;
v___y_1050_ = v___y_1137_;
v___y_1051_ = v_a_1187_;
v___y_1052_ = v_e_x27_1182_;
v___y_1053_ = v___y_1139_;
v___y_1054_ = v_contextDependent_1162_;
v___y_1055_ = v___y_1141_;
v___y_1056_ = v___y_1138_;
v___y_1057_ = v___y_1144_;
v___y_1058_ = v_contextDependent_1185_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1188_; 
v_a_1188_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1186_);
v___y_1044_ = v___y_1142_;
v___y_1045_ = v_done_1184_;
v___y_1046_ = v_done_1161_;
v___y_1047_ = v___y_1143_;
v___y_1048_ = v___y_1136_;
v___y_1049_ = v___y_1140_;
v___y_1050_ = v___y_1137_;
v___y_1051_ = v_a_1188_;
v___y_1052_ = v_e_x27_1182_;
v___y_1053_ = v___y_1139_;
v___y_1054_ = v_contextDependent_1162_;
v___y_1055_ = v___y_1141_;
v___y_1056_ = v___y_1138_;
v___y_1057_ = v___y_1144_;
v___y_1058_ = v_contextDependent_1176_;
goto v___jp_1043_;
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_e_x27_1182_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v_e_u2081_832_);
v_a_1189_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1186_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1186_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1175_);
lean_dec_ref(v_e_x27_1174_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v_e_u2081_832_);
return v___x_1177_;
}
}
else
{
lean_dec_ref(v_a_1164_);
v___y_1093_ = v___y_1139_;
v___y_1094_ = v_contextDependent_1162_;
v___y_1095_ = v___y_1142_;
v___y_1096_ = v___y_1141_;
v___y_1097_ = v___y_1143_;
v___y_1098_ = v_done_1161_;
v___y_1099_ = v___y_1138_;
v___y_1100_ = v___y_1144_;
v___y_1101_ = v___y_1136_;
v___y_1102_ = v___y_1140_;
v___y_1103_ = v___y_1137_;
v___y_1104_ = v___x_1163_;
goto v___jp_1092_;
}
}
}
else
{
v___y_1093_ = v___y_1139_;
v___y_1094_ = v_contextDependent_1162_;
v___y_1095_ = v___y_1142_;
v___y_1096_ = v___y_1141_;
v___y_1097_ = v___y_1143_;
v___y_1098_ = v_done_1161_;
v___y_1099_ = v___y_1138_;
v___y_1100_ = v___y_1144_;
v___y_1101_ = v___y_1136_;
v___y_1102_ = v___y_1140_;
v___y_1103_ = v___y_1137_;
v___y_1104_ = v___x_1163_;
goto v___jp_1092_;
}
}
else
{
uint8_t v_contextDependent_1197_; 
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
v_contextDependent_1197_ = lean_ctor_get_uint8(v_a_1157_, 1);
if (v_contextDependent_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v_numSteps_1199_; lean_object* v_persistentCache_1200_; lean_object* v_transientCache_1201_; lean_object* v_funext_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1214_; 
v___x_1198_ = lean_st_ref_take(v___y_1138_);
v_numSteps_1199_ = lean_ctor_get(v___x_1198_, 0);
v_persistentCache_1200_ = lean_ctor_get(v___x_1198_, 1);
v_transientCache_1201_ = lean_ctor_get(v___x_1198_, 2);
v_funext_1202_ = lean_ctor_get(v___x_1198_, 3);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1204_ = v___x_1198_;
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_funext_1202_);
lean_inc(v_transientCache_1201_);
lean_inc(v_persistentCache_1200_);
lean_inc(v_numSteps_1199_);
lean_dec(v___x_1198_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_inc_ref(v_a_1157_);
v___x_1206_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1200_, v_e_u2081_832_, v_a_1157_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_numSteps_1199_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_transientCache_1201_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_funext_1202_);
v___x_1208_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_st_ref_set(v___y_1138_, v___x_1208_);
lean_dec(v___y_1138_);
if (v_isShared_1160_ == 0)
{
v___x_1211_ = v___x_1159_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1157_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v___x_1215_; lean_object* v_numSteps_1216_; lean_object* v_persistentCache_1217_; lean_object* v_transientCache_1218_; lean_object* v_funext_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1231_; 
v___x_1215_ = lean_st_ref_take(v___y_1138_);
v_numSteps_1216_ = lean_ctor_get(v___x_1215_, 0);
v_persistentCache_1217_ = lean_ctor_get(v___x_1215_, 1);
v_transientCache_1218_ = lean_ctor_get(v___x_1215_, 2);
v_funext_1219_ = lean_ctor_get(v___x_1215_, 3);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1221_ = v___x_1215_;
v_isShared_1222_ = v_isSharedCheck_1231_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_funext_1219_);
lean_inc(v_transientCache_1218_);
lean_inc(v_persistentCache_1217_);
lean_inc(v_numSteps_1216_);
lean_dec(v___x_1215_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1231_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
lean_inc_ref(v_a_1157_);
v___x_1223_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1218_, v_e_u2081_832_, v_a_1157_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 2, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_numSteps_1216_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_persistentCache_1217_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_funext_1219_);
v___x_1225_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_st_ref_set(v___y_1138_, v___x_1225_);
lean_dec(v___y_1138_);
if (v_isShared_1160_ == 0)
{
v___x_1228_ = v___x_1159_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1157_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
else
{
uint8_t v_done_1232_; 
v_done_1232_ = lean_ctor_get_uint8(v_a_1157_, sizeof(void*)*2);
if (v_done_1232_ == 0)
{
lean_object* v_e_x27_1233_; lean_object* v_proof_1234_; uint8_t v_contextDependent_1235_; 
lean_del_object(v___x_1159_);
v_e_x27_1233_ = lean_ctor_get(v_a_1157_, 0);
lean_inc_ref(v_e_x27_1233_);
v_proof_1234_ = lean_ctor_get(v_a_1157_, 1);
lean_inc_ref(v_proof_1234_);
v_contextDependent_1235_ = lean_ctor_get_uint8(v_a_1157_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1157_);
v_e_u2082_892_ = v_e_x27_1233_;
v_h_u2081_893_ = v_proof_1234_;
v_cd_u2081_894_ = v_contextDependent_1235_;
v___y_895_ = v___y_1136_;
v___y_896_ = v___y_1137_;
v___y_897_ = v___y_1138_;
v___y_898_ = v___y_1139_;
v___y_899_ = v___y_1140_;
v___y_900_ = v___y_1141_;
v___y_901_ = v___y_1142_;
v___y_902_ = v___y_1143_;
v___y_903_ = v___y_1144_;
goto v___jp_891_;
}
else
{
uint8_t v_contextDependent_1236_; 
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
v_contextDependent_1236_ = lean_ctor_get_uint8(v_a_1157_, sizeof(void*)*2 + 1);
if (v_contextDependent_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v_numSteps_1238_; lean_object* v_persistentCache_1239_; lean_object* v_transientCache_1240_; lean_object* v_funext_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1253_; 
v___x_1237_ = lean_st_ref_take(v___y_1138_);
v_numSteps_1238_ = lean_ctor_get(v___x_1237_, 0);
v_persistentCache_1239_ = lean_ctor_get(v___x_1237_, 1);
v_transientCache_1240_ = lean_ctor_get(v___x_1237_, 2);
v_funext_1241_ = lean_ctor_get(v___x_1237_, 3);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1243_ = v___x_1237_;
v_isShared_1244_ = v_isSharedCheck_1253_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_funext_1241_);
lean_inc(v_transientCache_1240_);
lean_inc(v_persistentCache_1239_);
lean_inc(v_numSteps_1238_);
lean_dec(v___x_1237_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1253_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
lean_inc_ref(v_a_1157_);
v___x_1245_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1239_, v_e_u2081_832_, v_a_1157_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_numSteps_1238_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_transientCache_1240_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_funext_1241_);
v___x_1247_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_st_ref_set(v___y_1138_, v___x_1247_);
lean_dec(v___y_1138_);
if (v_isShared_1160_ == 0)
{
v___x_1250_ = v___x_1159_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1157_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v___x_1254_; lean_object* v_numSteps_1255_; lean_object* v_persistentCache_1256_; lean_object* v_transientCache_1257_; lean_object* v_funext_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1270_; 
v___x_1254_ = lean_st_ref_take(v___y_1138_);
v_numSteps_1255_ = lean_ctor_get(v___x_1254_, 0);
v_persistentCache_1256_ = lean_ctor_get(v___x_1254_, 1);
v_transientCache_1257_ = lean_ctor_get(v___x_1254_, 2);
v_funext_1258_ = lean_ctor_get(v___x_1254_, 3);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1260_ = v___x_1254_;
v_isShared_1261_ = v_isSharedCheck_1270_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_funext_1258_);
lean_inc(v_transientCache_1257_);
lean_inc(v_persistentCache_1256_);
lean_inc(v_numSteps_1255_);
lean_dec(v___x_1254_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1270_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
lean_inc_ref(v_a_1157_);
v___x_1262_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1257_, v_e_u2081_832_, v_a_1157_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 2, v___x_1262_);
v___x_1264_ = v___x_1260_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_numSteps_1255_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_persistentCache_1256_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v_funext_1258_);
v___x_1264_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_st_ref_set(v___y_1138_, v___x_1264_);
lean_dec(v___y_1138_);
if (v_isShared_1160_ == 0)
{
v___x_1267_ = v___x_1159_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1157_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
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
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v_e_u2081_832_);
return v___x_1156_;
}
}
}
}
v_reusejp_1277_:
{
lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; uint8_t v___x_1377_; 
v___x_1377_ = lean_nat_dec_le(v_maxSteps_1130_, v_numSteps_1129_);
lean_dec(v_maxSteps_1130_);
if (v___x_1377_ == 0)
{
v___y_1280_ = v_a_833_;
v___y_1281_ = v_a_834_;
v___y_1282_ = v_a_835_;
v___y_1283_ = v_a_836_;
v___y_1284_ = v_a_837_;
v___y_1285_ = v_a_838_;
v___y_1286_ = v_a_839_;
v___y_1287_ = v_a_841_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_del_object(v___x_1132_);
lean_dec(v_numSteps_1129_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_e_u2081_832_);
v___x_1378_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5);
v___x_1379_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_1378_, v_a_838_, v_a_839_, v___x_1278_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v___x_1278_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
v___jp_1279_:
{
lean_object* v___x_1288_; lean_object* v_persistentCache_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_st_ref_get(v___y_1282_);
v_persistentCache_1289_ = lean_ctor_get(v___x_1288_, 1);
lean_inc_ref(v_persistentCache_1289_);
lean_dec(v___x_1288_);
v___x_1290_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_persistentCache_1289_, v_e_u2081_832_);
if (lean_obj_tag(v___x_1290_) == 1)
{
lean_object* v_val_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v_numSteps_1129_);
v_val_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_val_1291_);
lean_dec_ref(v___x_1290_);
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1293_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1292_, v___x_1278_);
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1324_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1324_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_unbox(v_a_1294_);
lean_dec(v_a_1294_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1300_; 
lean_dec(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v___x_1278_);
lean_del_object(v___x_1132_);
lean_dec_ref(v_e_u2081_832_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v_val_1291_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1291_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_del_object(v___x_1296_);
v___x_1302_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1);
v___x_1303_ = l_Lean_MessageData_ofExpr(v_e_u2081_832_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 7);
lean_ctor_set(v___x_1132_, 1, v___x_1303_);
lean_ctor_set(v___x_1132_, 0, v___x_1302_);
v___x_1305_ = v___x_1132_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v___x_1292_, v___x_1305_, v___y_1285_, v___y_1286_, v___x_1278_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___x_1278_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1306_, 0);
lean_dec(v_unused_1314_);
v___x_1308_ = v___x_1306_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_dec(v___x_1306_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_val_1291_);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_val_1291_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec(v_val_1291_);
v_a_1315_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1306_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1306_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1325_; lean_object* v_transientCache_1326_; lean_object* v___x_1327_; 
lean_dec(v___x_1290_);
v___x_1325_ = lean_st_ref_get(v___y_1282_);
v_transientCache_1326_ = lean_ctor_get(v___x_1325_, 2);
lean_inc_ref(v_transientCache_1326_);
lean_dec(v___x_1325_);
v___x_1327_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_transientCache_1326_, v_e_u2081_832_);
if (lean_obj_tag(v___x_1327_) == 1)
{
lean_object* v_val_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v_numSteps_1129_);
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_val_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1330_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1329_, v___x_1278_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1361_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1361_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_unbox(v_a_1331_);
lean_dec(v_a_1331_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1337_; 
lean_dec(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v___x_1278_);
lean_del_object(v___x_1132_);
lean_dec_ref(v_e_u2081_832_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v_val_1328_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_val_1328_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_del_object(v___x_1333_);
v___x_1339_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3);
v___x_1340_ = l_Lean_MessageData_ofExpr(v_e_u2081_832_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 7);
lean_ctor_set(v___x_1132_, 1, v___x_1340_);
lean_ctor_set(v___x_1132_, 0, v___x_1339_);
v___x_1342_ = v___x_1132_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v___x_1329_, v___x_1342_, v___y_1285_, v___y_1286_, v___x_1278_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___x_1278_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v___x_1343_, 0);
lean_dec(v_unused_1351_);
v___x_1345_ = v___x_1343_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_dec(v___x_1343_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_val_1328_);
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_val_1328_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_val_1328_);
v_a_1352_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1343_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1343_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
lean_dec(v___x_1327_);
lean_del_object(v___x_1132_);
v___x_1362_ = lean_nat_add(v_numSteps_1129_, v___x_1275_);
lean_dec(v_numSteps_1129_);
v___x_1363_ = lean_unsigned_to_nat(1000u);
v___x_1364_ = lean_nat_mod(v___x_1362_, v___x_1363_);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_nat_dec_eq(v___x_1364_, v___x_1365_);
lean_dec(v___x_1364_);
if (v___x_1366_ == 0)
{
v___y_1135_ = v___x_1362_;
v___y_1136_ = v___y_1280_;
v___y_1137_ = v___y_1281_;
v___y_1138_ = v___y_1282_;
v___y_1139_ = v___y_1283_;
v___y_1140_ = v___y_1284_;
v___y_1141_ = v___y_1285_;
v___y_1142_ = v___y_1286_;
v___y_1143_ = v___x_1278_;
v___y_1144_ = v___y_1287_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1368_ = l_Lean_Core_checkSystem(v___x_1367_, v___x_1278_, v___y_1287_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_dec_ref(v___x_1368_);
v___y_1135_ = v___x_1362_;
v___y_1136_ = v___y_1280_;
v___y_1137_ = v___y_1281_;
v___y_1138_ = v___y_1282_;
v___y_1139_ = v___y_1283_;
v___y_1140_ = v___y_1284_;
v___y_1141_ = v___y_1285_;
v___y_1142_ = v___y_1286_;
v___y_1143_ = v___x_1278_;
v___y_1144_ = v___y_1287_;
goto v___jp_1134_;
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v___x_1362_);
lean_dec(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___x_1278_);
lean_dec_ref(v_e_u2081_832_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
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
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v___x_1126_);
lean_del_object(v___x_1123_);
lean_dec_ref(v_inheritedTraceOptions_1121_);
lean_dec(v_cancelTk_x3f_1119_);
lean_dec(v_currMacroScope_1117_);
lean_dec(v_quotContext_1116_);
lean_dec(v_maxHeartbeats_1115_);
lean_dec(v_initHeartbeats_1114_);
lean_dec(v_openDecls_1113_);
lean_dec(v_currNamespace_1112_);
lean_dec(v_ref_1111_);
lean_dec(v_maxRecDepth_1110_);
lean_dec(v_currRecDepth_1109_);
lean_dec_ref(v_options_1108_);
lean_dec_ref(v_fileMap_1107_);
lean_dec_ref(v_fileName_1106_);
lean_dec(v_a_841_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_e_u2081_832_);
v_a_1391_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1127_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1127_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
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
lean_object* v___x_1399_; 
lean_del_object(v___x_1123_);
lean_dec_ref(v_inheritedTraceOptions_1121_);
lean_dec(v_cancelTk_x3f_1119_);
lean_dec(v_currMacroScope_1117_);
lean_dec(v_quotContext_1116_);
lean_dec(v_maxHeartbeats_1115_);
lean_dec(v_initHeartbeats_1114_);
lean_dec(v_openDecls_1113_);
lean_dec(v_currNamespace_1112_);
lean_dec(v_maxRecDepth_1110_);
lean_dec(v_currRecDepth_1109_);
lean_dec_ref(v_options_1108_);
lean_dec_ref(v_fileMap_1107_);
lean_dec_ref(v_fileName_1106_);
lean_dec(v_a_841_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_e_u2081_832_);
v___x_1399_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__4___redArg(v_ref_1111_);
return v___x_1399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* v_e_u2081_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = lean_sym_simp(v_e_u2081_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* v_00_u03b2_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_1414_, v_x_1415_, v_x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* v_00_u03b2_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_1419_, v_x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* v_00_u03b2_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_1422_, v_x_1423_, v_x_1424_);
lean_dec_ref(v_x_1424_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_object* v_cls_1426_, lean_object* v_msg_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_cls_1426_, v_msg_1427_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(lean_object* v_cls_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(v_cls_1439_, v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* v_00_u03b2_1452_, lean_object* v_x_1453_, size_t v_x_1454_, size_t v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_1453_, v_x_1454_, v_x_1455_, v_x_1456_, v_x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
size_t v_x_112934__boxed_1465_; size_t v_x_112935__boxed_1466_; lean_object* v_res_1467_; 
v_x_112934__boxed_1465_ = lean_unbox_usize(v_x_1461_);
lean_dec(v_x_1461_);
v_x_112935__boxed_1466_ = lean_unbox_usize(v_x_1462_);
lean_dec(v_x_1462_);
v_res_1467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_1459_, v_x_1460_, v_x_112934__boxed_1465_, v_x_112935__boxed_1466_, v_x_1463_, v_x_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* v_00_u03b2_1468_, lean_object* v_x_1469_, size_t v_x_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_1469_, v_x_1470_, v_x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
size_t v_x_112951__boxed_1477_; lean_object* v_res_1478_; 
v_x_112951__boxed_1477_ = lean_unbox_usize(v_x_1475_);
lean_dec(v_x_1475_);
v_res_1478_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_1473_, v_x_1474_, v_x_112951__boxed_1477_, v_x_1476_);
lean_dec_ref(v_x_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1479_, lean_object* v_n_1480_, lean_object* v_k_1481_, lean_object* v_v_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_n_1480_, v_k_1481_, v_v_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1484_, size_t v_depth_1485_, lean_object* v_keys_1486_, lean_object* v_vals_1487_, lean_object* v_heq_1488_, lean_object* v_i_1489_, lean_object* v_entries_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___redArg(v_depth_1485_, v_keys_1486_, v_vals_1487_, v_i_1489_, v_entries_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1492_, lean_object* v_depth_1493_, lean_object* v_keys_1494_, lean_object* v_vals_1495_, lean_object* v_heq_1496_, lean_object* v_i_1497_, lean_object* v_entries_1498_){
_start:
{
size_t v_depth_boxed_1499_; lean_object* v_res_1500_; 
v_depth_boxed_1499_ = lean_unbox_usize(v_depth_1493_);
lean_dec(v_depth_1493_);
v_res_1500_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__4(v_00_u03b2_1492_, v_depth_boxed_1499_, v_keys_1494_, v_vals_1495_, v_heq_1496_, v_i_1497_, v_entries_1498_);
lean_dec_ref(v_vals_1495_);
lean_dec_ref(v_keys_1494_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_1501_, lean_object* v_keys_1502_, lean_object* v_vals_1503_, lean_object* v_heq_1504_, lean_object* v_i_1505_, lean_object* v_k_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___redArg(v_keys_1502_, v_vals_1503_, v_i_1505_, v_k_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7___boxed(lean_object* v_00_u03b2_1508_, lean_object* v_keys_1509_, lean_object* v_vals_1510_, lean_object* v_heq_1511_, lean_object* v_i_1512_, lean_object* v_k_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__7(v_00_u03b2_1508_, v_keys_1509_, v_vals_1510_, v_heq_1511_, v_i_1512_, v_k_1513_);
lean_dec_ref(v_k_1513_);
lean_dec_ref(v_vals_1510_);
lean_dec_ref(v_keys_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3_spec__6___redArg(v_x_1516_, v_x_1517_, v_x_1518_, v_x_1519_);
return v___x_1520_;
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
