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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; 
v___x_529_ = ((size_t)5ULL);
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_shift_left(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; 
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
v___x_534_ = lean_usize_sub(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* v_x_536_, size_t v_x_537_, size_t v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_es_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v_j_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_es_541_ = lean_ctor_get(v_x_536_, 0);
v___x_542_ = ((size_t)5ULL);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1);
v___x_545_ = lean_usize_land(v_x_537_, v___x_544_);
v_j_546_ = lean_usize_to_nat(v___x_545_);
v___x_547_ = lean_array_get_size(v_es_541_);
v___x_548_ = lean_nat_dec_lt(v_j_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec(v_j_546_);
lean_dec(v_x_540_);
lean_dec_ref(v_x_539_);
return v_x_536_;
}
else
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_585_; 
lean_inc_ref(v_es_541_);
v_isSharedCheck_585_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; 
v_unused_586_ = lean_ctor_get(v_x_536_, 0);
lean_dec(v_unused_586_);
v___x_550_ = v_x_536_;
v_isShared_551_ = v_isSharedCheck_585_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_x_536_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_585_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_v_552_; lean_object* v___x_553_; lean_object* v_xs_x27_554_; lean_object* v___y_556_; 
v_v_552_ = lean_array_fget(v_es_541_, v_j_546_);
v___x_553_ = lean_box(0);
v_xs_x27_554_ = lean_array_fset(v_es_541_, v_j_546_, v___x_553_);
switch(lean_obj_tag(v_v_552_))
{
case 0:
{
lean_object* v_key_561_; lean_object* v_val_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_572_; 
v_key_561_ = lean_ctor_get(v_v_552_, 0);
v_val_562_ = lean_ctor_get(v_v_552_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_v_552_);
if (v_isSharedCheck_572_ == 0)
{
v___x_564_ = v_v_552_;
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_val_562_);
lean_inc(v_key_561_);
lean_dec(v_v_552_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___x_566_; 
v___x_566_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_539_, v_key_561_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_del_object(v___x_564_);
v___x_567_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_561_, v_val_562_, v_x_539_, v_x_540_);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
v___y_556_ = v___x_568_;
goto v___jp_555_;
}
else
{
lean_object* v___x_570_; 
lean_dec(v_val_562_);
lean_dec(v_key_561_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v_x_540_);
lean_ctor_set(v___x_564_, 0, v_x_539_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_x_539_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_x_540_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v___y_556_ = v___x_570_;
goto v___jp_555_;
}
}
}
}
case 1:
{
lean_object* v_node_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_583_; 
v_node_573_ = lean_ctor_get(v_v_552_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_v_552_);
if (v_isSharedCheck_583_ == 0)
{
v___x_575_ = v_v_552_;
v_isShared_576_ = v_isSharedCheck_583_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_node_573_);
lean_dec(v_v_552_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_583_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_577_ = lean_usize_shift_right(v_x_537_, v___x_542_);
v___x_578_ = lean_usize_add(v_x_538_, v___x_543_);
v___x_579_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_573_, v___x_577_, v___x_578_, v_x_539_, v_x_540_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_579_);
v___x_581_ = v___x_575_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
v___y_556_ = v___x_581_;
goto v___jp_555_;
}
}
}
default: 
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_x_539_);
lean_ctor_set(v___x_584_, 1, v_x_540_);
v___y_556_ = v___x_584_;
goto v___jp_555_;
}
}
v___jp_555_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_array_fset(v_xs_x27_554_, v_j_546_, v___y_556_);
lean_dec(v_j_546_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_557_);
v___x_559_ = v___x_550_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
else
{
lean_object* v_ks_587_; lean_object* v_vs_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_608_; 
v_ks_587_ = lean_ctor_get(v_x_536_, 0);
v_vs_588_ = lean_ctor_get(v_x_536_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_608_ == 0)
{
v___x_590_ = v_x_536_;
v_isShared_591_ = v_isSharedCheck_608_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_vs_588_);
lean_inc(v_ks_587_);
lean_dec(v_x_536_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_608_;
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
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_ks_587_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_vs_588_);
v___x_593_ = v_reuseFailAlloc_607_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v_newNode_594_; uint8_t v___y_596_; size_t v___x_602_; uint8_t v___x_603_; 
v_newNode_594_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v___x_593_, v_x_539_, v_x_540_);
v___x_602_ = ((size_t)7ULL);
v___x_603_ = lean_usize_dec_le(v___x_602_, v_x_538_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_604_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_594_);
v___x_605_ = lean_unsigned_to_nat(4u);
v___x_606_ = lean_nat_dec_lt(v___x_604_, v___x_605_);
lean_dec(v___x_604_);
v___y_596_ = v___x_606_;
goto v___jp_595_;
}
else
{
v___y_596_ = v___x_603_;
goto v___jp_595_;
}
v___jp_595_:
{
if (v___y_596_ == 0)
{
lean_object* v_ks_597_; lean_object* v_vs_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_ks_597_ = lean_ctor_get(v_newNode_594_, 0);
lean_inc_ref(v_ks_597_);
v_vs_598_ = lean_ctor_get(v_newNode_594_, 1);
lean_inc_ref(v_vs_598_);
lean_dec_ref(v_newNode_594_);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2);
v___x_601_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_x_538_, v_ks_597_, v_vs_598_, v___x_599_, v___x_600_);
lean_dec_ref(v_vs_598_);
lean_dec_ref(v_ks_597_);
return v___x_601_;
}
else
{
return v_newNode_594_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_609_, lean_object* v_keys_610_, lean_object* v_vals_611_, lean_object* v_i_612_, lean_object* v_entries_613_){
_start:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_array_get_size(v_keys_610_);
v___x_615_ = lean_nat_dec_lt(v_i_612_, v___x_614_);
if (v___x_615_ == 0)
{
lean_dec(v_i_612_);
return v_entries_613_;
}
else
{
lean_object* v_k_616_; lean_object* v_v_617_; uint64_t v___x_618_; size_t v_h_619_; size_t v___x_620_; lean_object* v___x_621_; size_t v___x_622_; size_t v___x_623_; size_t v___x_624_; size_t v_h_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_k_616_ = lean_array_fget_borrowed(v_keys_610_, v_i_612_);
v_v_617_ = lean_array_fget_borrowed(v_vals_611_, v_i_612_);
v___x_618_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_616_);
v_h_619_ = lean_uint64_to_usize(v___x_618_);
v___x_620_ = ((size_t)5ULL);
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_sub(v_depth_609_, v___x_622_);
v___x_624_ = lean_usize_mul(v___x_620_, v___x_623_);
v_h_625_ = lean_usize_shift_right(v_h_619_, v___x_624_);
v___x_626_ = lean_nat_add(v_i_612_, v___x_621_);
lean_dec(v_i_612_);
lean_inc(v_v_617_);
lean_inc(v_k_616_);
v___x_627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_613_, v_h_625_, v_depth_609_, v_k_616_, v_v_617_);
v_i_612_ = v___x_626_;
v_entries_613_ = v___x_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_629_, lean_object* v_keys_630_, lean_object* v_vals_631_, lean_object* v_i_632_, lean_object* v_entries_633_){
_start:
{
size_t v_depth_boxed_634_; lean_object* v_res_635_; 
v_depth_boxed_634_ = lean_unbox_usize(v_depth_629_);
lean_dec(v_depth_629_);
v_res_635_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_634_, v_keys_630_, v_vals_631_, v_i_632_, v_entries_633_);
lean_dec_ref(v_vals_631_);
lean_dec_ref(v_keys_630_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_118674__boxed_641_; size_t v_x_118675__boxed_642_; lean_object* v_res_643_; 
v_x_118674__boxed_641_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_x_118675__boxed_642_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_res_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_636_, v_x_118674__boxed_641_, v_x_118675__boxed_642_, v_x_639_, v_x_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
uint64_t v___x_647_; size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v___x_647_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_645_);
v___x_648_ = lean_uint64_to_usize(v___x_647_);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_644_, v___x_648_, v___x_649_, v_x_645_, v_x_646_);
return v___x_650_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_651_; double v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_float_of_nat(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* v_cls_656_, lean_object* v_msg_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_ref_663_; lean_object* v___x_664_; lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_709_; 
v_ref_663_ = lean_ctor_get(v___y_660_, 5);
v___x_664_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_709_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_709_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_709_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v_traceState_670_; lean_object* v_env_671_; lean_object* v_nextMacroScope_672_; lean_object* v_ngen_673_; lean_object* v_auxDeclNGen_674_; lean_object* v_cache_675_; lean_object* v_messages_676_; lean_object* v_infoState_677_; lean_object* v_snapshotTasks_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_708_; 
v___x_669_ = lean_st_ref_take(v___y_661_);
v_traceState_670_ = lean_ctor_get(v___x_669_, 4);
v_env_671_ = lean_ctor_get(v___x_669_, 0);
v_nextMacroScope_672_ = lean_ctor_get(v___x_669_, 1);
v_ngen_673_ = lean_ctor_get(v___x_669_, 2);
v_auxDeclNGen_674_ = lean_ctor_get(v___x_669_, 3);
v_cache_675_ = lean_ctor_get(v___x_669_, 5);
v_messages_676_ = lean_ctor_get(v___x_669_, 6);
v_infoState_677_ = lean_ctor_get(v___x_669_, 7);
v_snapshotTasks_678_ = lean_ctor_get(v___x_669_, 8);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_708_ == 0)
{
v___x_680_ = v___x_669_;
v_isShared_681_ = v_isSharedCheck_708_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snapshotTasks_678_);
lean_inc(v_infoState_677_);
lean_inc(v_messages_676_);
lean_inc(v_cache_675_);
lean_inc(v_traceState_670_);
lean_inc(v_auxDeclNGen_674_);
lean_inc(v_ngen_673_);
lean_inc(v_nextMacroScope_672_);
lean_inc(v_env_671_);
lean_dec(v___x_669_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_708_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
uint64_t v_tid_682_; lean_object* v_traces_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_707_; 
v_tid_682_ = lean_ctor_get_uint64(v_traceState_670_, sizeof(void*)*1);
v_traces_683_ = lean_ctor_get(v_traceState_670_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_traceState_670_);
if (v_isSharedCheck_707_ == 0)
{
v___x_685_ = v_traceState_670_;
v_isShared_686_ = v_isSharedCheck_707_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_traces_683_);
lean_dec(v_traceState_670_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_707_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; double v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_687_ = lean_box(0);
v___x_688_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0);
v___x_689_ = 0;
v___x_690_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1));
v___x_691_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_691_, 0, v_cls_656_);
lean_ctor_set(v___x_691_, 1, v___x_687_);
lean_ctor_set(v___x_691_, 2, v___x_690_);
lean_ctor_set_float(v___x_691_, sizeof(void*)*3, v___x_688_);
lean_ctor_set_float(v___x_691_, sizeof(void*)*3 + 8, v___x_688_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*3 + 16, v___x_689_);
v___x_692_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2));
v___x_693_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v_a_665_);
lean_ctor_set(v___x_693_, 2, v___x_692_);
lean_inc(v_ref_663_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_ref_663_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = l_Lean_PersistentArray_push___redArg(v_traces_683_, v___x_694_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_695_);
v___x_697_ = v___x_685_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_695_);
lean_ctor_set_uint64(v_reuseFailAlloc_706_, sizeof(void*)*1, v_tid_682_);
v___x_697_ = v_reuseFailAlloc_706_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 4, v___x_697_);
v___x_699_ = v___x_680_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_env_671_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_nextMacroScope_672_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_ngen_673_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_auxDeclNGen_674_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_705_, 5, v_cache_675_);
lean_ctor_set(v_reuseFailAlloc_705_, 6, v_messages_676_);
lean_ctor_set(v_reuseFailAlloc_705_, 7, v_infoState_677_);
lean_ctor_set(v_reuseFailAlloc_705_, 8, v_snapshotTasks_678_);
v___x_699_ = v_reuseFailAlloc_705_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_700_ = lean_st_ref_set(v___y_661_, v___x_699_);
v___x_701_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_701_);
v___x_703_ = v___x_667_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* v_cls_710_, lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_710_, v_msg_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_718_, lean_object* v_vals_719_, lean_object* v_i_720_, lean_object* v_k_721_){
_start:
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_array_get_size(v_keys_718_);
v___x_723_ = lean_nat_dec_lt(v_i_720_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec(v_i_720_);
v___x_724_ = lean_box(0);
return v___x_724_;
}
else
{
lean_object* v_k_x27_725_; uint8_t v___x_726_; 
v_k_x27_725_ = lean_array_fget_borrowed(v_keys_718_, v_i_720_);
v___x_726_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_721_, v_k_x27_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_i_720_, v___x_727_);
lean_dec(v_i_720_);
v_i_720_ = v___x_728_;
goto _start;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_array_fget_borrowed(v_vals_719_, v_i_720_);
lean_dec(v_i_720_);
lean_inc(v___x_730_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_732_, lean_object* v_vals_733_, lean_object* v_i_734_, lean_object* v_k_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_732_, v_vals_733_, v_i_734_, v_k_735_);
lean_dec_ref(v_k_735_);
lean_dec_ref(v_vals_733_);
lean_dec_ref(v_keys_732_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* v_x_737_, size_t v_x_738_, lean_object* v_x_739_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
lean_object* v_es_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_761_; 
v_es_740_ = lean_ctor_get(v_x_737_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_761_ == 0)
{
v___x_742_ = v_x_737_;
v_isShared_743_ = v_isSharedCheck_761_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_es_740_);
lean_dec(v_x_737_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_761_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; lean_object* v_j_748_; lean_object* v___x_749_; 
v___x_744_ = lean_box(2);
v___x_745_ = ((size_t)5ULL);
v___x_746_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1);
v___x_747_ = lean_usize_land(v_x_738_, v___x_746_);
v_j_748_ = lean_usize_to_nat(v___x_747_);
v___x_749_ = lean_array_get(v___x_744_, v_es_740_, v_j_748_);
lean_dec(v_j_748_);
lean_dec_ref(v_es_740_);
switch(lean_obj_tag(v___x_749_))
{
case 0:
{
lean_object* v_key_750_; lean_object* v_val_751_; uint8_t v___x_752_; 
v_key_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_key_750_);
v_val_751_ = lean_ctor_get(v___x_749_, 1);
lean_inc(v_val_751_);
lean_dec_ref(v___x_749_);
v___x_752_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_739_, v_key_750_);
lean_dec(v_key_750_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec(v_val_751_);
lean_del_object(v___x_742_);
v___x_753_ = lean_box(0);
return v___x_753_;
}
else
{
lean_object* v___x_755_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 0, v_val_751_);
v___x_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_val_751_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
case 1:
{
lean_object* v_node_757_; size_t v___x_758_; 
lean_del_object(v___x_742_);
v_node_757_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_node_757_);
lean_dec_ref(v___x_749_);
v___x_758_ = lean_usize_shift_right(v_x_738_, v___x_745_);
v_x_737_ = v_node_757_;
v_x_738_ = v___x_758_;
goto _start;
}
default: 
{
lean_object* v___x_760_; 
lean_del_object(v___x_742_);
v___x_760_ = lean_box(0);
return v___x_760_;
}
}
}
}
else
{
lean_object* v_ks_762_; lean_object* v_vs_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_ks_762_ = lean_ctor_get(v_x_737_, 0);
lean_inc_ref(v_ks_762_);
v_vs_763_ = lean_ctor_get(v_x_737_, 1);
lean_inc_ref(v_vs_763_);
lean_dec_ref(v_x_737_);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_ks_762_, v_vs_763_, v___x_764_, v_x_739_);
lean_dec_ref(v_vs_763_);
lean_dec_ref(v_ks_762_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
size_t v_x_118975__boxed_769_; lean_object* v_res_770_; 
v_x_118975__boxed_769_ = lean_unbox_usize(v_x_767_);
lean_dec(v_x_767_);
v_res_770_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_766_, v_x_118975__boxed_769_, v_x_768_);
lean_dec_ref(v_x_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
uint64_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
v___x_773_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_772_);
v___x_774_ = lean_uint64_to_usize(v___x_773_);
v___x_775_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_771_, v___x_774_, v_x_772_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_776_, v_x_777_);
lean_dec_ref(v_x_777_);
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
lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v___y_840_; uint8_t v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; uint8_t v___y_844_; lean_object* v___y_847_; uint8_t v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; uint8_t v___y_851_; lean_object* v_e_u2082_854_; lean_object* v_h_u2081_855_; uint8_t v_cd_u2081_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; uint8_t v___y_974_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; uint8_t v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; uint8_t v___y_987_; lean_object* v___y_988_; uint8_t v___y_989_; lean_object* v___y_991_; uint8_t v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; uint8_t v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v_a_1002_; lean_object* v___y_1006_; uint8_t v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; uint8_t v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; uint8_t v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; uint8_t v___y_1030_; lean_object* v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; uint8_t v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; uint8_t v___y_1047_; lean_object* v___y_1048_; uint8_t v___y_1049_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; uint8_t v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; uint8_t v___y_1064_; lean_object* v___y_1065_; uint8_t v___y_1066_; lean_object* v_fileName_1068_; lean_object* v_fileMap_1069_; lean_object* v_options_1070_; lean_object* v_currRecDepth_1071_; lean_object* v_maxRecDepth_1072_; lean_object* v_ref_1073_; lean_object* v_currNamespace_1074_; lean_object* v_openDecls_1075_; lean_object* v_initHeartbeats_1076_; lean_object* v_maxHeartbeats_1077_; lean_object* v_quotContext_1078_; lean_object* v_currMacroScope_1079_; uint8_t v_diag_1080_; lean_object* v_cancelTk_x3f_1081_; uint8_t v_suppressElabErrors_1082_; lean_object* v_inheritedTraceOptions_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1379_; 
v_fileName_1068_ = lean_ctor_get(v_a_802_, 0);
v_fileMap_1069_ = lean_ctor_get(v_a_802_, 1);
v_options_1070_ = lean_ctor_get(v_a_802_, 2);
v_currRecDepth_1071_ = lean_ctor_get(v_a_802_, 3);
v_maxRecDepth_1072_ = lean_ctor_get(v_a_802_, 4);
v_ref_1073_ = lean_ctor_get(v_a_802_, 5);
v_currNamespace_1074_ = lean_ctor_get(v_a_802_, 6);
v_openDecls_1075_ = lean_ctor_get(v_a_802_, 7);
v_initHeartbeats_1076_ = lean_ctor_get(v_a_802_, 8);
v_maxHeartbeats_1077_ = lean_ctor_get(v_a_802_, 9);
v_quotContext_1078_ = lean_ctor_get(v_a_802_, 10);
v_currMacroScope_1079_ = lean_ctor_get(v_a_802_, 11);
v_diag_1080_ = lean_ctor_get_uint8(v_a_802_, sizeof(void*)*14);
v_cancelTk_x3f_1081_ = lean_ctor_get(v_a_802_, 12);
v_suppressElabErrors_1082_ = lean_ctor_get_uint8(v_a_802_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1083_ = lean_ctor_get(v_a_802_, 13);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_a_802_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1085_ = v_a_802_;
v_isShared_1086_ = v_isSharedCheck_1379_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_inheritedTraceOptions_1083_);
lean_inc(v_cancelTk_x3f_1081_);
lean_inc(v_currMacroScope_1079_);
lean_inc(v_quotContext_1078_);
lean_inc(v_maxHeartbeats_1077_);
lean_inc(v_initHeartbeats_1076_);
lean_inc(v_openDecls_1075_);
lean_inc(v_currNamespace_1074_);
lean_inc(v_ref_1073_);
lean_inc(v_maxRecDepth_1072_);
lean_inc(v_currRecDepth_1071_);
lean_inc(v_options_1070_);
lean_inc(v_fileMap_1069_);
lean_inc(v_fileName_1068_);
lean_dec(v_a_802_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1379_;
goto v_resetjp_1084_;
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
v___x_820_ = lean_st_ref_set(v___y_807_, v___x_819_);
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
v___x_835_ = lean_st_ref_set(v___y_807_, v___x_834_);
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
lean_ctor_set(v___x_845_, 0, v___y_843_);
lean_ctor_set(v___x_845_, 1, v___y_840_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*2, v___y_841_);
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
lean_ctor_set(v___x_852_, 0, v___y_849_);
lean_ctor_set(v___x_852_, 1, v___y_847_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*2, v___y_848_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*2 + 1, v___y_851_);
v___y_806_ = v___x_852_;
v___y_807_ = v___y_850_;
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
lean_inc(v___y_859_);
lean_inc_ref(v_e_u2082_854_);
v___x_866_ = lean_sym_simp(v_e_u2082_854_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
if (lean_obj_tag(v_a_867_) == 0)
{
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
if (v_cd_u2081_856_ == 0)
{
uint8_t v_done_868_; uint8_t v_contextDependent_869_; 
v_done_868_ = lean_ctor_get_uint8(v_a_867_, 0);
v_contextDependent_869_ = lean_ctor_get_uint8(v_a_867_, 1);
lean_dec_ref(v_a_867_);
v___y_840_ = v_h_u2081_855_;
v___y_841_ = v_done_868_;
v___y_842_ = v___y_859_;
v___y_843_ = v_e_u2082_854_;
v___y_844_ = v_contextDependent_869_;
goto v___jp_839_;
}
else
{
uint8_t v_done_870_; 
v_done_870_ = lean_ctor_get_uint8(v_a_867_, 0);
lean_dec_ref(v_a_867_);
v___y_840_ = v_h_u2081_855_;
v___y_841_ = v_done_870_;
v___y_842_ = v___y_859_;
v___y_843_ = v_e_u2082_854_;
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
lean_dec_ref(v_a_867_);
lean_inc_ref(v_e_u2081_794_);
v___x_875_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_794_, v_e_u2082_854_, v_h_u2081_855_, v_e_x27_871_, v_proof_872_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
if (lean_obj_tag(v___x_875_) == 0)
{
if (v_cd_u2081_856_ == 0)
{
lean_object* v_a_876_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___y_847_ = v_a_876_;
v___y_848_ = v_done_873_;
v___y_849_ = v_e_x27_871_;
v___y_850_ = v___y_859_;
v___y_851_ = v_contextDependent_874_;
goto v___jp_846_;
}
else
{
lean_object* v_a_877_; 
v_a_877_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v___x_875_);
v___y_847_ = v_a_877_;
v___y_848_ = v_done_873_;
v___y_849_ = v_e_x27_871_;
v___y_850_ = v___y_859_;
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
lean_dec(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec(v___y_887_);
v_contextDependent_897_ = lean_ctor_get_uint8(v___y_896_, 1);
if (v_contextDependent_897_ == 0)
{
lean_object* v___x_898_; lean_object* v_numSteps_899_; lean_object* v_persistentCache_900_; lean_object* v_transientCache_901_; lean_object* v_funext_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v___x_898_ = lean_st_ref_take(v___y_890_);
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
v___x_909_ = lean_st_ref_set(v___y_890_, v___x_908_);
lean_dec(v___y_890_);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___y_896_);
return v___x_910_;
}
}
}
else
{
lean_object* v___x_913_; lean_object* v_numSteps_914_; lean_object* v_persistentCache_915_; lean_object* v_transientCache_916_; lean_object* v_funext_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_927_; 
v___x_913_ = lean_st_ref_take(v___y_890_);
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
v___x_924_ = lean_st_ref_set(v___y_890_, v___x_923_);
lean_dec(v___y_890_);
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
lean_dec_ref(v___y_896_);
v_e_u2082_854_ = v_e_x27_929_;
v_h_u2081_855_ = v_proof_930_;
v_cd_u2081_856_ = v_contextDependent_931_;
v___y_857_ = v___y_893_;
v___y_858_ = v___y_892_;
v___y_859_ = v___y_890_;
v___y_860_ = v___y_889_;
v___y_861_ = v___y_887_;
v___y_862_ = v___y_895_;
v___y_863_ = v___y_894_;
v___y_864_ = v___y_891_;
v___y_865_ = v___y_888_;
goto v___jp_853_;
}
else
{
uint8_t v_contextDependent_932_; 
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec(v___y_887_);
v_contextDependent_932_ = lean_ctor_get_uint8(v___y_896_, sizeof(void*)*2 + 1);
if (v_contextDependent_932_ == 0)
{
lean_object* v___x_933_; lean_object* v_numSteps_934_; lean_object* v_persistentCache_935_; lean_object* v_transientCache_936_; lean_object* v_funext_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v___x_933_ = lean_st_ref_take(v___y_890_);
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
v___x_944_ = lean_st_ref_set(v___y_890_, v___x_943_);
lean_dec(v___y_890_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___y_896_);
return v___x_945_;
}
}
}
else
{
lean_object* v___x_948_; lean_object* v_numSteps_949_; lean_object* v_persistentCache_950_; lean_object* v_transientCache_951_; lean_object* v_funext_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_962_; 
v___x_948_ = lean_st_ref_take(v___y_890_);
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
v___x_959_ = lean_st_ref_set(v___y_890_, v___x_958_);
lean_dec(v___y_890_);
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
v___y_887_ = v___y_964_;
v___y_888_ = v___y_967_;
v___y_889_ = v___y_966_;
v___y_890_ = v___y_965_;
v___y_891_ = v___y_969_;
v___y_892_ = v___y_970_;
v___y_893_ = v___y_971_;
v___y_894_ = v___y_973_;
v___y_895_ = v___y_972_;
v___y_896_ = v___y_968_;
goto v___jp_886_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_968_);
v___y_887_ = v___y_964_;
v___y_888_ = v___y_967_;
v___y_889_ = v___y_966_;
v___y_890_ = v___y_965_;
v___y_891_ = v___y_969_;
v___y_892_ = v___y_970_;
v___y_893_ = v___y_971_;
v___y_894_ = v___y_973_;
v___y_895_ = v___y_972_;
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
v___y_966_ = v___y_978_;
v___y_967_ = v___y_985_;
v___y_968_ = v___y_979_;
v___y_969_ = v___y_980_;
v___y_970_ = v___y_986_;
v___y_971_ = v___y_981_;
v___y_972_ = v___y_988_;
v___y_973_ = v___y_982_;
v___y_974_ = v___y_987_;
goto v___jp_963_;
}
else
{
v___y_964_ = v___y_977_;
v___y_965_ = v___y_984_;
v___y_966_ = v___y_978_;
v___y_967_ = v___y_985_;
v___y_968_ = v___y_979_;
v___y_969_ = v___y_980_;
v___y_970_ = v___y_986_;
v___y_971_ = v___y_981_;
v___y_972_ = v___y_988_;
v___y_973_ = v___y_982_;
v___y_974_ = v___y_983_;
goto v___jp_963_;
}
}
v___jp_990_:
{
if (v___y_998_ == 0)
{
v___y_887_ = v___y_991_;
v___y_888_ = v___y_995_;
v___y_889_ = v___y_994_;
v___y_890_ = v___y_993_;
v___y_891_ = v___y_996_;
v___y_892_ = v___y_997_;
v___y_893_ = v___y_999_;
v___y_894_ = v___y_1001_;
v___y_895_ = v___y_1000_;
v___y_896_ = v_a_1002_;
goto v___jp_886_;
}
else
{
if (lean_obj_tag(v_a_1002_) == 0)
{
uint8_t v_contextDependent_1003_; 
v_contextDependent_1003_ = lean_ctor_get_uint8(v_a_1002_, 1);
v___y_977_ = v___y_991_;
v___y_978_ = v___y_994_;
v___y_979_ = v_a_1002_;
v___y_980_ = v___y_996_;
v___y_981_ = v___y_999_;
v___y_982_ = v___y_1001_;
v___y_983_ = v___y_992_;
v___y_984_ = v___y_993_;
v___y_985_ = v___y_995_;
v___y_986_ = v___y_997_;
v___y_987_ = v___y_998_;
v___y_988_ = v___y_1000_;
v___y_989_ = v_contextDependent_1003_;
goto v___jp_976_;
}
else
{
uint8_t v_contextDependent_1004_; 
v_contextDependent_1004_ = lean_ctor_get_uint8(v_a_1002_, sizeof(void*)*2 + 1);
v___y_977_ = v___y_991_;
v___y_978_ = v___y_994_;
v___y_979_ = v_a_1002_;
v___y_980_ = v___y_996_;
v___y_981_ = v___y_999_;
v___y_982_ = v___y_1001_;
v___y_983_ = v___y_992_;
v___y_984_ = v___y_993_;
v___y_985_ = v___y_995_;
v___y_986_ = v___y_997_;
v___y_987_ = v___y_998_;
v___y_988_ = v___y_1000_;
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
lean_dec_ref(v___y_1017_);
v___y_991_ = v___y_1006_;
v___y_992_ = v___y_1007_;
v___y_993_ = v___y_1010_;
v___y_994_ = v___y_1009_;
v___y_995_ = v___y_1008_;
v___y_996_ = v___y_1011_;
v___y_997_ = v___y_1012_;
v___y_998_ = v___y_1013_;
v___y_999_ = v___y_1014_;
v___y_1000_ = v___y_1016_;
v___y_1001_ = v___y_1015_;
v_a_1002_ = v_a_1018_;
goto v___jp_990_;
}
else
{
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
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
v___x_1033_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1025_);
v___y_991_ = v___y_1020_;
v___y_992_ = v___y_1026_;
v___y_993_ = v___y_1027_;
v___y_994_ = v___y_1021_;
v___y_995_ = v___y_1028_;
v___y_996_ = v___y_1022_;
v___y_997_ = v___y_1029_;
v___y_998_ = v___y_1030_;
v___y_999_ = v___y_1023_;
v___y_1000_ = v___y_1031_;
v___y_1001_ = v___y_1024_;
v_a_1002_ = v___x_1033_;
goto v___jp_990_;
}
else
{
v___y_991_ = v___y_1020_;
v___y_992_ = v___y_1026_;
v___y_993_ = v___y_1027_;
v___y_994_ = v___y_1021_;
v___y_995_ = v___y_1028_;
v___y_996_ = v___y_1022_;
v___y_997_ = v___y_1029_;
v___y_998_ = v___y_1030_;
v___y_999_ = v___y_1023_;
v___y_1000_ = v___y_1031_;
v___y_1001_ = v___y_1024_;
v_a_1002_ = v___y_1025_;
goto v___jp_990_;
}
}
v___jp_1034_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1050_, 0, v___y_1038_);
lean_ctor_set(v___x_1050_, 1, v___y_1035_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*2, v___y_1040_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*2 + 1, v___y_1049_);
v___y_991_ = v___y_1036_;
v___y_992_ = v___y_1043_;
v___y_993_ = v___y_1044_;
v___y_994_ = v___y_1037_;
v___y_995_ = v___y_1045_;
v___y_996_ = v___y_1039_;
v___y_997_ = v___y_1046_;
v___y_998_ = v___y_1047_;
v___y_999_ = v___y_1041_;
v___y_1000_ = v___y_1048_;
v___y_1001_ = v___y_1042_;
v_a_1002_ = v___x_1050_;
goto v___jp_990_;
}
v___jp_1051_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1067_, 0, v___y_1058_);
lean_ctor_set(v___x_1067_, 1, v___y_1052_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*2, v___y_1064_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*2 + 1, v___y_1066_);
v___y_991_ = v___y_1053_;
v___y_992_ = v___y_1059_;
v___y_993_ = v___y_1060_;
v___y_994_ = v___y_1054_;
v___y_995_ = v___y_1061_;
v___y_996_ = v___y_1055_;
v___y_997_ = v___y_1062_;
v___y_998_ = v___y_1063_;
v___y_999_ = v___y_1056_;
v___y_1000_ = v___y_1065_;
v___y_1001_ = v___y_1057_;
v_a_1002_ = v___x_1067_;
goto v___jp_990_;
}
v_resetjp_1084_:
{
lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = lean_nat_dec_eq(v_maxRecDepth_1072_, v___x_1375_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_nat_dec_eq(v_currRecDepth_1071_, v_maxRecDepth_1072_);
if (v___x_1377_ == 0)
{
goto v___jp_1345_;
}
else
{
lean_object* v___x_1378_; 
lean_del_object(v___x_1085_);
lean_dec_ref(v_inheritedTraceOptions_1083_);
lean_dec(v_cancelTk_x3f_1081_);
lean_dec(v_currMacroScope_1079_);
lean_dec(v_quotContext_1078_);
lean_dec(v_maxHeartbeats_1077_);
lean_dec(v_initHeartbeats_1076_);
lean_dec(v_openDecls_1075_);
lean_dec(v_currNamespace_1074_);
lean_dec(v_maxRecDepth_1072_);
lean_dec(v_currRecDepth_1071_);
lean_dec_ref(v_options_1070_);
lean_dec_ref(v_fileMap_1069_);
lean_dec_ref(v_fileName_1068_);
lean_dec(v_a_803_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_e_u2081_794_);
v___x_1378_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_1073_);
return v___x_1378_;
}
}
else
{
goto v___jp_1345_;
}
v___jp_1087_:
{
lean_object* v___x_1098_; lean_object* v_persistentCache_1099_; lean_object* v_transientCache_1100_; lean_object* v_funext_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1226_; 
v___x_1098_ = lean_st_ref_take(v___y_1091_);
v_persistentCache_1099_ = lean_ctor_get(v___x_1098_, 1);
v_transientCache_1100_ = lean_ctor_get(v___x_1098_, 2);
v_funext_1101_ = lean_ctor_get(v___x_1098_, 3);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v___x_1098_, 0);
lean_dec(v_unused_1227_);
v___x_1103_ = v___x_1098_;
v_isShared_1104_ = v_isSharedCheck_1226_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_funext_1101_);
lean_inc(v_transientCache_1100_);
lean_inc(v_persistentCache_1099_);
lean_dec(v___x_1098_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1226_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___y_1088_);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___y_1088_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_persistentCache_1099_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_transientCache_1100_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_funext_1101_);
v___x_1106_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v_pre_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_st_ref_set(v___y_1091_, v___x_1106_);
v_pre_1108_ = lean_ctor_get(v___y_1089_, 0);
lean_inc_ref(v_pre_1108_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1094_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1089_);
lean_inc_ref(v_e_u2081_794_);
v___x_1109_ = lean_apply_11(v_pre_1108_, v_e_u2081_794_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, lean_box(0));
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1224_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1224_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1224_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
if (lean_obj_tag(v_a_1110_) == 0)
{
uint8_t v_done_1114_; 
v_done_1114_ = lean_ctor_get_uint8(v_a_1110_, 0);
if (v_done_1114_ == 0)
{
uint8_t v_contextDependent_1115_; lean_object* v___x_1116_; 
lean_del_object(v___x_1112_);
v_contextDependent_1115_ = lean_ctor_get_uint8(v_a_1110_, 1);
lean_dec_ref(v_a_1110_);
lean_inc_ref(v_e_u2081_794_);
v___x_1116_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_u2081_794_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
v___x_1118_ = lean_box(0);
if (lean_obj_tag(v_a_1117_) == 0)
{
uint8_t v_done_1119_; 
v_done_1119_ = lean_ctor_get_uint8(v_a_1117_, 0);
if (v_done_1119_ == 0)
{
uint8_t v_contextDependent_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v___x_1116_);
v_contextDependent_1120_ = lean_ctor_get_uint8(v_a_1117_, 1);
lean_dec_ref(v_a_1117_);
lean_inc_ref(v_e_u2081_794_);
v___x_1121_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1118_, v_e_u2081_794_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1121_) == 0)
{
if (v_contextDependent_1120_ == 0)
{
lean_object* v_a_1122_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1121_);
v___y_991_ = v___y_1093_;
v___y_992_ = v_done_1114_;
v___y_993_ = v___y_1091_;
v___y_994_ = v___y_1092_;
v___y_995_ = v___y_1097_;
v___y_996_ = v___y_1096_;
v___y_997_ = v___y_1090_;
v___y_998_ = v_contextDependent_1115_;
v___y_999_ = v___y_1089_;
v___y_1000_ = v___y_1094_;
v___y_1001_ = v___y_1095_;
v_a_1002_ = v_a_1122_;
goto v___jp_990_;
}
else
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1121_);
if (lean_obj_tag(v_a_1123_) == 0)
{
uint8_t v_contextDependent_1124_; 
v_contextDependent_1124_ = lean_ctor_get_uint8(v_a_1123_, 1);
v___y_1020_ = v___y_1093_;
v___y_1021_ = v___y_1092_;
v___y_1022_ = v___y_1096_;
v___y_1023_ = v___y_1089_;
v___y_1024_ = v___y_1095_;
v___y_1025_ = v_a_1123_;
v___y_1026_ = v_done_1114_;
v___y_1027_ = v___y_1091_;
v___y_1028_ = v___y_1097_;
v___y_1029_ = v___y_1090_;
v___y_1030_ = v_contextDependent_1115_;
v___y_1031_ = v___y_1094_;
v___y_1032_ = v_contextDependent_1124_;
goto v___jp_1019_;
}
else
{
uint8_t v_contextDependent_1125_; 
v_contextDependent_1125_ = lean_ctor_get_uint8(v_a_1123_, sizeof(void*)*2 + 1);
v___y_1020_ = v___y_1093_;
v___y_1021_ = v___y_1092_;
v___y_1022_ = v___y_1096_;
v___y_1023_ = v___y_1089_;
v___y_1024_ = v___y_1095_;
v___y_1025_ = v_a_1123_;
v___y_1026_ = v_done_1114_;
v___y_1027_ = v___y_1091_;
v___y_1028_ = v___y_1097_;
v___y_1029_ = v___y_1090_;
v___y_1030_ = v_contextDependent_1115_;
v___y_1031_ = v___y_1094_;
v___y_1032_ = v_contextDependent_1125_;
goto v___jp_1019_;
}
}
}
else
{
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v_e_u2081_794_);
return v___x_1121_;
}
}
else
{
lean_dec_ref(v_a_1117_);
v___y_1006_ = v___y_1093_;
v___y_1007_ = v_done_1114_;
v___y_1008_ = v___y_1097_;
v___y_1009_ = v___y_1092_;
v___y_1010_ = v___y_1091_;
v___y_1011_ = v___y_1096_;
v___y_1012_ = v___y_1090_;
v___y_1013_ = v_contextDependent_1115_;
v___y_1014_ = v___y_1089_;
v___y_1015_ = v___y_1095_;
v___y_1016_ = v___y_1094_;
v___y_1017_ = v___x_1116_;
goto v___jp_1005_;
}
}
else
{
uint8_t v_done_1126_; 
v_done_1126_ = lean_ctor_get_uint8(v_a_1117_, sizeof(void*)*2);
if (v_done_1126_ == 0)
{
lean_object* v_e_x27_1127_; lean_object* v_proof_1128_; uint8_t v_contextDependent_1129_; lean_object* v___x_1130_; 
lean_dec_ref(v___x_1116_);
v_e_x27_1127_ = lean_ctor_get(v_a_1117_, 0);
lean_inc_ref_n(v_e_x27_1127_, 2);
v_proof_1128_ = lean_ctor_get(v_a_1117_, 1);
lean_inc_ref(v_proof_1128_);
v_contextDependent_1129_ = lean_ctor_get_uint8(v_a_1117_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1117_);
v___x_1130_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1118_, v_e_x27_1127_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
if (lean_obj_tag(v_a_1131_) == 0)
{
if (v_contextDependent_1129_ == 0)
{
uint8_t v_done_1132_; uint8_t v_contextDependent_1133_; 
v_done_1132_ = lean_ctor_get_uint8(v_a_1131_, 0);
v_contextDependent_1133_ = lean_ctor_get_uint8(v_a_1131_, 1);
lean_dec_ref(v_a_1131_);
v___y_1035_ = v_proof_1128_;
v___y_1036_ = v___y_1093_;
v___y_1037_ = v___y_1092_;
v___y_1038_ = v_e_x27_1127_;
v___y_1039_ = v___y_1096_;
v___y_1040_ = v_done_1132_;
v___y_1041_ = v___y_1089_;
v___y_1042_ = v___y_1095_;
v___y_1043_ = v_done_1114_;
v___y_1044_ = v___y_1091_;
v___y_1045_ = v___y_1097_;
v___y_1046_ = v___y_1090_;
v___y_1047_ = v_contextDependent_1115_;
v___y_1048_ = v___y_1094_;
v___y_1049_ = v_contextDependent_1133_;
goto v___jp_1034_;
}
else
{
uint8_t v_done_1134_; 
v_done_1134_ = lean_ctor_get_uint8(v_a_1131_, 0);
lean_dec_ref(v_a_1131_);
v___y_1035_ = v_proof_1128_;
v___y_1036_ = v___y_1093_;
v___y_1037_ = v___y_1092_;
v___y_1038_ = v_e_x27_1127_;
v___y_1039_ = v___y_1096_;
v___y_1040_ = v_done_1134_;
v___y_1041_ = v___y_1089_;
v___y_1042_ = v___y_1095_;
v___y_1043_ = v_done_1114_;
v___y_1044_ = v___y_1091_;
v___y_1045_ = v___y_1097_;
v___y_1046_ = v___y_1090_;
v___y_1047_ = v_contextDependent_1115_;
v___y_1048_ = v___y_1094_;
v___y_1049_ = v_contextDependent_1129_;
goto v___jp_1034_;
}
}
else
{
lean_object* v_e_x27_1135_; lean_object* v_proof_1136_; uint8_t v_done_1137_; uint8_t v_contextDependent_1138_; lean_object* v___x_1139_; 
v_e_x27_1135_ = lean_ctor_get(v_a_1131_, 0);
lean_inc_ref_n(v_e_x27_1135_, 2);
v_proof_1136_ = lean_ctor_get(v_a_1131_, 1);
lean_inc_ref(v_proof_1136_);
v_done_1137_ = lean_ctor_get_uint8(v_a_1131_, sizeof(void*)*2);
v_contextDependent_1138_ = lean_ctor_get_uint8(v_a_1131_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1131_);
lean_inc_ref(v_e_u2081_794_);
v___x_1139_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_794_, v_e_x27_1127_, v_proof_1128_, v_e_x27_1135_, v_proof_1136_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1139_) == 0)
{
if (v_contextDependent_1129_ == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref(v___x_1139_);
v___y_1052_ = v_a_1140_;
v___y_1053_ = v___y_1093_;
v___y_1054_ = v___y_1092_;
v___y_1055_ = v___y_1096_;
v___y_1056_ = v___y_1089_;
v___y_1057_ = v___y_1095_;
v___y_1058_ = v_e_x27_1135_;
v___y_1059_ = v_done_1114_;
v___y_1060_ = v___y_1091_;
v___y_1061_ = v___y_1097_;
v___y_1062_ = v___y_1090_;
v___y_1063_ = v_contextDependent_1115_;
v___y_1064_ = v_done_1137_;
v___y_1065_ = v___y_1094_;
v___y_1066_ = v_contextDependent_1138_;
goto v___jp_1051_;
}
else
{
lean_object* v_a_1141_; 
v_a_1141_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v___x_1139_);
v___y_1052_ = v_a_1141_;
v___y_1053_ = v___y_1093_;
v___y_1054_ = v___y_1092_;
v___y_1055_ = v___y_1096_;
v___y_1056_ = v___y_1089_;
v___y_1057_ = v___y_1095_;
v___y_1058_ = v_e_x27_1135_;
v___y_1059_ = v_done_1114_;
v___y_1060_ = v___y_1091_;
v___y_1061_ = v___y_1097_;
v___y_1062_ = v___y_1090_;
v___y_1063_ = v_contextDependent_1115_;
v___y_1064_ = v_done_1137_;
v___y_1065_ = v___y_1094_;
v___y_1066_ = v_contextDependent_1129_;
goto v___jp_1051_;
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_e_x27_1135_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v_e_u2081_794_);
v_a_1142_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1139_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1128_);
lean_dec_ref(v_e_x27_1127_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v_e_u2081_794_);
return v___x_1130_;
}
}
else
{
lean_dec_ref(v_a_1117_);
v___y_1006_ = v___y_1093_;
v___y_1007_ = v_done_1114_;
v___y_1008_ = v___y_1097_;
v___y_1009_ = v___y_1092_;
v___y_1010_ = v___y_1091_;
v___y_1011_ = v___y_1096_;
v___y_1012_ = v___y_1090_;
v___y_1013_ = v_contextDependent_1115_;
v___y_1014_ = v___y_1089_;
v___y_1015_ = v___y_1095_;
v___y_1016_ = v___y_1094_;
v___y_1017_ = v___x_1116_;
goto v___jp_1005_;
}
}
}
else
{
v___y_1006_ = v___y_1093_;
v___y_1007_ = v_done_1114_;
v___y_1008_ = v___y_1097_;
v___y_1009_ = v___y_1092_;
v___y_1010_ = v___y_1091_;
v___y_1011_ = v___y_1096_;
v___y_1012_ = v___y_1090_;
v___y_1013_ = v_contextDependent_1115_;
v___y_1014_ = v___y_1089_;
v___y_1015_ = v___y_1095_;
v___y_1016_ = v___y_1094_;
v___y_1017_ = v___x_1116_;
goto v___jp_1005_;
}
}
else
{
uint8_t v_contextDependent_1150_; 
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
v_contextDependent_1150_ = lean_ctor_get_uint8(v_a_1110_, 1);
if (v_contextDependent_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v_numSteps_1152_; lean_object* v_persistentCache_1153_; lean_object* v_transientCache_1154_; lean_object* v_funext_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1167_; 
v___x_1151_ = lean_st_ref_take(v___y_1091_);
v_numSteps_1152_ = lean_ctor_get(v___x_1151_, 0);
v_persistentCache_1153_ = lean_ctor_get(v___x_1151_, 1);
v_transientCache_1154_ = lean_ctor_get(v___x_1151_, 2);
v_funext_1155_ = lean_ctor_get(v___x_1151_, 3);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1157_ = v___x_1151_;
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_funext_1155_);
lean_inc(v_transientCache_1154_);
lean_inc(v_persistentCache_1153_);
lean_inc(v_numSteps_1152_);
lean_dec(v___x_1151_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_inc_ref(v_a_1110_);
v___x_1159_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1153_, v_e_u2081_794_, v_a_1110_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_numSteps_1152_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_transientCache_1154_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_funext_1155_);
v___x_1161_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_st_ref_set(v___y_1091_, v___x_1161_);
lean_dec(v___y_1091_);
if (v_isShared_1113_ == 0)
{
v___x_1164_ = v___x_1112_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1110_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v_numSteps_1169_; lean_object* v_persistentCache_1170_; lean_object* v_transientCache_1171_; lean_object* v_funext_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1184_; 
v___x_1168_ = lean_st_ref_take(v___y_1091_);
v_numSteps_1169_ = lean_ctor_get(v___x_1168_, 0);
v_persistentCache_1170_ = lean_ctor_get(v___x_1168_, 1);
v_transientCache_1171_ = lean_ctor_get(v___x_1168_, 2);
v_funext_1172_ = lean_ctor_get(v___x_1168_, 3);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1174_ = v___x_1168_;
v_isShared_1175_ = v_isSharedCheck_1184_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_funext_1172_);
lean_inc(v_transientCache_1171_);
lean_inc(v_persistentCache_1170_);
lean_inc(v_numSteps_1169_);
lean_dec(v___x_1168_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1184_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_inc_ref(v_a_1110_);
v___x_1176_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1171_, v_e_u2081_794_, v_a_1110_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 2, v___x_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_numSteps_1169_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_persistentCache_1170_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_funext_1172_);
v___x_1178_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_st_ref_set(v___y_1091_, v___x_1178_);
lean_dec(v___y_1091_);
if (v_isShared_1113_ == 0)
{
v___x_1181_ = v___x_1112_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1110_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
else
{
uint8_t v_done_1185_; 
v_done_1185_ = lean_ctor_get_uint8(v_a_1110_, sizeof(void*)*2);
if (v_done_1185_ == 0)
{
lean_object* v_e_x27_1186_; lean_object* v_proof_1187_; uint8_t v_contextDependent_1188_; 
lean_del_object(v___x_1112_);
v_e_x27_1186_ = lean_ctor_get(v_a_1110_, 0);
lean_inc_ref(v_e_x27_1186_);
v_proof_1187_ = lean_ctor_get(v_a_1110_, 1);
lean_inc_ref(v_proof_1187_);
v_contextDependent_1188_ = lean_ctor_get_uint8(v_a_1110_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1110_);
v_e_u2082_854_ = v_e_x27_1186_;
v_h_u2081_855_ = v_proof_1187_;
v_cd_u2081_856_ = v_contextDependent_1188_;
v___y_857_ = v___y_1089_;
v___y_858_ = v___y_1090_;
v___y_859_ = v___y_1091_;
v___y_860_ = v___y_1092_;
v___y_861_ = v___y_1093_;
v___y_862_ = v___y_1094_;
v___y_863_ = v___y_1095_;
v___y_864_ = v___y_1096_;
v___y_865_ = v___y_1097_;
goto v___jp_853_;
}
else
{
uint8_t v_contextDependent_1189_; 
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
v_contextDependent_1189_ = lean_ctor_get_uint8(v_a_1110_, sizeof(void*)*2 + 1);
if (v_contextDependent_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v_numSteps_1191_; lean_object* v_persistentCache_1192_; lean_object* v_transientCache_1193_; lean_object* v_funext_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1206_; 
v___x_1190_ = lean_st_ref_take(v___y_1091_);
v_numSteps_1191_ = lean_ctor_get(v___x_1190_, 0);
v_persistentCache_1192_ = lean_ctor_get(v___x_1190_, 1);
v_transientCache_1193_ = lean_ctor_get(v___x_1190_, 2);
v_funext_1194_ = lean_ctor_get(v___x_1190_, 3);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1196_ = v___x_1190_;
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_funext_1194_);
lean_inc(v_transientCache_1193_);
lean_inc(v_persistentCache_1192_);
lean_inc(v_numSteps_1191_);
lean_dec(v___x_1190_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
lean_inc_ref(v_a_1110_);
v___x_1198_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1192_, v_e_u2081_794_, v_a_1110_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_numSteps_1191_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_transientCache_1193_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_funext_1194_);
v___x_1200_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_st_ref_set(v___y_1091_, v___x_1200_);
lean_dec(v___y_1091_);
if (v_isShared_1113_ == 0)
{
v___x_1203_ = v___x_1112_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1110_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v___x_1207_; lean_object* v_numSteps_1208_; lean_object* v_persistentCache_1209_; lean_object* v_transientCache_1210_; lean_object* v_funext_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1223_; 
v___x_1207_ = lean_st_ref_take(v___y_1091_);
v_numSteps_1208_ = lean_ctor_get(v___x_1207_, 0);
v_persistentCache_1209_ = lean_ctor_get(v___x_1207_, 1);
v_transientCache_1210_ = lean_ctor_get(v___x_1207_, 2);
v_funext_1211_ = lean_ctor_get(v___x_1207_, 3);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1213_ = v___x_1207_;
v_isShared_1214_ = v_isSharedCheck_1223_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_funext_1211_);
lean_inc(v_transientCache_1210_);
lean_inc(v_persistentCache_1209_);
lean_inc(v_numSteps_1208_);
lean_dec(v___x_1207_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1223_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_inc_ref(v_a_1110_);
v___x_1215_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1210_, v_e_u2081_794_, v_a_1110_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 2, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_numSteps_1208_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_persistentCache_1209_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_funext_1211_);
v___x_1217_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_st_ref_set(v___y_1091_, v___x_1217_);
lean_dec(v___y_1091_);
if (v_isShared_1113_ == 0)
{
v___x_1220_ = v___x_1112_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1110_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
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
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v_e_u2081_794_);
return v___x_1109_;
}
}
}
}
v___jp_1228_:
{
lean_object* v___x_1240_; lean_object* v_persistentCache_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_st_ref_get(v___y_1233_);
v_persistentCache_1241_ = lean_ctor_get(v___x_1240_, 1);
lean_inc_ref(v_persistentCache_1241_);
lean_dec(v___x_1240_);
v___x_1242_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_persistentCache_1241_, v_e_u2081_794_);
if (lean_obj_tag(v___x_1242_) == 1)
{
lean_object* v_options_1243_; uint8_t v_hasTrace_1244_; 
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
v_options_1243_ = lean_ctor_get(v___y_1238_, 2);
v_hasTrace_1244_ = lean_ctor_get_uint8(v_options_1243_, sizeof(void*)*1);
if (v_hasTrace_1244_ == 0)
{
lean_object* v_val_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_e_u2081_794_);
v_val_1245_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1242_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_val_1245_);
lean_dec(v___x_1242_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 0);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_val_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v_val_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1284_; 
v_val_1253_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1255_ = v___x_1242_;
v_isShared_1256_ = v_isSharedCheck_1284_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_val_1253_);
lean_dec(v___x_1242_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1284_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v_inheritedTraceOptions_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_inheritedTraceOptions_1257_ = lean_ctor_get(v___y_1238_, 13);
v___x_1258_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1259_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1260_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1257_, v_options_1243_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1262_; 
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_e_u2081_794_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 0);
v___x_1262_ = v___x_1255_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_val_1253_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_del_object(v___x_1255_);
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4);
v___x_1265_ = l_Lean_MessageData_ofExpr(v_e_u2081_794_);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1258_, v___x_1266_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1275_);
v___x_1269_ = v___x_1267_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1267_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_val_1253_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_val_1253_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_val_1253_);
v_a_1276_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1267_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1267_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v_transientCache_1286_; lean_object* v___x_1287_; 
lean_dec(v___x_1242_);
v___x_1285_ = lean_st_ref_get(v___y_1233_);
v_transientCache_1286_ = lean_ctor_get(v___x_1285_, 2);
lean_inc_ref(v_transientCache_1286_);
lean_dec(v___x_1285_);
v___x_1287_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_transientCache_1286_, v_e_u2081_794_);
if (lean_obj_tag(v___x_1287_) == 1)
{
lean_object* v_options_1288_; uint8_t v_hasTrace_1289_; 
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
v_options_1288_ = lean_ctor_get(v___y_1238_, 2);
v_hasTrace_1289_ = lean_ctor_get_uint8(v_options_1288_, sizeof(void*)*1);
if (v_hasTrace_1289_ == 0)
{
lean_object* v_val_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_e_u2081_794_);
v_val_1290_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1287_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_val_1290_);
lean_dec(v___x_1287_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set_tag(v___x_1292_, 0);
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_val_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
lean_object* v_val_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1329_; 
v_val_1298_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1300_ = v___x_1287_;
v_isShared_1301_ = v_isSharedCheck_1329_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_val_1298_);
lean_dec(v___x_1287_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1329_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_inheritedTraceOptions_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_inheritedTraceOptions_1302_ = lean_ctor_get(v___y_1238_, 13);
v___x_1303_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1304_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1305_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1302_, v_options_1288_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1307_; 
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_e_u2081_794_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 0);
v___x_1307_ = v___x_1300_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_val_1298_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_del_object(v___x_1300_);
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6);
v___x_1310_ = l_Lean_MessageData_ofExpr(v_e_u2081_794_);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1303_, v___x_1311_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v___x_1312_, 0);
lean_dec(v_unused_1320_);
v___x_1314_ = v___x_1312_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v___x_1312_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v_val_1298_);
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_val_1298_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_val_1298_);
v_a_1321_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1312_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1312_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
lean_dec(v___x_1287_);
v___x_1330_ = lean_nat_add(v___y_1230_, v___y_1229_);
lean_dec(v___y_1230_);
v___x_1331_ = lean_unsigned_to_nat(1000u);
v___x_1332_ = lean_nat_mod(v___x_1330_, v___x_1331_);
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_nat_dec_eq(v___x_1332_, v___x_1333_);
lean_dec(v___x_1332_);
if (v___x_1334_ == 0)
{
v___y_1088_ = v___x_1330_;
v___y_1089_ = v___y_1231_;
v___y_1090_ = v___y_1232_;
v___y_1091_ = v___y_1233_;
v___y_1092_ = v___y_1234_;
v___y_1093_ = v___y_1235_;
v___y_1094_ = v___y_1236_;
v___y_1095_ = v___y_1237_;
v___y_1096_ = v___y_1238_;
v___y_1097_ = v___y_1239_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1336_ = l_Lean_Core_checkSystem(v___x_1335_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_dec_ref(v___x_1336_);
v___y_1088_ = v___x_1330_;
v___y_1089_ = v___y_1231_;
v___y_1090_ = v___y_1232_;
v___y_1091_ = v___y_1233_;
v___y_1092_ = v___y_1234_;
v___y_1093_ = v___y_1235_;
v___y_1094_ = v___y_1236_;
v___y_1095_ = v___y_1237_;
v___y_1096_ = v___y_1238_;
v___y_1097_ = v___y_1239_;
goto v___jp_1087_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v___x_1330_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v_e_u2081_794_);
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
}
v___jp_1345_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_st_ref_get(v_a_797_);
v___x_1347_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_796_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v_numSteps_1349_; lean_object* v_maxSteps_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
v_numSteps_1349_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_numSteps_1349_);
lean_dec(v___x_1346_);
v_maxSteps_1350_ = lean_ctor_get(v_a_1348_, 0);
lean_inc(v_maxSteps_1350_);
lean_dec(v_a_1348_);
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_nat_add(v_currRecDepth_1071_, v___x_1351_);
lean_dec(v_currRecDepth_1071_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 3, v___x_1352_);
v___x_1354_ = v___x_1085_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_fileName_1068_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_fileMap_1069_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_options_1070_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_maxRecDepth_1072_);
lean_ctor_set(v_reuseFailAlloc_1366_, 5, v_ref_1073_);
lean_ctor_set(v_reuseFailAlloc_1366_, 6, v_currNamespace_1074_);
lean_ctor_set(v_reuseFailAlloc_1366_, 7, v_openDecls_1075_);
lean_ctor_set(v_reuseFailAlloc_1366_, 8, v_initHeartbeats_1076_);
lean_ctor_set(v_reuseFailAlloc_1366_, 9, v_maxHeartbeats_1077_);
lean_ctor_set(v_reuseFailAlloc_1366_, 10, v_quotContext_1078_);
lean_ctor_set(v_reuseFailAlloc_1366_, 11, v_currMacroScope_1079_);
lean_ctor_set(v_reuseFailAlloc_1366_, 12, v_cancelTk_x3f_1081_);
lean_ctor_set(v_reuseFailAlloc_1366_, 13, v_inheritedTraceOptions_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*14, v_diag_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*14 + 1, v_suppressElabErrors_1082_);
v___x_1354_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_nat_dec_le(v_maxSteps_1350_, v_numSteps_1349_);
lean_dec(v_maxSteps_1350_);
if (v___x_1355_ == 0)
{
v___y_1229_ = v___x_1351_;
v___y_1230_ = v_numSteps_1349_;
v___y_1231_ = v_a_795_;
v___y_1232_ = v_a_796_;
v___y_1233_ = v_a_797_;
v___y_1234_ = v_a_798_;
v___y_1235_ = v_a_799_;
v___y_1236_ = v_a_800_;
v___y_1237_ = v_a_801_;
v___y_1238_ = v___x_1354_;
v___y_1239_ = v_a_803_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_numSteps_1349_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_e_u2081_794_);
v___x_1356_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8);
v___x_1357_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_1356_, v_a_800_, v_a_801_, v___x_1354_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v___x_1354_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v___x_1346_);
lean_del_object(v___x_1085_);
lean_dec_ref(v_inheritedTraceOptions_1083_);
lean_dec(v_cancelTk_x3f_1081_);
lean_dec(v_currMacroScope_1079_);
lean_dec(v_quotContext_1078_);
lean_dec(v_maxHeartbeats_1077_);
lean_dec(v_initHeartbeats_1076_);
lean_dec(v_openDecls_1075_);
lean_dec(v_currNamespace_1074_);
lean_dec(v_ref_1073_);
lean_dec(v_maxRecDepth_1072_);
lean_dec(v_currRecDepth_1071_);
lean_dec_ref(v_options_1070_);
lean_dec_ref(v_fileMap_1069_);
lean_dec_ref(v_fileName_1068_);
lean_dec(v_a_803_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_e_u2081_794_);
v_a_1367_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1347_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1347_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* v_e_u2081_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = lean_sym_simp(v_e_u2081_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* v_00_u03b2_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_1393_, v_x_1394_, v_x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* v_00_u03b2_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_1398_, v_x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* v_00_u03b2_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_1401_, v_x_1402_, v_x_1403_);
lean_dec_ref(v_x_1403_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* v_cls_1405_, lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_1405_, v_msg_1406_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* v_cls_1418_, lean_object* v_msg_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_1418_, v_msg_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* v_00_u03b2_1431_, lean_object* v_x_1432_, size_t v_x_1433_, size_t v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_1432_, v_x_1433_, v_x_1434_, v_x_1435_, v_x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
size_t v_x_120191__boxed_1444_; size_t v_x_120192__boxed_1445_; lean_object* v_res_1446_; 
v_x_120191__boxed_1444_ = lean_unbox_usize(v_x_1440_);
lean_dec(v_x_1440_);
v_x_120192__boxed_1445_ = lean_unbox_usize(v_x_1441_);
lean_dec(v_x_1441_);
v_res_1446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_1438_, v_x_1439_, v_x_120191__boxed_1444_, v_x_120192__boxed_1445_, v_x_1442_, v_x_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* v_00_u03b2_1447_, lean_object* v_x_1448_, size_t v_x_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_1448_, v_x_1449_, v_x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_){
_start:
{
size_t v_x_120208__boxed_1456_; lean_object* v_res_1457_; 
v_x_120208__boxed_1456_ = lean_unbox_usize(v_x_1454_);
lean_dec(v_x_1454_);
v_res_1457_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_1452_, v_x_1453_, v_x_120208__boxed_1456_, v_x_1455_);
lean_dec_ref(v_x_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1458_, lean_object* v_n_1459_, lean_object* v_k_1460_, lean_object* v_v_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v_n_1459_, v_k_1460_, v_v_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1463_, size_t v_depth_1464_, lean_object* v_keys_1465_, lean_object* v_vals_1466_, lean_object* v_heq_1467_, lean_object* v_i_1468_, lean_object* v_entries_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_1464_, v_keys_1465_, v_vals_1466_, v_i_1468_, v_entries_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1471_, lean_object* v_depth_1472_, lean_object* v_keys_1473_, lean_object* v_vals_1474_, lean_object* v_heq_1475_, lean_object* v_i_1476_, lean_object* v_entries_1477_){
_start:
{
size_t v_depth_boxed_1478_; lean_object* v_res_1479_; 
v_depth_boxed_1478_ = lean_unbox_usize(v_depth_1472_);
lean_dec(v_depth_1472_);
v_res_1479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(v_00_u03b2_1471_, v_depth_boxed_1478_, v_keys_1473_, v_vals_1474_, v_heq_1475_, v_i_1476_, v_entries_1477_);
lean_dec_ref(v_vals_1474_);
lean_dec_ref(v_keys_1473_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1480_, lean_object* v_keys_1481_, lean_object* v_vals_1482_, lean_object* v_heq_1483_, lean_object* v_i_1484_, lean_object* v_k_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1481_, v_vals_1482_, v_i_1484_, v_k_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1487_, lean_object* v_keys_1488_, lean_object* v_vals_1489_, lean_object* v_heq_1490_, lean_object* v_i_1491_, lean_object* v_k_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(v_00_u03b2_1487_, v_keys_1488_, v_vals_1489_, v_heq_1490_, v_i_1491_, v_k_1492_);
lean_dec_ref(v_k_1492_);
lean_dec_ref(v_vals_1489_);
lean_dec_ref(v_keys_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1495_, v_x_1496_, v_x_1497_, v_x_1498_);
return v___x_1499_;
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
