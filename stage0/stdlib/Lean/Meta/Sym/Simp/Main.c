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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "OfScientific"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofScientific"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 219, 72, 84, 44, 38, 226, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 32, 126, 239, 82, 155, 222, 105)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "unexpected kernel projection term during simplification"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "\npre-process and fold them as projection applications"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_91_;
v_res_91_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_();
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2____boxed(lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_();
return v_res_93_;
}
}
uint8_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(lean_object* v_e_104_){
_start:
{
uint8_t v___y_106_; uint8_t v___y_115_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__5));
v___x_128_ = lean_unsigned_to_nat(3u);
v___x_129_ = l_Lean_Expr_isAppOfArity(v_e_104_, v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
v___y_115_ = v___x_129_;
goto v___jp_114_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = l_Lean_Expr_getAppNumArgs(v_e_104_);
v___x_132_ = lean_nat_sub(v___x_131_, v___x_130_);
lean_dec(v___x_131_);
v___x_133_ = lean_nat_sub(v___x_132_, v___x_130_);
lean_dec(v___x_132_);
v___x_134_ = l_Lean_Expr_getRevArg_x21(v_e_104_, v___x_133_);
v___x_135_ = l_Lean_Expr_isRawNatLit(v___x_134_);
lean_dec_ref(v___x_134_);
v___y_115_ = v___x_135_;
goto v___jp_114_;
}
v___jp_105_:
{
if (v___y_106_ == 0)
{
return v___y_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_107_ = lean_unsigned_to_nat(4u);
v___x_108_ = l_Lean_Expr_getAppNumArgs(v_e_104_);
v___x_109_ = lean_nat_sub(v___x_108_, v___x_107_);
lean_dec(v___x_108_);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_sub(v___x_109_, v___x_110_);
lean_dec(v___x_109_);
v___x_112_ = l_Lean_Expr_getRevArg_x21(v_e_104_, v___x_111_);
v___x_113_ = l_Lean_Expr_isRawNatLit(v___x_112_);
lean_dec_ref(v___x_112_);
return v___x_113_;
}
}
v___jp_114_:
{
if (v___y_115_ == 0)
{
uint8_t v___x_116_; 
v___x_116_ = l_Lean_Expr_isCharLit(v_e_104_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__2));
v___x_118_ = lean_unsigned_to_nat(5u);
v___x_119_ = l_Lean_Expr_isAppOfArity(v_e_104_, v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
v___y_106_ = v___x_119_;
goto v___jp_105_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = l_Lean_Expr_getAppNumArgs(v_e_104_);
v___x_122_ = lean_nat_sub(v___x_121_, v___x_120_);
lean_dec(v___x_121_);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_sub(v___x_122_, v___x_123_);
lean_dec(v___x_122_);
v___x_125_ = l_Lean_Expr_getRevArg_x21(v_e_104_, v___x_124_);
v___x_126_ = l_Lean_Expr_isRawNatLit(v___x_125_);
lean_dec_ref(v___x_125_);
v___y_106_ = v___x_126_;
goto v___jp_105_;
}
}
else
{
return v___x_116_;
}
}
else
{
return v___y_115_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_104_ = stack[0].m_obj;
uint8_t v_res_136_;
v_res_136_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(v_e_104_);
stack->m_num = v_res_136_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___boxed(lean_object* v_e_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(v_e_137_);
lean_dec_ref(v_e_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object* v_d_140_, lean_object* v_e_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___y_150_; lean_object* v___x_153_; uint8_t v_debug_154_; 
v___x_153_ = lean_st_ref_get(v___y_143_);
v_debug_154_ = lean_ctor_get_uint8(v___x_153_, sizeof(void*)*12);
lean_dec(v___x_153_);
if (v_debug_154_ == 0)
{
v___y_150_ = v___y_143_;
goto v___jp_149_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_dec_ref_known(v___x_155_, 1);
v___y_150_ = v___y_143_;
goto v___jp_149_;
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec_ref(v_e_141_);
lean_dec(v_d_140_);
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = l_Lean_Expr_mdata___override(v_d_140_, v_e_141_);
v___x_152_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_151_, v___y_150_);
return v___x_152_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_140_ = stack[0].m_obj;
lean_object* v_e_141_ = stack[1].m_obj;
lean_object* v___y_142_ = stack[2].m_obj;
lean_object* v___y_143_ = stack[3].m_obj;
lean_object* v___y_144_ = stack[4].m_obj;
lean_object* v___y_145_ = stack[5].m_obj;
lean_object* v___y_146_ = stack[6].m_obj;
lean_object* v___y_147_ = stack[7].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_140_, v_e_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object* v_d_165_, lean_object* v_e_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_165_, v_e_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_174_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object* v_d_175_, lean_object* v_e_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_175_, v_e_176_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_175_ = stack[0].m_obj;
lean_object* v_e_176_ = stack[1].m_obj;
lean_object* v___y_177_ = stack[2].m_obj;
lean_object* v___y_178_ = stack[3].m_obj;
lean_object* v___y_179_ = stack[4].m_obj;
lean_object* v___y_180_ = stack[5].m_obj;
lean_object* v___y_181_ = stack[6].m_obj;
lean_object* v___y_182_ = stack[7].m_obj;
lean_object* v___y_183_ = stack[8].m_obj;
lean_object* v___y_184_ = stack[9].m_obj;
lean_object* v___y_185_ = stack[10].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(v_d_175_, v_e_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object* v_d_189_, lean_object* v_e_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(v_d_189_, v_e_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
return v_res_201_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object* v_msgData_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_env_209_; uint8_t v___x_210_; lean_object* v_env_211_; lean_object* v___x_212_; lean_object* v_toCold_213_; lean_object* v_mctx_214_; lean_object* v_lctx_215_; lean_object* v_options_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_208_ = lean_st_ref_get(v___y_206_);
v_env_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc_ref(v_env_209_);
lean_dec(v___x_208_);
v___x_210_ = 0;
v_env_211_ = l_Lean_Environment_setRecordingDeps(v_env_209_, v___x_210_);
v___x_212_ = lean_st_ref_get(v___y_204_);
v_toCold_213_ = lean_ctor_get(v___y_205_, 0);
v_mctx_214_ = lean_ctor_get(v___x_212_, 0);
lean_inc_ref(v_mctx_214_);
lean_dec(v___x_212_);
v_lctx_215_ = lean_ctor_get(v___y_203_, 2);
v_options_216_ = lean_ctor_get(v_toCold_213_, 2);
lean_inc_ref(v_options_216_);
lean_inc_ref(v_lctx_215_);
v___x_217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_217_, 0, v_env_211_);
lean_ctor_set(v___x_217_, 1, v_mctx_214_);
lean_ctor_set(v___x_217_, 2, v_lctx_215_);
lean_ctor_set(v___x_217_, 3, v_options_216_);
v___x_218_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_msgData_202_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_202_ = stack[0].m_obj;
lean_object* v___y_203_ = stack[1].m_obj;
lean_object* v___y_204_ = stack[2].m_obj;
lean_object* v___y_205_ = stack[3].m_obj;
lean_object* v___y_206_ = stack[4].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msgData_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object* v_msgData_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msgData_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_227_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_ref_234_; lean_object* v___x_235_; lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_ref_234_ = lean_ctor_get(v___y_231_, 2);
v___x_235_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
v_a_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
lean_inc(v_ref_234_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_ref_234_);
lean_ctor_set(v___x_240_, 1, v_a_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 1);
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_228_ = stack[0].m_obj;
lean_object* v___y_229_ = stack[1].m_obj;
lean_object* v___y_230_ = stack[2].m_obj;
lean_object* v___y_231_ = stack[3].m_obj;
lean_object* v___y_232_ = stack[4].m_obj;
lean_object* v_res_245_;
v_res_245_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object* v_msg_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3));
v___x_260_ = l_Lean_stringToMessageData(v___x_259_);
return v___x_260_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object* v_e_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
switch(lean_obj_tag(v_e_261_))
{
case 5:
{
uint8_t v___x_272_; 
v___x_272_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(v_e_261_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref_known(v_e_261_, 2);
v___x_274_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
case 6:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v___x_276_;
}
case 7:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v___x_277_;
}
case 8:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v___x_278_;
}
case 9:
{
lean_object* v_a_279_; 
v_a_279_ = lean_ctor_get(v_e_261_, 0);
lean_inc_ref(v_a_279_);
lean_dec_ref_known(v_e_261_, 1);
if (lean_obj_tag(v_a_279_) == 0)
{
lean_object* v_val_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_val_280_ = lean_ctor_get(v_a_279_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v_a_279_, 1);
v___x_281_ = l_Lean_mkNatLit(v_val_280_);
v___x_282_ = l_Lean_Meta_Sym_shareCommonInc(v___x_281_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_n(v_a_283_, 2);
lean_dec_ref_known(v___x_282_, 1);
v___x_284_ = l_Lean_Meta_Sym_mkEqRefl(v_a_283_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_294_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_294_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_294_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_294_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_289_ = 0;
v___x_290_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_290_, 0, v_a_283_);
lean_ctor_set(v___x_290_, 1, v_a_285_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*2, v___x_289_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*2 + 1, v___x_289_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_290_);
v___x_292_ = v___x_287_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec(v_a_283_);
v_a_295_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_284_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_284_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_282_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_282_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec_ref(v_a_279_);
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
case 10:
{
lean_object* v_data_313_; lean_object* v_expr_314_; lean_object* v___x_315_; 
v_data_313_ = lean_ctor_get(v_e_261_, 0);
lean_inc(v_data_313_);
v_expr_314_ = lean_ctor_get(v_e_261_, 1);
lean_inc_ref(v_expr_314_);
lean_dec_ref_known(v_e_261_, 2);
lean_inc(v_a_270_);
lean_inc_ref(v_a_269_);
lean_inc(v_a_268_);
lean_inc_ref(v_a_267_);
lean_inc(v_a_266_);
lean_inc_ref(v_a_265_);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
lean_inc(v_a_262_);
v___x_315_ = lean_sym_simp(v_expr_314_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_353_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_353_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_353_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_353_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
if (lean_obj_tag(v_a_316_) == 0)
{
uint8_t v_contextDependent_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
lean_dec(v_data_313_);
v_contextDependent_320_ = lean_ctor_get_uint8(v_a_316_, 1);
lean_dec_ref_known(v_a_316_, 0);
v___x_321_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_320_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
else
{
lean_object* v_e_x27_325_; lean_object* v_proof_326_; uint8_t v_contextDependent_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_352_; 
lean_del_object(v___x_318_);
v_e_x27_325_ = lean_ctor_get(v_a_316_, 0);
v_proof_326_ = lean_ctor_get(v_a_316_, 1);
v_contextDependent_327_ = lean_ctor_get_uint8(v_a_316_, sizeof(void*)*2 + 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_a_316_);
if (v_isSharedCheck_352_ == 0)
{
v___x_329_ = v_a_316_;
v_isShared_330_ = v_isSharedCheck_352_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_proof_326_);
lean_inc(v_e_x27_325_);
lean_dec(v_a_316_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_352_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_data_313_, v_e_x27_325_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_343_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_343_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
uint8_t v___x_336_; lean_object* v___x_338_; 
v___x_336_ = 0;
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v_a_332_);
v___x_338_ = v___x_329_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_332_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_proof_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_342_, sizeof(void*)*2 + 1, v_contextDependent_327_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*2, v___x_336_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_338_);
v___x_340_ = v___x_334_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_del_object(v___x_329_);
lean_dec_ref(v_proof_326_);
v_a_344_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_331_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_331_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
}
else
{
lean_dec(v_data_313_);
return v___x_315_;
}
}
case 11:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_354_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2);
v___x_355_ = l_Lean_indentExpr(v_e_261_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_358_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v___x_359_;
}
default: 
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_e_261_);
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_261_ = stack[0].m_obj;
lean_object* v_a_262_ = stack[1].m_obj;
lean_object* v_a_263_ = stack[2].m_obj;
lean_object* v_a_264_ = stack[3].m_obj;
lean_object* v_a_265_ = stack[4].m_obj;
lean_object* v_a_266_ = stack[5].m_obj;
lean_object* v_a_267_ = stack[6].m_obj;
lean_object* v_a_268_ = stack[7].m_obj;
lean_object* v_a_269_ = stack[8].m_obj;
lean_object* v_a_270_ = stack[9].m_obj;
lean_object* v_res_362_;
v_res_362_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object* v_e_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
return v_res_374_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object* v_00_u03b1_375_, lean_object* v_msg_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_376_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_376_ = stack[1].m_obj;
lean_object* v___y_377_ = stack[2].m_obj;
lean_object* v___y_378_ = stack[3].m_obj;
lean_object* v___y_379_ = stack[4].m_obj;
lean_object* v___y_380_ = stack[5].m_obj;
lean_object* v___y_381_ = stack[6].m_obj;
lean_object* v___y_382_ = stack[7].m_obj;
lean_object* v___y_383_ = stack[8].m_obj;
lean_object* v___y_384_ = stack[9].m_obj;
lean_object* v___y_385_ = stack[10].m_obj;
lean_object* v_res_388_;
v_res_388_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_box(0), v_msg_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object* v_00_u03b1_389_, lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(v_00_u03b1_389_, v_msg_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
return v_res_401_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = l_Lean_maxRecDepthErrorMessage;
v___x_408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3);
v___x_410_ = l_Lean_MessageData_ofFormat(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4);
v___x_412_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2));
v___x_413_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
return v___x_413_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(lean_object* v_ref_414_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_ref_414_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_414_ = stack[0].m_obj;
lean_object* v_res_419_;
v_res_419_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_414_);
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(lean_object* v_ref_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_420_);
return v_res_422_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_object* v_00_u03b1_423_, lean_object* v_ref_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_424_);
return v___x_435_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_424_ = stack[1].m_obj;
lean_object* v___y_425_ = stack[2].m_obj;
lean_object* v___y_426_ = stack[3].m_obj;
lean_object* v___y_427_ = stack[4].m_obj;
lean_object* v___y_428_ = stack[5].m_obj;
lean_object* v___y_429_ = stack[6].m_obj;
lean_object* v___y_430_ = stack[7].m_obj;
lean_object* v___y_431_ = stack[8].m_obj;
lean_object* v___y_432_ = stack[9].m_obj;
lean_object* v___y_433_ = stack[10].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_box(0), v_ref_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(lean_object* v_00_u03b1_437_, lean_object* v_ref_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(v_00_u03b1_437_, v_ref_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
return v_res_449_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_post_462_; lean_object* v___x_463_; 
v_post_462_ = lean_ctor_get(v___y_452_, 1);
lean_inc_ref(v_post_462_);
lean_inc(v___y_460_);
lean_inc_ref(v___y_459_);
lean_inc(v___y_458_);
lean_inc_ref(v___y_457_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
lean_inc(v___y_452_);
v___x_463_ = lean_apply_11(v_post_462_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, lean_box(0));
return v___x_463_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_450_ = stack[0].m_obj;
lean_object* v___y_451_ = stack[1].m_obj;
lean_object* v___y_452_ = stack[2].m_obj;
lean_object* v___y_453_ = stack[3].m_obj;
lean_object* v___y_454_ = stack[4].m_obj;
lean_object* v___y_455_ = stack[5].m_obj;
lean_object* v___y_456_ = stack[6].m_obj;
lean_object* v___y_457_ = stack[7].m_obj;
lean_object* v___y_458_ = stack[8].m_obj;
lean_object* v___y_459_ = stack[9].m_obj;
lean_object* v___y_460_ = stack[10].m_obj;
lean_object* v_res_464_;
v_res_464_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object* v_x_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v_x_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_ks_482_; lean_object* v_vs_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_509_; 
v_ks_482_ = lean_ctor_get(v_x_478_, 0);
v_vs_483_ = lean_ctor_get(v_x_478_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_478_);
if (v_isSharedCheck_509_ == 0)
{
v___x_485_ = v_x_478_;
v_isShared_486_ = v_isSharedCheck_509_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_vs_483_);
lean_inc(v_ks_482_);
lean_dec(v_x_478_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_509_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_array_get_size(v_ks_482_);
v___x_488_ = lean_nat_dec_lt(v_x_479_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
lean_dec(v_x_479_);
v___x_489_ = lean_array_push(v_ks_482_, v_x_480_);
v___x_490_ = lean_array_push(v_vs_483_, v_x_481_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_490_);
lean_ctor_set(v___x_485_, 0, v___x_489_);
v___x_492_ = v___x_485_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v_k_x27_494_; size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v_k_x27_494_ = lean_array_fget_borrowed(v_ks_482_, v_x_479_);
v___x_495_ = lean_ptr_addr(v_x_480_);
v___x_496_ = lean_ptr_addr(v_k_x27_494_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_499_; 
if (v_isShared_486_ == 0)
{
v___x_499_ = v___x_485_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_ks_482_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_vs_483_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v_x_479_, v___x_500_);
lean_dec(v_x_479_);
v_x_478_ = v___x_499_;
v_x_479_ = v___x_501_;
goto _start;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = lean_array_fset(v_ks_482_, v_x_479_, v_x_480_);
v___x_505_ = lean_array_fset(v_vs_483_, v_x_479_, v_x_481_);
lean_dec(v_x_479_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_505_);
lean_ctor_set(v___x_485_, 0, v___x_504_);
v___x_507_ = v___x_485_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_510_, lean_object* v_k_511_, lean_object* v_v_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_n_510_, v___x_513_, v_k_511_, v_v_512_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_515_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* v_x_516_, size_t v_x_517_, size_t v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v_es_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v_j_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_es_521_ = lean_ctor_get(v_x_516_, 0);
v___x_522_ = ((size_t)31ULL);
v___x_523_ = lean_usize_land(v_x_517_, v___x_522_);
v_j_524_ = lean_usize_to_nat(v___x_523_);
v___x_525_ = lean_array_get_size(v_es_521_);
v___x_526_ = lean_nat_dec_lt(v_j_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec(v_j_524_);
lean_dec(v_x_520_);
lean_dec_ref(v_x_519_);
return v_x_516_;
}
else
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_567_; 
lean_inc_ref(v_es_521_);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_x_516_, 0);
lean_dec(v_unused_568_);
v___x_528_ = v_x_516_;
v_isShared_529_ = v_isSharedCheck_567_;
goto v_resetjp_527_;
}
else
{
lean_dec(v_x_516_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_567_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_v_530_; lean_object* v___x_531_; lean_object* v_xs_x27_532_; lean_object* v___y_534_; 
v_v_530_ = lean_array_fget(v_es_521_, v_j_524_);
v___x_531_ = lean_box(0);
v_xs_x27_532_ = lean_array_fset(v_es_521_, v_j_524_, v___x_531_);
switch(lean_obj_tag(v_v_530_))
{
case 0:
{
lean_object* v_key_539_; lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_552_; 
v_key_539_ = lean_ctor_get(v_v_530_, 0);
v_val_540_ = lean_ctor_get(v_v_530_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_v_530_);
if (v_isSharedCheck_552_ == 0)
{
v___x_542_ = v_v_530_;
v_isShared_543_ = v_isSharedCheck_552_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_inc(v_key_539_);
lean_dec(v_v_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_552_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
size_t v___x_544_; size_t v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_ptr_addr(v_x_519_);
v___x_545_ = lean_ptr_addr(v_key_539_);
v___x_546_ = lean_usize_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_del_object(v___x_542_);
v___x_547_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_539_, v_val_540_, v_x_519_, v_x_520_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___y_534_ = v___x_548_;
goto v___jp_533_;
}
else
{
lean_object* v___x_550_; 
lean_dec(v_val_540_);
lean_dec(v_key_539_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_x_520_);
lean_ctor_set(v___x_542_, 0, v_x_519_);
v___x_550_ = v___x_542_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_x_519_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_x_520_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v___y_534_ = v___x_550_;
goto v___jp_533_;
}
}
}
}
case 1:
{
lean_object* v_node_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_565_; 
v_node_553_ = lean_ctor_get(v_v_530_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_v_530_);
if (v_isSharedCheck_565_ == 0)
{
v___x_555_ = v_v_530_;
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_node_553_);
lean_dec(v_v_530_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_557_ = ((size_t)5ULL);
v___x_558_ = lean_usize_shift_right(v_x_517_, v___x_557_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_x_518_, v___x_559_);
v___x_561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_553_, v___x_558_, v___x_560_, v_x_519_, v_x_520_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_561_);
v___x_563_ = v___x_555_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
v___y_534_ = v___x_563_;
goto v___jp_533_;
}
}
}
default: 
{
lean_object* v___x_566_; 
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_x_519_);
lean_ctor_set(v___x_566_, 1, v_x_520_);
v___y_534_ = v___x_566_;
goto v___jp_533_;
}
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_array_fset(v_xs_x27_532_, v_j_524_, v___y_534_);
lean_dec(v_j_524_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_535_);
v___x_537_ = v___x_528_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
else
{
lean_object* v_ks_569_; lean_object* v_vs_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_588_; 
v_ks_569_ = lean_ctor_get(v_x_516_, 0);
v_vs_570_ = lean_ctor_get(v_x_516_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_588_ == 0)
{
v___x_572_ = v_x_516_;
v_isShared_573_ = v_isSharedCheck_588_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_vs_570_);
lean_inc(v_ks_569_);
lean_dec(v_x_516_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_588_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_ks_569_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_vs_570_);
v___x_575_ = v_reuseFailAlloc_587_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v_newNode_576_; size_t v___x_577_; uint8_t v___x_578_; 
v_newNode_576_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v___x_575_, v_x_519_, v_x_520_);
v___x_577_ = ((size_t)7ULL);
v___x_578_ = lean_usize_dec_le(v___x_577_, v_x_518_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_576_);
v___x_580_ = lean_unsigned_to_nat(4u);
v___x_581_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
lean_dec(v___x_579_);
if (v___x_581_ == 0)
{
lean_object* v_ks_582_; lean_object* v_vs_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_ks_582_ = lean_ctor_get(v_newNode_576_, 0);
lean_inc_ref(v_ks_582_);
v_vs_583_ = lean_ctor_get(v_newNode_576_, 1);
lean_inc_ref(v_vs_583_);
lean_dec_ref(v_newNode_576_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
v___x_586_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_x_518_, v_ks_582_, v_vs_583_, v___x_584_, v___x_585_);
lean_dec_ref(v_vs_583_);
lean_dec_ref(v_ks_582_);
return v___x_586_;
}
else
{
return v_newNode_576_;
}
}
else
{
return v_newNode_576_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_516_ = stack[0].m_obj;
size_t v_x_517_ = stack[1].m_num;
size_t v_x_518_ = stack[2].m_num;
lean_object* v_x_519_ = stack[3].m_obj;
lean_object* v_x_520_ = stack[4].m_obj;
lean_object* v_res_589_;
v_res_589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_516_, v_x_517_, v_x_518_, v_x_519_, v_x_520_);
stack->m_obj
 = v_res_589_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_590_, lean_object* v_keys_591_, lean_object* v_vals_592_, lean_object* v_i_593_, lean_object* v_entries_594_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_array_get_size(v_keys_591_);
v___x_596_ = lean_nat_dec_lt(v_i_593_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v_i_593_);
return v_entries_594_;
}
else
{
lean_object* v_k_597_; lean_object* v_v_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; uint64_t v___x_602_; size_t v_h_603_; size_t v___x_604_; lean_object* v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v_h_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_k_597_ = lean_array_fget_borrowed(v_keys_591_, v_i_593_);
v_v_598_ = lean_array_fget_borrowed(v_vals_592_, v_i_593_);
v___x_599_ = lean_ptr_addr(v_k_597_);
v___x_600_ = ((size_t)3ULL);
v___x_601_ = lean_usize_shift_right(v___x_599_, v___x_600_);
v___x_602_ = lean_usize_to_uint64(v___x_601_);
v_h_603_ = lean_uint64_to_usize(v___x_602_);
v___x_604_ = ((size_t)5ULL);
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_sub(v_depth_590_, v___x_606_);
v___x_608_ = lean_usize_mul(v___x_604_, v___x_607_);
v_h_609_ = lean_usize_shift_right(v_h_603_, v___x_608_);
v___x_610_ = lean_nat_add(v_i_593_, v___x_605_);
lean_dec(v_i_593_);
lean_inc(v_v_598_);
lean_inc(v_k_597_);
v___x_611_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_594_, v_h_609_, v_depth_590_, v_k_597_, v_v_598_);
v_i_593_ = v___x_610_;
v_entries_594_ = v___x_611_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_590_ = stack[0].m_num;
lean_object* v_keys_591_ = stack[1].m_obj;
lean_object* v_vals_592_ = stack[2].m_obj;
lean_object* v_i_593_ = stack[3].m_obj;
lean_object* v_entries_594_ = stack[4].m_obj;
lean_object* v_res_613_;
v_res_613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_590_, v_keys_591_, v_vals_592_, v_i_593_, v_entries_594_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_614_, lean_object* v_keys_615_, lean_object* v_vals_616_, lean_object* v_i_617_, lean_object* v_entries_618_){
_start:
{
size_t v_depth_boxed_619_; lean_object* v_res_620_; 
v_depth_boxed_619_ = lean_unbox_usize(v_depth_614_);
lean_dec(v_depth_614_);
v_res_620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_619_, v_keys_615_, v_vals_616_, v_i_617_, v_entries_618_);
lean_dec_ref(v_vals_616_);
lean_dec_ref(v_keys_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
size_t v_x_110069__boxed_626_; size_t v_x_110070__boxed_627_; lean_object* v_res_628_; 
v_x_110069__boxed_626_ = lean_unbox_usize(v_x_622_);
lean_dec(v_x_622_);
v_x_110070__boxed_627_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_res_628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_621_, v_x_110069__boxed_626_, v_x_110070__boxed_627_, v_x_624_, v_x_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
size_t v___x_632_; size_t v___x_633_; size_t v___x_634_; uint64_t v___x_635_; size_t v___x_636_; size_t v___x_637_; lean_object* v___x_638_; 
v___x_632_ = lean_ptr_addr(v_x_630_);
v___x_633_ = ((size_t)3ULL);
v___x_634_ = lean_usize_shift_right(v___x_632_, v___x_633_);
v___x_635_ = lean_usize_to_uint64(v___x_634_);
v___x_636_ = lean_uint64_to_usize(v___x_635_);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_629_, v___x_636_, v___x_637_, v_x_630_, v_x_631_);
return v___x_638_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_639_; double v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_float_of_nat(v___x_639_);
return v___x_640_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* v_cls_644_, lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_ref_651_; lean_object* v___x_652_; lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_698_; 
v_ref_651_ = lean_ctor_get(v___y_648_, 2);
v___x_652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_698_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_698_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_698_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v_traceState_658_; lean_object* v_env_659_; lean_object* v_nextMacroScope_660_; lean_object* v_ngen_661_; lean_object* v_auxDeclNGen_662_; lean_object* v_cache_663_; lean_object* v_recordedDeps_664_; lean_object* v_messages_665_; lean_object* v_infoState_666_; lean_object* v_snapshotTasks_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_697_; 
v___x_657_ = lean_st_ref_take(v___y_649_);
v_traceState_658_ = lean_ctor_get(v___x_657_, 4);
v_env_659_ = lean_ctor_get(v___x_657_, 0);
v_nextMacroScope_660_ = lean_ctor_get(v___x_657_, 1);
v_ngen_661_ = lean_ctor_get(v___x_657_, 2);
v_auxDeclNGen_662_ = lean_ctor_get(v___x_657_, 3);
v_cache_663_ = lean_ctor_get(v___x_657_, 5);
v_recordedDeps_664_ = lean_ctor_get(v___x_657_, 6);
v_messages_665_ = lean_ctor_get(v___x_657_, 7);
v_infoState_666_ = lean_ctor_get(v___x_657_, 8);
v_snapshotTasks_667_ = lean_ctor_get(v___x_657_, 9);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_697_ == 0)
{
v___x_669_ = v___x_657_;
v_isShared_670_ = v_isSharedCheck_697_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snapshotTasks_667_);
lean_inc(v_infoState_666_);
lean_inc(v_messages_665_);
lean_inc(v_recordedDeps_664_);
lean_inc(v_cache_663_);
lean_inc(v_traceState_658_);
lean_inc(v_auxDeclNGen_662_);
lean_inc(v_ngen_661_);
lean_inc(v_nextMacroScope_660_);
lean_inc(v_env_659_);
lean_dec(v___x_657_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_697_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
uint64_t v_tid_671_; lean_object* v_traces_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_696_; 
v_tid_671_ = lean_ctor_get_uint64(v_traceState_658_, sizeof(void*)*1);
v_traces_672_ = lean_ctor_get(v_traceState_658_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v_traceState_658_);
if (v_isSharedCheck_696_ == 0)
{
v___x_674_ = v_traceState_658_;
v_isShared_675_ = v_isSharedCheck_696_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_traces_672_);
lean_dec(v_traceState_658_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_696_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; double v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_676_ = lean_box(0);
v___x_677_ = lean_box(0);
v___x_678_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0);
v___x_679_ = 0;
v___x_680_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1));
v___x_681_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_681_, 0, v_cls_644_);
lean_ctor_set(v___x_681_, 1, v___x_677_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
lean_ctor_set_float(v___x_681_, sizeof(void*)*3, v___x_678_);
lean_ctor_set_float(v___x_681_, sizeof(void*)*3 + 8, v___x_678_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*3 + 16, v___x_679_);
v___x_682_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2));
v___x_683_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v_a_653_);
lean_ctor_set(v___x_683_, 2, v___x_682_);
lean_inc(v_ref_651_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_ref_651_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_PersistentArray_push___redArg(v_traces_672_, v___x_684_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_685_);
v___x_687_ = v___x_674_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_685_);
lean_ctor_set_uint64(v_reuseFailAlloc_695_, sizeof(void*)*1, v_tid_671_);
v___x_687_ = v_reuseFailAlloc_695_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v___x_687_);
v___x_689_ = v___x_669_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_env_659_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_nextMacroScope_660_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_ngen_661_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_auxDeclNGen_662_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_694_, 5, v_cache_663_);
lean_ctor_set(v_reuseFailAlloc_694_, 6, v_recordedDeps_664_);
lean_ctor_set(v_reuseFailAlloc_694_, 7, v_messages_665_);
lean_ctor_set(v_reuseFailAlloc_694_, 8, v_infoState_666_);
lean_ctor_set(v_reuseFailAlloc_694_, 9, v_snapshotTasks_667_);
v___x_689_ = v_reuseFailAlloc_694_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_st_ref_put(v___y_649_, v___x_689_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_676_);
v___x_692_ = v___x_655_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_676_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_644_ = stack[0].m_obj;
lean_object* v_msg_645_ = stack[1].m_obj;
lean_object* v___y_646_ = stack[2].m_obj;
lean_object* v___y_647_ = stack[3].m_obj;
lean_object* v___y_648_ = stack[4].m_obj;
lean_object* v___y_649_ = stack[5].m_obj;
lean_object* v_res_699_;
v_res_699_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_644_, v_msg_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* v_cls_700_, lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_700_, v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_708_, lean_object* v_vals_709_, lean_object* v_i_710_, lean_object* v_k_711_){
_start:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_get_size(v_keys_708_);
v___x_713_ = lean_nat_dec_lt(v_i_710_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec(v_i_710_);
v___x_714_ = lean_box(0);
return v___x_714_;
}
else
{
lean_object* v_k_x27_715_; size_t v___x_716_; size_t v___x_717_; uint8_t v___x_718_; 
v_k_x27_715_ = lean_array_fget_borrowed(v_keys_708_, v_i_710_);
v___x_716_ = lean_ptr_addr(v_k_711_);
v___x_717_ = lean_ptr_addr(v_k_x27_715_);
v___x_718_ = lean_usize_dec_eq(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_add(v_i_710_, v___x_719_);
lean_dec(v_i_710_);
v_i_710_ = v___x_720_;
goto _start;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_array_fget_borrowed(v_vals_709_, v_i_710_);
lean_dec(v_i_710_);
lean_inc(v___x_722_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_724_, lean_object* v_vals_725_, lean_object* v_i_726_, lean_object* v_k_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_724_, v_vals_725_, v_i_726_, v_k_727_);
lean_dec_ref(v_k_727_);
lean_dec_ref(v_vals_725_);
lean_dec_ref(v_keys_724_);
return v_res_728_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* v_x_729_, size_t v_x_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_729_) == 0)
{
lean_object* v_es_732_; lean_object* v___x_733_; size_t v___x_734_; size_t v___x_735_; lean_object* v_j_736_; lean_object* v___x_737_; 
v_es_732_ = lean_ctor_get(v_x_729_, 0);
v___x_733_ = lean_box(2);
v___x_734_ = ((size_t)31ULL);
v___x_735_ = lean_usize_land(v_x_730_, v___x_734_);
v_j_736_ = lean_usize_to_nat(v___x_735_);
v___x_737_ = lean_array_get_borrowed(v___x_733_, v_es_732_, v_j_736_);
lean_dec(v_j_736_);
switch(lean_obj_tag(v___x_737_))
{
case 0:
{
lean_object* v_key_738_; lean_object* v_val_739_; size_t v___x_740_; size_t v___x_741_; uint8_t v___x_742_; 
v_key_738_ = lean_ctor_get(v___x_737_, 0);
v_val_739_ = lean_ctor_get(v___x_737_, 1);
v___x_740_ = lean_ptr_addr(v_x_731_);
v___x_741_ = lean_ptr_addr(v_key_738_);
v___x_742_ = lean_usize_dec_eq(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
v___x_743_ = lean_box(0);
return v___x_743_;
}
else
{
lean_object* v___x_744_; 
lean_inc(v_val_739_);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_val_739_);
return v___x_744_;
}
}
case 1:
{
lean_object* v_node_745_; size_t v___x_746_; size_t v___x_747_; 
v_node_745_ = lean_ctor_get(v___x_737_, 0);
v___x_746_ = ((size_t)5ULL);
v___x_747_ = lean_usize_shift_right(v_x_730_, v___x_746_);
v_x_729_ = v_node_745_;
v_x_730_ = v___x_747_;
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
v_ks_750_ = lean_ctor_get(v_x_729_, 0);
v_vs_751_ = lean_ctor_get(v_x_729_, 1);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_ks_750_, v_vs_751_, v___x_752_, v_x_731_);
return v___x_753_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_729_ = stack[0].m_obj;
size_t v_x_730_ = stack[1].m_num;
lean_object* v_x_731_ = stack[2].m_obj;
lean_object* v_res_754_;
v_res_754_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_729_, v_x_730_, v_x_731_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
size_t v_x_110531__boxed_758_; lean_object* v_res_759_; 
v_x_110531__boxed_758_ = lean_unbox_usize(v_x_756_);
lean_dec(v_x_756_);
v_res_759_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_755_, v_x_110531__boxed_758_, v_x_757_);
lean_dec_ref(v_x_757_);
lean_dec_ref(v_x_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; uint64_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_762_ = lean_ptr_addr(v_x_761_);
v___x_763_ = ((size_t)3ULL);
v___x_764_ = lean_usize_shift_right(v___x_762_, v___x_763_);
v___x_765_ = lean_usize_to_uint64(v___x_764_);
v___x_766_ = lean_uint64_to_usize(v___x_765_);
v___x_767_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_760_, v___x_766_, v_x_761_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_768_, v_x_769_);
lean_dec_ref(v_x_769_);
lean_dec_ref(v_x_768_);
return v_res_770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1));
v___x_776_ = l_Lean_Name_append(v___x_775_, v___x_774_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
lean_object* lean_sym_simp(lean_object* v_e_u2081_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___y_798_; lean_object* v___y_799_; uint8_t v___y_800_; lean_object* v___y_832_; uint8_t v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; uint8_t v___y_836_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___y_841_; lean_object* v___y_842_; uint8_t v___y_843_; lean_object* v_e_u2082_846_; lean_object* v_h_u2081_847_; uint8_t v_cd_u2081_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; uint8_t v___y_966_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; uint8_t v___y_979_; uint8_t v___y_980_; uint8_t v___y_981_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; uint8_t v___y_992_; uint8_t v___y_993_; lean_object* v_a_994_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; uint8_t v___y_1007_; uint8_t v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; uint8_t v___y_1022_; uint8_t v___y_1023_; uint8_t v___y_1024_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; uint8_t v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; uint8_t v___y_1039_; uint8_t v___y_1040_; uint8_t v___y_1041_; uint8_t v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; uint8_t v___y_1056_; uint8_t v___y_1057_; uint8_t v___y_1058_; lean_object* v_toCold_1060_; lean_object* v_currRecDepth_1061_; lean_object* v_ref_1062_; uint16_t v_optionFlags_1063_; uint8_t v_suppressElabErrors_1064_; uint8_t v_isRecordingDeps_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1364_; 
v_toCold_1060_ = lean_ctor_get(v_a_794_, 0);
v_currRecDepth_1061_ = lean_ctor_get(v_a_794_, 1);
v_ref_1062_ = lean_ctor_get(v_a_794_, 2);
v_optionFlags_1063_ = lean_ctor_get_uint16(v_a_794_, sizeof(void*)*3);
v_suppressElabErrors_1064_ = lean_ctor_get_uint8(v_a_794_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1065_ = lean_ctor_get_uint8(v_a_794_, sizeof(void*)*3 + 3);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_a_794_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1067_ = v_a_794_;
v_isShared_1068_ = v_isSharedCheck_1364_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_ref_1062_);
lean_inc(v_currRecDepth_1061_);
lean_inc(v_toCold_1060_);
lean_dec(v_a_794_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1364_;
goto v_resetjp_1066_;
}
v___jp_797_:
{
if (v___y_800_ == 0)
{
lean_object* v___x_801_; lean_object* v_numSteps_802_; lean_object* v_persistentCache_803_; lean_object* v_transientCache_804_; lean_object* v_funext_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
v___x_801_ = lean_st_ref_take(v___y_799_);
v_numSteps_802_ = lean_ctor_get(v___x_801_, 0);
v_persistentCache_803_ = lean_ctor_get(v___x_801_, 1);
v_transientCache_804_ = lean_ctor_get(v___x_801_, 2);
v_funext_805_ = lean_ctor_get(v___x_801_, 3);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_815_ == 0)
{
v___x_807_ = v___x_801_;
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_funext_805_);
lean_inc(v_transientCache_804_);
lean_inc(v_persistentCache_803_);
lean_inc(v_numSteps_802_);
lean_dec(v___x_801_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
lean_inc_ref(v___y_798_);
v___x_809_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_803_, v_e_u2081_786_, v___y_798_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_numSteps_802_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_transientCache_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_funext_805_);
v___x_811_ = v_reuseFailAlloc_814_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_st_ref_put(v___y_799_, v___x_811_);
lean_dec(v___y_799_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___y_798_);
return v___x_813_;
}
}
}
else
{
lean_object* v___x_816_; lean_object* v_numSteps_817_; lean_object* v_persistentCache_818_; lean_object* v_transientCache_819_; lean_object* v_funext_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_830_; 
v___x_816_ = lean_st_ref_take(v___y_799_);
v_numSteps_817_ = lean_ctor_get(v___x_816_, 0);
v_persistentCache_818_ = lean_ctor_get(v___x_816_, 1);
v_transientCache_819_ = lean_ctor_get(v___x_816_, 2);
v_funext_820_ = lean_ctor_get(v___x_816_, 3);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_830_ == 0)
{
v___x_822_ = v___x_816_;
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_funext_820_);
lean_inc(v_transientCache_819_);
lean_inc(v_persistentCache_818_);
lean_inc(v_numSteps_817_);
lean_dec(v___x_816_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc_ref(v___y_798_);
v___x_824_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_819_, v_e_u2081_786_, v___y_798_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 2, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_numSteps_817_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_persistentCache_818_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_funext_820_);
v___x_826_ = v_reuseFailAlloc_829_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_st_ref_put(v___y_799_, v___x_826_);
lean_dec(v___y_799_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___y_798_);
return v___x_828_;
}
}
}
}
v___jp_831_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_837_, 0, v___y_832_);
lean_ctor_set(v___x_837_, 1, v___y_835_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*2, v___y_833_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*2 + 1, v___y_836_);
v___y_798_ = v___x_837_;
v___y_799_ = v___y_834_;
v___y_800_ = v___y_836_;
goto v___jp_797_;
}
v___jp_838_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_844_, 0, v___y_840_);
lean_ctor_set(v___x_844_, 1, v___y_839_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*2, v___y_841_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*2 + 1, v___y_843_);
v___y_798_ = v___x_844_;
v___y_799_ = v___y_842_;
v___y_800_ = v___y_843_;
goto v___jp_797_;
}
v___jp_845_:
{
lean_object* v___x_858_; 
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
lean_inc(v___y_855_);
lean_inc_ref(v___y_854_);
lean_inc(v___y_853_);
lean_inc_ref(v___y_852_);
lean_inc(v___y_851_);
lean_inc_ref(v_e_u2082_846_);
v___x_858_ = lean_sym_simp(v_e_u2082_846_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
if (lean_obj_tag(v_a_859_) == 0)
{
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
if (v_cd_u2081_848_ == 0)
{
uint8_t v_done_860_; uint8_t v_contextDependent_861_; 
v_done_860_ = lean_ctor_get_uint8(v_a_859_, 0);
v_contextDependent_861_ = lean_ctor_get_uint8(v_a_859_, 1);
lean_dec_ref_known(v_a_859_, 0);
v___y_832_ = v_e_u2082_846_;
v___y_833_ = v_done_860_;
v___y_834_ = v___y_851_;
v___y_835_ = v_h_u2081_847_;
v___y_836_ = v_contextDependent_861_;
goto v___jp_831_;
}
else
{
uint8_t v_done_862_; 
v_done_862_ = lean_ctor_get_uint8(v_a_859_, 0);
lean_dec_ref_known(v_a_859_, 0);
v___y_832_ = v_e_u2082_846_;
v___y_833_ = v_done_862_;
v___y_834_ = v___y_851_;
v___y_835_ = v_h_u2081_847_;
v___y_836_ = v_cd_u2081_848_;
goto v___jp_831_;
}
}
else
{
lean_object* v_e_x27_863_; lean_object* v_proof_864_; uint8_t v_done_865_; uint8_t v_contextDependent_866_; lean_object* v___x_867_; 
v_e_x27_863_ = lean_ctor_get(v_a_859_, 0);
lean_inc_ref_n(v_e_x27_863_, 2);
v_proof_864_ = lean_ctor_get(v_a_859_, 1);
lean_inc_ref(v_proof_864_);
v_done_865_ = lean_ctor_get_uint8(v_a_859_, sizeof(void*)*2);
v_contextDependent_866_ = lean_ctor_get_uint8(v_a_859_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_859_, 2);
lean_inc_ref(v_e_u2081_786_);
v___x_867_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_786_, v_e_u2082_846_, v_h_u2081_847_, v_e_x27_863_, v_proof_864_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
if (lean_obj_tag(v___x_867_) == 0)
{
if (v_cd_u2081_848_ == 0)
{
lean_object* v_a_868_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___y_839_ = v_a_868_;
v___y_840_ = v_e_x27_863_;
v___y_841_ = v_done_865_;
v___y_842_ = v___y_851_;
v___y_843_ = v_contextDependent_866_;
goto v___jp_838_;
}
else
{
lean_object* v_a_869_; 
v_a_869_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_867_, 1);
v___y_839_ = v_a_869_;
v___y_840_ = v_e_x27_863_;
v___y_841_ = v_done_865_;
v___y_842_ = v___y_851_;
v___y_843_ = v_cd_u2081_848_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v_e_x27_863_);
lean_dec(v___y_851_);
lean_dec_ref(v_e_u2081_786_);
v_a_870_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_867_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_867_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
else
{
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v_h_u2081_847_);
lean_dec_ref(v_e_u2082_846_);
lean_dec_ref(v_e_u2081_786_);
return v___x_858_;
}
}
v___jp_878_:
{
if (lean_obj_tag(v___y_888_) == 0)
{
uint8_t v_contextDependent_889_; 
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_879_);
v_contextDependent_889_ = lean_ctor_get_uint8(v___y_888_, 1);
if (v_contextDependent_889_ == 0)
{
lean_object* v___x_890_; lean_object* v_numSteps_891_; lean_object* v_persistentCache_892_; lean_object* v_transientCache_893_; lean_object* v_funext_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_904_; 
v___x_890_ = lean_st_ref_take(v___y_880_);
v_numSteps_891_ = lean_ctor_get(v___x_890_, 0);
v_persistentCache_892_ = lean_ctor_get(v___x_890_, 1);
v_transientCache_893_ = lean_ctor_get(v___x_890_, 2);
v_funext_894_ = lean_ctor_get(v___x_890_, 3);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_904_ == 0)
{
v___x_896_ = v___x_890_;
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_funext_894_);
lean_inc(v_transientCache_893_);
lean_inc(v_persistentCache_892_);
lean_inc(v_numSteps_891_);
lean_dec(v___x_890_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
lean_inc_ref(v___y_888_);
v___x_898_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_892_, v_e_u2081_786_, v___y_888_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___x_898_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_numSteps_891_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_transientCache_893_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_funext_894_);
v___x_900_ = v_reuseFailAlloc_903_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_st_ref_put(v___y_880_, v___x_900_);
lean_dec(v___y_880_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___y_888_);
return v___x_902_;
}
}
}
else
{
lean_object* v___x_905_; lean_object* v_numSteps_906_; lean_object* v_persistentCache_907_; lean_object* v_transientCache_908_; lean_object* v_funext_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_919_; 
v___x_905_ = lean_st_ref_take(v___y_880_);
v_numSteps_906_ = lean_ctor_get(v___x_905_, 0);
v_persistentCache_907_ = lean_ctor_get(v___x_905_, 1);
v_transientCache_908_ = lean_ctor_get(v___x_905_, 2);
v_funext_909_ = lean_ctor_get(v___x_905_, 3);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_919_ == 0)
{
v___x_911_ = v___x_905_;
v_isShared_912_ = v_isSharedCheck_919_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_funext_909_);
lean_inc(v_transientCache_908_);
lean_inc(v_persistentCache_907_);
lean_inc(v_numSteps_906_);
lean_dec(v___x_905_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_919_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_inc_ref(v___y_888_);
v___x_913_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_908_, v_e_u2081_786_, v___y_888_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 2, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_numSteps_906_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_persistentCache_907_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_funext_909_);
v___x_915_ = v_reuseFailAlloc_918_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_st_ref_put(v___y_880_, v___x_915_);
lean_dec(v___y_880_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___y_888_);
return v___x_917_;
}
}
}
}
else
{
uint8_t v_done_920_; 
v_done_920_ = lean_ctor_get_uint8(v___y_888_, sizeof(void*)*2);
if (v_done_920_ == 0)
{
lean_object* v_e_x27_921_; lean_object* v_proof_922_; uint8_t v_contextDependent_923_; 
v_e_x27_921_ = lean_ctor_get(v___y_888_, 0);
lean_inc_ref(v_e_x27_921_);
v_proof_922_ = lean_ctor_get(v___y_888_, 1);
lean_inc_ref(v_proof_922_);
v_contextDependent_923_ = lean_ctor_get_uint8(v___y_888_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v___y_888_, 2);
v_e_u2082_846_ = v_e_x27_921_;
v_h_u2081_847_ = v_proof_922_;
v_cd_u2081_848_ = v_contextDependent_923_;
v___y_849_ = v___y_886_;
v___y_850_ = v___y_885_;
v___y_851_ = v___y_880_;
v___y_852_ = v___y_887_;
v___y_853_ = v___y_884_;
v___y_854_ = v___y_882_;
v___y_855_ = v___y_883_;
v___y_856_ = v___y_881_;
v___y_857_ = v___y_879_;
goto v___jp_845_;
}
else
{
uint8_t v_contextDependent_924_; 
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_879_);
v_contextDependent_924_ = lean_ctor_get_uint8(v___y_888_, sizeof(void*)*2 + 1);
if (v_contextDependent_924_ == 0)
{
lean_object* v___x_925_; lean_object* v_numSteps_926_; lean_object* v_persistentCache_927_; lean_object* v_transientCache_928_; lean_object* v_funext_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_939_; 
v___x_925_ = lean_st_ref_take(v___y_880_);
v_numSteps_926_ = lean_ctor_get(v___x_925_, 0);
v_persistentCache_927_ = lean_ctor_get(v___x_925_, 1);
v_transientCache_928_ = lean_ctor_get(v___x_925_, 2);
v_funext_929_ = lean_ctor_get(v___x_925_, 3);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_939_ == 0)
{
v___x_931_ = v___x_925_;
v_isShared_932_ = v_isSharedCheck_939_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_funext_929_);
lean_inc(v_transientCache_928_);
lean_inc(v_persistentCache_927_);
lean_inc(v_numSteps_926_);
lean_dec(v___x_925_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_939_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
lean_inc_ref(v___y_888_);
v___x_933_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_927_, v_e_u2081_786_, v___y_888_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_numSteps_926_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_transientCache_928_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_funext_929_);
v___x_935_ = v_reuseFailAlloc_938_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_st_ref_put(v___y_880_, v___x_935_);
lean_dec(v___y_880_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___y_888_);
return v___x_937_;
}
}
}
else
{
lean_object* v___x_940_; lean_object* v_numSteps_941_; lean_object* v_persistentCache_942_; lean_object* v_transientCache_943_; lean_object* v_funext_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_954_; 
v___x_940_ = lean_st_ref_take(v___y_880_);
v_numSteps_941_ = lean_ctor_get(v___x_940_, 0);
v_persistentCache_942_ = lean_ctor_get(v___x_940_, 1);
v_transientCache_943_ = lean_ctor_get(v___x_940_, 2);
v_funext_944_ = lean_ctor_get(v___x_940_, 3);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_954_ == 0)
{
v___x_946_ = v___x_940_;
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_funext_944_);
lean_inc(v_transientCache_943_);
lean_inc(v_persistentCache_942_);
lean_inc(v_numSteps_941_);
lean_dec(v___x_940_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
lean_inc_ref(v___y_888_);
v___x_948_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_943_, v_e_u2081_786_, v___y_888_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 2, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_numSteps_941_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_persistentCache_942_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_funext_944_);
v___x_950_ = v_reuseFailAlloc_953_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_st_ref_put(v___y_880_, v___x_950_);
lean_dec(v___y_880_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___y_888_);
return v___x_952_;
}
}
}
}
}
}
v___jp_955_:
{
if (v___y_966_ == 0)
{
v___y_879_ = v___y_956_;
v___y_880_ = v___y_957_;
v___y_881_ = v___y_959_;
v___y_882_ = v___y_960_;
v___y_883_ = v___y_963_;
v___y_884_ = v___y_962_;
v___y_885_ = v___y_961_;
v___y_886_ = v___y_964_;
v___y_887_ = v___y_965_;
v___y_888_ = v___y_958_;
goto v___jp_878_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_958_);
v___y_879_ = v___y_956_;
v___y_880_ = v___y_957_;
v___y_881_ = v___y_959_;
v___y_882_ = v___y_960_;
v___y_883_ = v___y_963_;
v___y_884_ = v___y_962_;
v___y_885_ = v___y_961_;
v___y_886_ = v___y_964_;
v___y_887_ = v___y_965_;
v___y_888_ = v___x_967_;
goto v___jp_878_;
}
}
v___jp_968_:
{
if (v___y_981_ == 0)
{
v___y_956_ = v___y_974_;
v___y_957_ = v___y_975_;
v___y_958_ = v___y_969_;
v___y_959_ = v___y_970_;
v___y_960_ = v___y_976_;
v___y_961_ = v___y_977_;
v___y_962_ = v___y_971_;
v___y_963_ = v___y_978_;
v___y_964_ = v___y_972_;
v___y_965_ = v___y_973_;
v___y_966_ = v___y_979_;
goto v___jp_955_;
}
else
{
v___y_956_ = v___y_974_;
v___y_957_ = v___y_975_;
v___y_958_ = v___y_969_;
v___y_959_ = v___y_970_;
v___y_960_ = v___y_976_;
v___y_961_ = v___y_977_;
v___y_962_ = v___y_971_;
v___y_963_ = v___y_978_;
v___y_964_ = v___y_972_;
v___y_965_ = v___y_973_;
v___y_966_ = v___y_980_;
goto v___jp_955_;
}
}
v___jp_982_:
{
if (v___y_993_ == 0)
{
v___y_879_ = v___y_983_;
v___y_880_ = v___y_984_;
v___y_881_ = v___y_985_;
v___y_882_ = v___y_986_;
v___y_883_ = v___y_989_;
v___y_884_ = v___y_988_;
v___y_885_ = v___y_987_;
v___y_886_ = v___y_990_;
v___y_887_ = v___y_991_;
v___y_888_ = v_a_994_;
goto v___jp_878_;
}
else
{
if (lean_obj_tag(v_a_994_) == 0)
{
uint8_t v_contextDependent_995_; 
v_contextDependent_995_ = lean_ctor_get_uint8(v_a_994_, 1);
v___y_969_ = v_a_994_;
v___y_970_ = v___y_985_;
v___y_971_ = v___y_988_;
v___y_972_ = v___y_990_;
v___y_973_ = v___y_991_;
v___y_974_ = v___y_983_;
v___y_975_ = v___y_984_;
v___y_976_ = v___y_986_;
v___y_977_ = v___y_987_;
v___y_978_ = v___y_989_;
v___y_979_ = v___y_993_;
v___y_980_ = v___y_992_;
v___y_981_ = v_contextDependent_995_;
goto v___jp_968_;
}
else
{
uint8_t v_contextDependent_996_; 
v_contextDependent_996_ = lean_ctor_get_uint8(v_a_994_, sizeof(void*)*2 + 1);
v___y_969_ = v_a_994_;
v___y_970_ = v___y_985_;
v___y_971_ = v___y_988_;
v___y_972_ = v___y_990_;
v___y_973_ = v___y_991_;
v___y_974_ = v___y_983_;
v___y_975_ = v___y_984_;
v___y_976_ = v___y_986_;
v___y_977_ = v___y_987_;
v___y_978_ = v___y_989_;
v___y_979_ = v___y_993_;
v___y_980_ = v___y_992_;
v___y_981_ = v_contextDependent_996_;
goto v___jp_968_;
}
}
}
v___jp_997_:
{
if (lean_obj_tag(v___y_1009_) == 0)
{
lean_object* v_a_1010_; 
v_a_1010_ = lean_ctor_get(v___y_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___y_1009_, 1);
v___y_983_ = v___y_998_;
v___y_984_ = v___y_999_;
v___y_985_ = v___y_1000_;
v___y_986_ = v___y_1001_;
v___y_987_ = v___y_1004_;
v___y_988_ = v___y_1003_;
v___y_989_ = v___y_1002_;
v___y_990_ = v___y_1005_;
v___y_991_ = v___y_1006_;
v___y_992_ = v___y_1008_;
v___y_993_ = v___y_1007_;
v_a_994_ = v_a_1010_;
goto v___jp_982_;
}
else
{
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v_e_u2081_786_);
return v___y_1009_;
}
}
v___jp_1011_:
{
if (v___y_1024_ == 0)
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1012_);
v___y_983_ = v___y_1017_;
v___y_984_ = v___y_1018_;
v___y_985_ = v___y_1013_;
v___y_986_ = v___y_1019_;
v___y_987_ = v___y_1020_;
v___y_988_ = v___y_1014_;
v___y_989_ = v___y_1021_;
v___y_990_ = v___y_1015_;
v___y_991_ = v___y_1016_;
v___y_992_ = v___y_1022_;
v___y_993_ = v___y_1023_;
v_a_994_ = v___x_1025_;
goto v___jp_982_;
}
else
{
v___y_983_ = v___y_1017_;
v___y_984_ = v___y_1018_;
v___y_985_ = v___y_1013_;
v___y_986_ = v___y_1019_;
v___y_987_ = v___y_1020_;
v___y_988_ = v___y_1014_;
v___y_989_ = v___y_1021_;
v___y_990_ = v___y_1015_;
v___y_991_ = v___y_1016_;
v___y_992_ = v___y_1022_;
v___y_993_ = v___y_1023_;
v_a_994_ = v___y_1012_;
goto v___jp_982_;
}
}
v___jp_1026_:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1042_, 0, v___y_1028_);
lean_ctor_set(v___x_1042_, 1, v___y_1036_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*2, v___y_1034_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*2 + 1, v___y_1041_);
v___y_983_ = v___y_1032_;
v___y_984_ = v___y_1033_;
v___y_985_ = v___y_1027_;
v___y_986_ = v___y_1035_;
v___y_987_ = v___y_1037_;
v___y_988_ = v___y_1029_;
v___y_989_ = v___y_1038_;
v___y_990_ = v___y_1030_;
v___y_991_ = v___y_1031_;
v___y_992_ = v___y_1040_;
v___y_993_ = v___y_1039_;
v_a_994_ = v___x_1042_;
goto v___jp_982_;
}
v___jp_1043_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1059_, 0, v___y_1051_);
lean_ctor_set(v___x_1059_, 1, v___y_1055_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*2, v___y_1044_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*2 + 1, v___y_1058_);
v___y_983_ = v___y_1049_;
v___y_984_ = v___y_1050_;
v___y_985_ = v___y_1045_;
v___y_986_ = v___y_1052_;
v___y_987_ = v___y_1053_;
v___y_988_ = v___y_1046_;
v___y_989_ = v___y_1054_;
v___y_990_ = v___y_1047_;
v___y_991_ = v___y_1048_;
v___y_992_ = v___y_1057_;
v___y_993_ = v___y_1056_;
v_a_994_ = v___x_1059_;
goto v___jp_982_;
}
v_resetjp_1066_:
{
lean_object* v_maxRecDepth_1069_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_maxRecDepth_1069_ = lean_ctor_get(v_toCold_1060_, 3);
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_nat_dec_eq(v_maxRecDepth_1069_, v___x_1360_);
if (v___x_1361_ == 0)
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_nat_dec_eq(v_currRecDepth_1061_, v_maxRecDepth_1069_);
if (v___x_1362_ == 0)
{
goto v___jp_1330_;
}
else
{
lean_object* v___x_1363_; 
lean_del_object(v___x_1067_);
lean_dec(v_currRecDepth_1061_);
lean_dec_ref(v_toCold_1060_);
lean_dec(v_a_795_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_e_u2081_786_);
v___x_1363_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_1062_);
return v___x_1363_;
}
}
else
{
goto v___jp_1330_;
}
v___jp_1070_:
{
lean_object* v___x_1081_; lean_object* v_persistentCache_1082_; lean_object* v_transientCache_1083_; lean_object* v_funext_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1209_; 
v___x_1081_ = lean_st_ref_take(v___y_1074_);
v_persistentCache_1082_ = lean_ctor_get(v___x_1081_, 1);
v_transientCache_1083_ = lean_ctor_get(v___x_1081_, 2);
v_funext_1084_ = lean_ctor_get(v___x_1081_, 3);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v___x_1081_, 0);
lean_dec(v_unused_1210_);
v___x_1086_ = v___x_1081_;
v_isShared_1087_ = v_isSharedCheck_1209_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_funext_1084_);
lean_inc(v_transientCache_1083_);
lean_inc(v_persistentCache_1082_);
lean_dec(v___x_1081_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1209_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___y_1071_);
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___y_1071_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_persistentCache_1082_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_transientCache_1083_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_funext_1084_);
v___x_1089_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v_pre_1091_; lean_object* v___x_1092_; 
v___x_1090_ = lean_st_ref_put(v___y_1074_, v___x_1089_);
v_pre_1091_ = lean_ctor_get(v___y_1072_, 0);
lean_inc_ref(v_pre_1091_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
lean_inc(v___y_1072_);
lean_inc_ref(v_e_u2081_786_);
v___x_1092_ = lean_apply_11(v_pre_1091_, v_e_u2081_786_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, lean_box(0));
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1207_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1207_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1207_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
if (lean_obj_tag(v_a_1093_) == 0)
{
uint8_t v_done_1097_; 
v_done_1097_ = lean_ctor_get_uint8(v_a_1093_, 0);
if (v_done_1097_ == 0)
{
uint8_t v_contextDependent_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_del_object(v___x_1095_);
v_contextDependent_1098_ = lean_ctor_get_uint8(v_a_1093_, 1);
lean_dec_ref_known(v_a_1093_, 0);
v___x_1099_ = lean_box(0);
lean_inc_ref(v_e_u2081_786_);
v___x_1100_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_u2081_786_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
if (lean_obj_tag(v_a_1101_) == 0)
{
uint8_t v_done_1102_; 
v_done_1102_ = lean_ctor_get_uint8(v_a_1101_, 0);
if (v_done_1102_ == 0)
{
uint8_t v_contextDependent_1103_; lean_object* v___x_1104_; 
lean_inc_ref(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v_contextDependent_1103_ = lean_ctor_get_uint8(v_a_1101_, 1);
lean_dec_ref_known(v_a_1101_, 0);
lean_inc_ref(v_e_u2081_786_);
v___x_1104_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1099_, v_e_u2081_786_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1104_) == 0)
{
if (v_contextDependent_1103_ == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___y_983_ = v___y_1080_;
v___y_984_ = v___y_1074_;
v___y_985_ = v___y_1079_;
v___y_986_ = v___y_1077_;
v___y_987_ = v___y_1073_;
v___y_988_ = v___y_1076_;
v___y_989_ = v___y_1078_;
v___y_990_ = v___y_1072_;
v___y_991_ = v___y_1075_;
v___y_992_ = v_done_1097_;
v___y_993_ = v_contextDependent_1098_;
v_a_994_ = v_a_1105_;
goto v___jp_982_;
}
else
{
lean_object* v_a_1106_; 
v_a_1106_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1104_, 1);
if (lean_obj_tag(v_a_1106_) == 0)
{
uint8_t v_contextDependent_1107_; 
v_contextDependent_1107_ = lean_ctor_get_uint8(v_a_1106_, 1);
v___y_1012_ = v_a_1106_;
v___y_1013_ = v___y_1079_;
v___y_1014_ = v___y_1076_;
v___y_1015_ = v___y_1072_;
v___y_1016_ = v___y_1075_;
v___y_1017_ = v___y_1080_;
v___y_1018_ = v___y_1074_;
v___y_1019_ = v___y_1077_;
v___y_1020_ = v___y_1073_;
v___y_1021_ = v___y_1078_;
v___y_1022_ = v_done_1097_;
v___y_1023_ = v_contextDependent_1098_;
v___y_1024_ = v_contextDependent_1107_;
goto v___jp_1011_;
}
else
{
uint8_t v_contextDependent_1108_; 
v_contextDependent_1108_ = lean_ctor_get_uint8(v_a_1106_, sizeof(void*)*2 + 1);
v___y_1012_ = v_a_1106_;
v___y_1013_ = v___y_1079_;
v___y_1014_ = v___y_1076_;
v___y_1015_ = v___y_1072_;
v___y_1016_ = v___y_1075_;
v___y_1017_ = v___y_1080_;
v___y_1018_ = v___y_1074_;
v___y_1019_ = v___y_1077_;
v___y_1020_ = v___y_1073_;
v___y_1021_ = v___y_1078_;
v___y_1022_ = v_done_1097_;
v___y_1023_ = v_contextDependent_1098_;
v___y_1024_ = v_contextDependent_1108_;
goto v___jp_1011_;
}
}
}
else
{
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v_e_u2081_786_);
return v___x_1104_;
}
}
else
{
v___y_998_ = v___y_1080_;
v___y_999_ = v___y_1074_;
v___y_1000_ = v___y_1079_;
v___y_1001_ = v___y_1077_;
v___y_1002_ = v___y_1078_;
v___y_1003_ = v___y_1076_;
v___y_1004_ = v___y_1073_;
v___y_1005_ = v___y_1072_;
v___y_1006_ = v___y_1075_;
v___y_1007_ = v_contextDependent_1098_;
v___y_1008_ = v_done_1097_;
v___y_1009_ = v___x_1100_;
goto v___jp_997_;
}
}
else
{
uint8_t v_done_1109_; 
v_done_1109_ = lean_ctor_get_uint8(v_a_1101_, sizeof(void*)*2);
if (v_done_1109_ == 0)
{
lean_object* v_e_x27_1110_; lean_object* v_proof_1111_; uint8_t v_contextDependent_1112_; lean_object* v___x_1113_; 
lean_inc_ref(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v_e_x27_1110_ = lean_ctor_get(v_a_1101_, 0);
lean_inc_ref_n(v_e_x27_1110_, 2);
v_proof_1111_ = lean_ctor_get(v_a_1101_, 1);
lean_inc_ref(v_proof_1111_);
v_contextDependent_1112_ = lean_ctor_get_uint8(v_a_1101_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1101_, 2);
v___x_1113_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1099_, v_e_x27_1110_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
if (lean_obj_tag(v_a_1114_) == 0)
{
if (v_contextDependent_1112_ == 0)
{
uint8_t v_done_1115_; uint8_t v_contextDependent_1116_; 
v_done_1115_ = lean_ctor_get_uint8(v_a_1114_, 0);
v_contextDependent_1116_ = lean_ctor_get_uint8(v_a_1114_, 1);
lean_dec_ref_known(v_a_1114_, 0);
v___y_1027_ = v___y_1079_;
v___y_1028_ = v_e_x27_1110_;
v___y_1029_ = v___y_1076_;
v___y_1030_ = v___y_1072_;
v___y_1031_ = v___y_1075_;
v___y_1032_ = v___y_1080_;
v___y_1033_ = v___y_1074_;
v___y_1034_ = v_done_1115_;
v___y_1035_ = v___y_1077_;
v___y_1036_ = v_proof_1111_;
v___y_1037_ = v___y_1073_;
v___y_1038_ = v___y_1078_;
v___y_1039_ = v_contextDependent_1098_;
v___y_1040_ = v_done_1097_;
v___y_1041_ = v_contextDependent_1116_;
goto v___jp_1026_;
}
else
{
uint8_t v_done_1117_; 
v_done_1117_ = lean_ctor_get_uint8(v_a_1114_, 0);
lean_dec_ref_known(v_a_1114_, 0);
v___y_1027_ = v___y_1079_;
v___y_1028_ = v_e_x27_1110_;
v___y_1029_ = v___y_1076_;
v___y_1030_ = v___y_1072_;
v___y_1031_ = v___y_1075_;
v___y_1032_ = v___y_1080_;
v___y_1033_ = v___y_1074_;
v___y_1034_ = v_done_1117_;
v___y_1035_ = v___y_1077_;
v___y_1036_ = v_proof_1111_;
v___y_1037_ = v___y_1073_;
v___y_1038_ = v___y_1078_;
v___y_1039_ = v_contextDependent_1098_;
v___y_1040_ = v_done_1097_;
v___y_1041_ = v_contextDependent_1112_;
goto v___jp_1026_;
}
}
else
{
lean_object* v_e_x27_1118_; lean_object* v_proof_1119_; uint8_t v_done_1120_; uint8_t v_contextDependent_1121_; lean_object* v___x_1122_; 
v_e_x27_1118_ = lean_ctor_get(v_a_1114_, 0);
lean_inc_ref_n(v_e_x27_1118_, 2);
v_proof_1119_ = lean_ctor_get(v_a_1114_, 1);
lean_inc_ref(v_proof_1119_);
v_done_1120_ = lean_ctor_get_uint8(v_a_1114_, sizeof(void*)*2);
v_contextDependent_1121_ = lean_ctor_get_uint8(v_a_1114_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1114_, 2);
lean_inc_ref(v_e_u2081_786_);
v___x_1122_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_786_, v_e_x27_1110_, v_proof_1111_, v_e_x27_1118_, v_proof_1119_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1122_) == 0)
{
if (v_contextDependent_1112_ == 0)
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___y_1044_ = v_done_1120_;
v___y_1045_ = v___y_1079_;
v___y_1046_ = v___y_1076_;
v___y_1047_ = v___y_1072_;
v___y_1048_ = v___y_1075_;
v___y_1049_ = v___y_1080_;
v___y_1050_ = v___y_1074_;
v___y_1051_ = v_e_x27_1118_;
v___y_1052_ = v___y_1077_;
v___y_1053_ = v___y_1073_;
v___y_1054_ = v___y_1078_;
v___y_1055_ = v_a_1123_;
v___y_1056_ = v_contextDependent_1098_;
v___y_1057_ = v_done_1097_;
v___y_1058_ = v_contextDependent_1121_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1124_; 
v_a_1124_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1122_, 1);
v___y_1044_ = v_done_1120_;
v___y_1045_ = v___y_1079_;
v___y_1046_ = v___y_1076_;
v___y_1047_ = v___y_1072_;
v___y_1048_ = v___y_1075_;
v___y_1049_ = v___y_1080_;
v___y_1050_ = v___y_1074_;
v___y_1051_ = v_e_x27_1118_;
v___y_1052_ = v___y_1077_;
v___y_1053_ = v___y_1073_;
v___y_1054_ = v___y_1078_;
v___y_1055_ = v_a_1124_;
v___y_1056_ = v_contextDependent_1098_;
v___y_1057_ = v_done_1097_;
v___y_1058_ = v_contextDependent_1112_;
goto v___jp_1043_;
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_e_x27_1118_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v_e_u2081_786_);
v_a_1125_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1122_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1122_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1111_);
lean_dec_ref(v_e_x27_1110_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v_e_u2081_786_);
return v___x_1113_;
}
}
else
{
v___y_998_ = v___y_1080_;
v___y_999_ = v___y_1074_;
v___y_1000_ = v___y_1079_;
v___y_1001_ = v___y_1077_;
v___y_1002_ = v___y_1078_;
v___y_1003_ = v___y_1076_;
v___y_1004_ = v___y_1073_;
v___y_1005_ = v___y_1072_;
v___y_1006_ = v___y_1075_;
v___y_1007_ = v_contextDependent_1098_;
v___y_1008_ = v_done_1097_;
v___y_1009_ = v___x_1100_;
goto v___jp_997_;
}
}
}
else
{
v___y_998_ = v___y_1080_;
v___y_999_ = v___y_1074_;
v___y_1000_ = v___y_1079_;
v___y_1001_ = v___y_1077_;
v___y_1002_ = v___y_1078_;
v___y_1003_ = v___y_1076_;
v___y_1004_ = v___y_1073_;
v___y_1005_ = v___y_1072_;
v___y_1006_ = v___y_1075_;
v___y_1007_ = v_contextDependent_1098_;
v___y_1008_ = v_done_1097_;
v___y_1009_ = v___x_1100_;
goto v___jp_997_;
}
}
else
{
uint8_t v_contextDependent_1133_; 
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
v_contextDependent_1133_ = lean_ctor_get_uint8(v_a_1093_, 1);
if (v_contextDependent_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v_numSteps_1135_; lean_object* v_persistentCache_1136_; lean_object* v_transientCache_1137_; lean_object* v_funext_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1150_; 
v___x_1134_ = lean_st_ref_take(v___y_1074_);
v_numSteps_1135_ = lean_ctor_get(v___x_1134_, 0);
v_persistentCache_1136_ = lean_ctor_get(v___x_1134_, 1);
v_transientCache_1137_ = lean_ctor_get(v___x_1134_, 2);
v_funext_1138_ = lean_ctor_get(v___x_1134_, 3);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1140_ = v___x_1134_;
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_funext_1138_);
lean_inc(v_transientCache_1137_);
lean_inc(v_persistentCache_1136_);
lean_inc(v_numSteps_1135_);
lean_dec(v___x_1134_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_inc_ref(v_a_1093_);
v___x_1142_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1136_, v_e_u2081_786_, v_a_1093_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1142_);
v___x_1144_ = v___x_1140_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_numSteps_1135_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_transientCache_1137_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_funext_1138_);
v___x_1144_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_st_ref_put(v___y_1074_, v___x_1144_);
lean_dec(v___y_1074_);
if (v_isShared_1096_ == 0)
{
v___x_1147_ = v___x_1095_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1093_);
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
else
{
lean_object* v___x_1151_; lean_object* v_numSteps_1152_; lean_object* v_persistentCache_1153_; lean_object* v_transientCache_1154_; lean_object* v_funext_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1167_; 
v___x_1151_ = lean_st_ref_take(v___y_1074_);
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
lean_inc_ref(v_a_1093_);
v___x_1159_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1154_, v_e_u2081_786_, v_a_1093_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 2, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_numSteps_1152_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_persistentCache_1153_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_funext_1155_);
v___x_1161_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_st_ref_put(v___y_1074_, v___x_1161_);
lean_dec(v___y_1074_);
if (v_isShared_1096_ == 0)
{
v___x_1164_ = v___x_1095_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1093_);
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
}
}
else
{
uint8_t v_done_1168_; 
v_done_1168_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*2);
if (v_done_1168_ == 0)
{
lean_object* v_e_x27_1169_; lean_object* v_proof_1170_; uint8_t v_contextDependent_1171_; 
lean_del_object(v___x_1095_);
v_e_x27_1169_ = lean_ctor_get(v_a_1093_, 0);
lean_inc_ref(v_e_x27_1169_);
v_proof_1170_ = lean_ctor_get(v_a_1093_, 1);
lean_inc_ref(v_proof_1170_);
v_contextDependent_1171_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1093_, 2);
v_e_u2082_846_ = v_e_x27_1169_;
v_h_u2081_847_ = v_proof_1170_;
v_cd_u2081_848_ = v_contextDependent_1171_;
v___y_849_ = v___y_1072_;
v___y_850_ = v___y_1073_;
v___y_851_ = v___y_1074_;
v___y_852_ = v___y_1075_;
v___y_853_ = v___y_1076_;
v___y_854_ = v___y_1077_;
v___y_855_ = v___y_1078_;
v___y_856_ = v___y_1079_;
v___y_857_ = v___y_1080_;
goto v___jp_845_;
}
else
{
uint8_t v_contextDependent_1172_; 
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
v_contextDependent_1172_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*2 + 1);
if (v_contextDependent_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v_numSteps_1174_; lean_object* v_persistentCache_1175_; lean_object* v_transientCache_1176_; lean_object* v_funext_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1189_; 
v___x_1173_ = lean_st_ref_take(v___y_1074_);
v_numSteps_1174_ = lean_ctor_get(v___x_1173_, 0);
v_persistentCache_1175_ = lean_ctor_get(v___x_1173_, 1);
v_transientCache_1176_ = lean_ctor_get(v___x_1173_, 2);
v_funext_1177_ = lean_ctor_get(v___x_1173_, 3);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1179_ = v___x_1173_;
v_isShared_1180_ = v_isSharedCheck_1189_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_funext_1177_);
lean_inc(v_transientCache_1176_);
lean_inc(v_persistentCache_1175_);
lean_inc(v_numSteps_1174_);
lean_dec(v___x_1173_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1189_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_inc_ref(v_a_1093_);
v___x_1181_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1175_, v_e_u2081_786_, v_a_1093_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___x_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_numSteps_1174_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_transientCache_1176_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_funext_1177_);
v___x_1183_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_st_ref_put(v___y_1074_, v___x_1183_);
lean_dec(v___y_1074_);
if (v_isShared_1096_ == 0)
{
v___x_1186_ = v___x_1095_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1093_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v___x_1190_; lean_object* v_numSteps_1191_; lean_object* v_persistentCache_1192_; lean_object* v_transientCache_1193_; lean_object* v_funext_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1206_; 
v___x_1190_ = lean_st_ref_take(v___y_1074_);
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
lean_inc_ref(v_a_1093_);
v___x_1198_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1193_, v_e_u2081_786_, v_a_1093_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 2, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_numSteps_1191_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_persistentCache_1192_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_funext_1194_);
v___x_1200_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_st_ref_put(v___y_1074_, v___x_1200_);
lean_dec(v___y_1074_);
if (v_isShared_1096_ == 0)
{
v___x_1203_ = v___x_1095_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1093_);
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
}
}
}
}
else
{
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v_e_u2081_786_);
return v___x_1092_;
}
}
}
}
v___jp_1211_:
{
lean_object* v___x_1223_; lean_object* v_persistentCache_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_st_ref_get(v___y_1216_);
v_persistentCache_1224_ = lean_ctor_get(v___x_1223_, 1);
lean_inc_ref(v_persistentCache_1224_);
lean_dec(v___x_1223_);
v___x_1225_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_persistentCache_1224_, v_e_u2081_786_);
lean_dec_ref(v_persistentCache_1224_);
if (lean_obj_tag(v___x_1225_) == 1)
{
lean_object* v_toCold_1226_; lean_object* v_options_1227_; uint8_t v_hasTrace_1228_; 
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec(v___y_1212_);
v_toCold_1226_ = lean_ctor_get(v___y_1221_, 0);
v_options_1227_ = lean_ctor_get(v_toCold_1226_, 2);
v_hasTrace_1228_ = lean_ctor_get_uint8(v_options_1227_, sizeof(void*)*1);
if (v_hasTrace_1228_ == 0)
{
lean_object* v_val_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_e_u2081_786_);
v_val_1229_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1225_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_val_1229_);
lean_dec(v___x_1225_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 0);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_val_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
lean_object* v_val_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1268_; 
v_val_1237_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1239_ = v___x_1225_;
v_isShared_1240_ = v_isSharedCheck_1268_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_val_1237_);
lean_dec(v___x_1225_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1268_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_inheritedTraceOptions_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_inheritedTraceOptions_1241_ = lean_ctor_get(v_toCold_1226_, 11);
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1243_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1241_, v_options_1227_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1246_; 
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_e_u2081_786_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set_tag(v___x_1239_, 0);
v___x_1246_ = v___x_1239_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_val_1237_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_del_object(v___x_1239_);
v___x_1248_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4);
v___x_1249_ = l_Lean_MessageData_ofExpr(v_e_u2081_786_);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1242_, v___x_1250_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1259_);
v___x_1253_ = v___x_1251_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v___x_1251_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v_val_1237_);
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_val_1237_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_val_1237_);
v_a_1260_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1251_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1251_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1269_; lean_object* v_transientCache_1270_; lean_object* v___x_1271_; 
lean_dec(v___x_1225_);
v___x_1269_ = lean_st_ref_get(v___y_1216_);
v_transientCache_1270_ = lean_ctor_get(v___x_1269_, 2);
lean_inc_ref(v_transientCache_1270_);
lean_dec(v___x_1269_);
v___x_1271_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_transientCache_1270_, v_e_u2081_786_);
lean_dec_ref(v_transientCache_1270_);
if (lean_obj_tag(v___x_1271_) == 1)
{
lean_object* v_toCold_1272_; lean_object* v_options_1273_; uint8_t v_hasTrace_1274_; 
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec(v___y_1212_);
v_toCold_1272_ = lean_ctor_get(v___y_1221_, 0);
v_options_1273_ = lean_ctor_get(v_toCold_1272_, 2);
v_hasTrace_1274_ = lean_ctor_get_uint8(v_options_1273_, sizeof(void*)*1);
if (v_hasTrace_1274_ == 0)
{
lean_object* v_val_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_e_u2081_786_);
v_val_1275_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1271_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_val_1275_);
lean_dec(v___x_1271_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 0);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_val_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1314_; 
v_val_1283_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1285_ = v___x_1271_;
v_isShared_1286_ = v_isSharedCheck_1314_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v___x_1271_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1314_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_inheritedTraceOptions_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_inheritedTraceOptions_1287_ = lean_ctor_get(v_toCold_1272_, 11);
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1289_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1290_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1287_, v_options_1273_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1292_; 
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_e_u2081_786_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 0);
v___x_1292_ = v___x_1285_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_val_1283_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_del_object(v___x_1285_);
v___x_1294_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6);
v___x_1295_ = l_Lean_MessageData_ofExpr(v_e_u2081_786_);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1288_, v___x_1296_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; 
v_unused_1305_ = lean_ctor_get(v___x_1297_, 0);
lean_dec(v_unused_1305_);
v___x_1299_ = v___x_1297_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v___x_1297_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_val_1283_);
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_val_1283_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_val_1283_);
v_a_1306_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1297_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1297_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
lean_dec(v___x_1271_);
v___x_1315_ = lean_nat_add(v___y_1212_, v___y_1213_);
lean_dec(v___y_1212_);
v___x_1316_ = lean_unsigned_to_nat(1000u);
v___x_1317_ = lean_nat_mod(v___x_1315_, v___x_1316_);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = lean_nat_dec_eq(v___x_1317_, v___x_1318_);
lean_dec(v___x_1317_);
if (v___x_1319_ == 0)
{
v___y_1071_ = v___x_1315_;
v___y_1072_ = v___y_1214_;
v___y_1073_ = v___y_1215_;
v___y_1074_ = v___y_1216_;
v___y_1075_ = v___y_1217_;
v___y_1076_ = v___y_1218_;
v___y_1077_ = v___y_1219_;
v___y_1078_ = v___y_1220_;
v___y_1079_ = v___y_1221_;
v___y_1080_ = v___y_1222_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1321_ = l_Lean_Core_checkSystem(v___x_1320_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_dec_ref_known(v___x_1321_, 1);
v___y_1071_ = v___x_1315_;
v___y_1072_ = v___y_1214_;
v___y_1073_ = v___y_1215_;
v___y_1074_ = v___y_1216_;
v___y_1075_ = v___y_1217_;
v___y_1076_ = v___y_1218_;
v___y_1077_ = v___y_1219_;
v___y_1078_ = v___y_1220_;
v___y_1079_ = v___y_1221_;
v___y_1080_ = v___y_1222_;
goto v___jp_1070_;
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v___x_1315_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v_e_u2081_786_);
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
}
}
v___jp_1330_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_nat_add(v_currRecDepth_1061_, v___x_1331_);
lean_dec(v_currRecDepth_1061_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 1, v___x_1332_);
v___x_1334_ = v___x_1067_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_toCold_1060_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_ref_1062_);
lean_ctor_set_uint16(v_reuseFailAlloc_1359_, sizeof(void*)*3, v_optionFlags_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1359_, sizeof(void*)*3 + 2, v_suppressElabErrors_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1359_, sizeof(void*)*3 + 3, v_isRecordingDeps_1065_);
v___x_1334_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v_numSteps_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_st_ref_get(v_a_789_);
v_numSteps_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_numSteps_1336_);
lean_dec(v___x_1335_);
v___x_1337_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_788_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v_maxSteps_1339_; uint8_t v___x_1340_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v_maxSteps_1339_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_maxSteps_1339_);
lean_dec(v_a_1338_);
v___x_1340_ = lean_nat_dec_le(v_maxSteps_1339_, v_numSteps_1336_);
lean_dec(v_maxSteps_1339_);
if (v___x_1340_ == 0)
{
v___y_1212_ = v_numSteps_1336_;
v___y_1213_ = v___x_1331_;
v___y_1214_ = v_a_787_;
v___y_1215_ = v_a_788_;
v___y_1216_ = v_a_789_;
v___y_1217_ = v_a_790_;
v___y_1218_ = v_a_791_;
v___y_1219_ = v_a_792_;
v___y_1220_ = v_a_793_;
v___y_1221_ = v___x_1334_;
v___y_1222_ = v_a_795_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_numSteps_1336_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_e_u2081_786_);
v___x_1341_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8);
v___x_1342_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_1341_, v_a_792_, v_a_793_, v___x_1334_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v___x_1334_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_numSteps_1336_);
lean_dec_ref(v___x_1334_);
lean_dec(v_a_795_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_e_u2081_786_);
v_a_1351_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1337_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1337_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void lean_sym_simp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2081_786_ = stack[0].m_obj;
lean_object* v_a_787_ = stack[1].m_obj;
lean_object* v_a_788_ = stack[2].m_obj;
lean_object* v_a_789_ = stack[3].m_obj;
lean_object* v_a_790_ = stack[4].m_obj;
lean_object* v_a_791_ = stack[5].m_obj;
lean_object* v_a_792_ = stack[6].m_obj;
lean_object* v_a_793_ = stack[7].m_obj;
lean_object* v_a_794_ = stack[8].m_obj;
lean_object* v_a_795_ = stack[9].m_obj;
lean_object* v_res_1365_;
v_res_1365_ = lean_sym_simp(v_e_u2081_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
stack->m_obj
 = v_res_1365_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* v_e_u2081_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = lean_sym_simp(v_e_u2081_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* v_00_u03b2_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_1379_, v_x_1380_, v_x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* v_00_u03b2_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_1384_, v_x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* v_00_u03b2_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_1387_, v_x_1388_, v_x_1389_);
lean_dec_ref(v_x_1389_);
lean_dec_ref(v_x_1388_);
return v_res_1390_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* v_cls_1391_, lean_object* v_msg_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_1391_, v_msg_1392_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1391_ = stack[0].m_obj;
lean_object* v_msg_1392_ = stack[1].m_obj;
lean_object* v___y_1393_ = stack[2].m_obj;
lean_object* v___y_1394_ = stack[3].m_obj;
lean_object* v___y_1395_ = stack[4].m_obj;
lean_object* v___y_1396_ = stack[5].m_obj;
lean_object* v___y_1397_ = stack[6].m_obj;
lean_object* v___y_1398_ = stack[7].m_obj;
lean_object* v___y_1399_ = stack[8].m_obj;
lean_object* v___y_1400_ = stack[9].m_obj;
lean_object* v___y_1401_ = stack[10].m_obj;
lean_object* v_res_1404_;
v_res_1404_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_1391_, v_msg_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
stack->m_obj
 = v_res_1404_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* v_cls_1405_, lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_1405_, v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
return v_res_1417_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* v_00_u03b2_1418_, lean_object* v_x_1419_, size_t v_x_1420_, size_t v_x_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_1419_, v_x_1420_, v_x_1421_, v_x_1422_, v_x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1419_ = stack[1].m_obj;
size_t v_x_1420_ = stack[2].m_num;
size_t v_x_1421_ = stack[3].m_num;
lean_object* v_x_1422_ = stack[4].m_obj;
lean_object* v_x_1423_ = stack[5].m_obj;
lean_object* v_res_1425_;
v_res_1425_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_box(0), v_x_1419_, v_x_1420_, v_x_1421_, v_x_1422_, v_x_1423_);
stack->m_obj
 = v_res_1425_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
size_t v_x_112329__boxed_1432_; size_t v_x_112330__boxed_1433_; lean_object* v_res_1434_; 
v_x_112329__boxed_1432_ = lean_unbox_usize(v_x_1428_);
lean_dec(v_x_1428_);
v_x_112330__boxed_1433_ = lean_unbox_usize(v_x_1429_);
lean_dec(v_x_1429_);
v_res_1434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_1426_, v_x_1427_, v_x_112329__boxed_1432_, v_x_112330__boxed_1433_, v_x_1430_, v_x_1431_);
return v_res_1434_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* v_00_u03b2_1435_, lean_object* v_x_1436_, size_t v_x_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_1436_, v_x_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1436_ = stack[1].m_obj;
size_t v_x_1437_ = stack[2].m_num;
lean_object* v_x_1438_ = stack[3].m_obj;
lean_object* v_res_1440_;
v_res_1440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_box(0), v_x_1436_, v_x_1437_, v_x_1438_);
stack->m_obj
 = v_res_1440_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
size_t v_x_112357__boxed_1445_; lean_object* v_res_1446_; 
v_x_112357__boxed_1445_ = lean_unbox_usize(v_x_1443_);
lean_dec(v_x_1443_);
v_res_1446_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_1441_, v_x_1442_, v_x_112357__boxed_1445_, v_x_1444_);
lean_dec_ref(v_x_1444_);
lean_dec_ref(v_x_1442_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1447_, lean_object* v_n_1448_, lean_object* v_k_1449_, lean_object* v_v_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v_n_1448_, v_k_1449_, v_v_1450_);
return v___x_1451_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1452_, size_t v_depth_1453_, lean_object* v_keys_1454_, lean_object* v_vals_1455_, lean_object* v_heq_1456_, lean_object* v_i_1457_, lean_object* v_entries_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_1453_, v_keys_1454_, v_vals_1455_, v_i_1457_, v_entries_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1453_ = stack[1].m_num;
lean_object* v_keys_1454_ = stack[2].m_obj;
lean_object* v_vals_1455_ = stack[3].m_obj;
lean_object* v_i_1457_ = stack[5].m_obj;
lean_object* v_entries_1458_ = stack[6].m_obj;
lean_object* v_res_1460_;
v_res_1460_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_box(0), v_depth_1453_, v_keys_1454_, v_vals_1455_, lean_box(0), v_i_1457_, v_entries_1458_);
stack->m_obj
 = v_res_1460_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1461_, lean_object* v_depth_1462_, lean_object* v_keys_1463_, lean_object* v_vals_1464_, lean_object* v_heq_1465_, lean_object* v_i_1466_, lean_object* v_entries_1467_){
_start:
{
size_t v_depth_boxed_1468_; lean_object* v_res_1469_; 
v_depth_boxed_1468_ = lean_unbox_usize(v_depth_1462_);
lean_dec(v_depth_1462_);
v_res_1469_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(v_00_u03b2_1461_, v_depth_boxed_1468_, v_keys_1463_, v_vals_1464_, v_heq_1465_, v_i_1466_, v_entries_1467_);
lean_dec_ref(v_vals_1464_);
lean_dec_ref(v_keys_1463_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1470_, lean_object* v_keys_1471_, lean_object* v_vals_1472_, lean_object* v_heq_1473_, lean_object* v_i_1474_, lean_object* v_k_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1471_, v_vals_1472_, v_i_1474_, v_k_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1477_, lean_object* v_keys_1478_, lean_object* v_vals_1479_, lean_object* v_heq_1480_, lean_object* v_i_1481_, lean_object* v_k_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(v_00_u03b2_1477_, v_keys_1478_, v_vals_1479_, v_heq_1480_, v_i_1481_, v_k_1482_);
lean_dec_ref(v_k_1482_);
lean_dec_ref(v_vals_1479_);
lean_dec_ref(v_keys_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1485_, v_x_1486_, v_x_1487_, v_x_1488_);
return v___x_1489_;
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
