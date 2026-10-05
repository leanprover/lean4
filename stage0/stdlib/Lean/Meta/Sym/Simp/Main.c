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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(lean_object* v_e_103_){
_start:
{
uint8_t v___y_105_; uint8_t v___y_114_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__5));
v___x_127_ = lean_unsigned_to_nat(3u);
v___x_128_ = l_Lean_Expr_isAppOfArity(v_e_103_, v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
v___y_114_ = v___x_128_;
goto v___jp_113_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = l_Lean_Expr_getAppNumArgs(v_e_103_);
v___x_131_ = lean_nat_sub(v___x_130_, v___x_129_);
lean_dec(v___x_130_);
v___x_132_ = lean_nat_sub(v___x_131_, v___x_129_);
lean_dec(v___x_131_);
v___x_133_ = l_Lean_Expr_getRevArg_x21(v_e_103_, v___x_132_);
v___x_134_ = l_Lean_Expr_isRawNatLit(v___x_133_);
lean_dec_ref(v___x_133_);
v___y_114_ = v___x_134_;
goto v___jp_113_;
}
v___jp_104_:
{
if (v___y_105_ == 0)
{
return v___y_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_106_ = lean_unsigned_to_nat(4u);
v___x_107_ = l_Lean_Expr_getAppNumArgs(v_e_103_);
v___x_108_ = lean_nat_sub(v___x_107_, v___x_106_);
lean_dec(v___x_107_);
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_sub(v___x_108_, v___x_109_);
lean_dec(v___x_108_);
v___x_111_ = l_Lean_Expr_getRevArg_x21(v_e_103_, v___x_110_);
v___x_112_ = l_Lean_Expr_isRawNatLit(v___x_111_);
lean_dec_ref(v___x_111_);
return v___x_112_;
}
}
v___jp_113_:
{
if (v___y_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = l_Lean_Expr_isCharLit(v_e_103_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__2));
v___x_117_ = lean_unsigned_to_nat(5u);
v___x_118_ = l_Lean_Expr_isAppOfArity(v_e_103_, v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
v___y_105_ = v___x_118_;
goto v___jp_104_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_119_ = lean_unsigned_to_nat(2u);
v___x_120_ = l_Lean_Expr_getAppNumArgs(v_e_103_);
v___x_121_ = lean_nat_sub(v___x_120_, v___x_119_);
lean_dec(v___x_120_);
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_sub(v___x_121_, v___x_122_);
lean_dec(v___x_121_);
v___x_124_ = l_Lean_Expr_getRevArg_x21(v_e_103_, v___x_123_);
v___x_125_ = l_Lean_Expr_isRawNatLit(v___x_124_);
lean_dec_ref(v___x_124_);
v___y_105_ = v___x_125_;
goto v___jp_104_;
}
}
else
{
return v___x_115_;
}
}
else
{
return v___y_114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___boxed(lean_object* v_e_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(v_e_135_);
lean_dec_ref(v_e_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object* v_d_138_, lean_object* v_e_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___y_148_; lean_object* v___x_151_; uint8_t v_debug_152_; 
v___x_151_ = lean_st_ref_get(v___y_141_);
v_debug_152_ = lean_ctor_get_uint8(v___x_151_, sizeof(void*)*12);
lean_dec(v___x_151_);
if (v_debug_152_ == 0)
{
v___y_148_ = v___y_141_;
goto v___jp_147_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_dec_ref_known(v___x_153_, 1);
v___y_148_ = v___y_141_;
goto v___jp_147_;
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v_e_139_);
lean_dec(v_d_138_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = l_Lean_Expr_mdata___override(v_d_138_, v_e_139_);
v___x_150_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_149_, v___y_148_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object* v_d_162_, lean_object* v_e_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_162_, v_e_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object* v_d_172_, lean_object* v_e_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_172_, v_e_173_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object* v_d_185_, lean_object* v_e_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(v_d_185_, v_e_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object* v_msgData_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; lean_object* v_env_205_; uint8_t v___x_206_; lean_object* v_env_207_; lean_object* v___x_208_; lean_object* v_toCold_209_; lean_object* v_mctx_210_; lean_object* v_lctx_211_; lean_object* v_options_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_204_ = lean_st_ref_get(v___y_202_);
v_env_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc_ref(v_env_205_);
lean_dec(v___x_204_);
v___x_206_ = 0;
v_env_207_ = l_Lean_Environment_setRecordingDeps(v_env_205_, v___x_206_);
v___x_208_ = lean_st_ref_get(v___y_200_);
v_toCold_209_ = lean_ctor_get(v___y_201_, 0);
v_mctx_210_ = lean_ctor_get(v___x_208_, 0);
lean_inc_ref(v_mctx_210_);
lean_dec(v___x_208_);
v_lctx_211_ = lean_ctor_get(v___y_199_, 2);
v_options_212_ = lean_ctor_get(v_toCold_209_, 2);
lean_inc_ref(v_options_212_);
lean_inc_ref(v_lctx_211_);
v___x_213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_213_, 0, v_env_207_);
lean_ctor_set(v___x_213_, 1, v_mctx_210_);
lean_ctor_set(v___x_213_, 2, v_lctx_211_);
lean_ctor_set(v___x_213_, 3, v_options_212_);
v___x_214_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v_msgData_198_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object* v_msgData_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msgData_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object* v_msg_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_ref_229_; lean_object* v___x_230_; lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_ref_229_ = lean_ctor_get(v___y_226_, 2);
v___x_230_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
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
lean_inc(v_ref_229_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_ref_229_);
lean_ctor_set(v___x_235_, 1, v_a_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 1);
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3));
v___x_254_ = l_Lean_stringToMessageData(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object* v_e_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
switch(lean_obj_tag(v_e_255_))
{
case 5:
{
uint8_t v___x_266_; 
v___x_266_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(v_e_255_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref_known(v_e_255_, 2);
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
}
case 6:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
return v___x_270_;
}
case 7:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
return v___x_271_;
}
case 8:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
return v___x_272_;
}
case 9:
{
lean_object* v_a_273_; 
v_a_273_ = lean_ctor_get(v_e_255_, 0);
lean_inc_ref(v_a_273_);
lean_dec_ref_known(v_e_255_, 1);
if (lean_obj_tag(v_a_273_) == 0)
{
lean_object* v_val_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_val_274_ = lean_ctor_get(v_a_273_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v_a_273_, 1);
v___x_275_ = l_Lean_mkNatLit(v_val_274_);
v___x_276_ = l_Lean_Meta_Sym_shareCommonInc(v___x_275_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc_n(v_a_277_, 2);
lean_dec_ref_known(v___x_276_, 1);
v___x_278_ = l_Lean_Meta_Sym_mkEqRefl(v_a_277_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_288_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_288_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = 0;
v___x_284_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_284_, 0, v_a_277_);
lean_ctor_set(v___x_284_, 1, v_a_279_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*2, v___x_283_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*2 + 1, v___x_283_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_284_);
v___x_286_ = v___x_281_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_a_277_);
v_a_289_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_278_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_278_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_a_297_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_276_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_276_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref(v_a_273_);
v___x_305_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
case 10:
{
lean_object* v_data_307_; lean_object* v_expr_308_; lean_object* v___x_309_; 
v_data_307_ = lean_ctor_get(v_e_255_, 0);
lean_inc(v_data_307_);
v_expr_308_ = lean_ctor_get(v_e_255_, 1);
lean_inc_ref(v_expr_308_);
lean_dec_ref_known(v_e_255_, 2);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
v___x_309_ = lean_sym_simp(v_expr_308_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_347_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_347_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_347_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_347_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
if (lean_obj_tag(v_a_310_) == 0)
{
uint8_t v_contextDependent_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec(v_data_307_);
v_contextDependent_314_ = lean_ctor_get_uint8(v_a_310_, 1);
lean_dec_ref_known(v_a_310_, 0);
v___x_315_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_314_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_315_);
v___x_317_ = v___x_312_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v_e_x27_319_; lean_object* v_proof_320_; uint8_t v_contextDependent_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_346_; 
lean_del_object(v___x_312_);
v_e_x27_319_ = lean_ctor_get(v_a_310_, 0);
v_proof_320_ = lean_ctor_get(v_a_310_, 1);
v_contextDependent_321_ = lean_ctor_get_uint8(v_a_310_, sizeof(void*)*2 + 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_346_ == 0)
{
v___x_323_ = v_a_310_;
v_isShared_324_ = v_isSharedCheck_346_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_proof_320_);
lean_inc(v_e_x27_319_);
lean_dec(v_a_310_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_346_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_data_307_, v_e_x27_319_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_337_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_337_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; lean_object* v___x_332_; 
v___x_330_ = 0;
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_326_);
v___x_332_ = v___x_323_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_proof_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*2 + 1, v_contextDependent_321_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*2, v___x_330_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_332_);
v___x_334_ = v___x_328_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_del_object(v___x_323_);
lean_dec_ref(v_proof_320_);
v_a_338_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_325_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_325_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
}
}
else
{
lean_dec(v_data_307_);
return v___x_309_;
}
}
case 11:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_348_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2);
v___x_349_ = l_Lean_indentExpr(v_e_255_);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_352_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
return v___x_353_;
}
default: 
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec_ref(v_e_255_);
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object* v_e_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object* v_00_u03b1_368_, lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_369_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object* v_00_u03b1_381_, lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(v_00_u03b1_381_, v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
return v_res_393_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = l_Lean_maxRecDepthErrorMessage;
v___x_400_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3);
v___x_402_ = l_Lean_MessageData_ofFormat(v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4);
v___x_404_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2));
v___x_405_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(lean_object* v_ref_406_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_ref_406_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(lean_object* v_ref_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_object* v_00_u03b1_414_, lean_object* v_ref_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_415_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(lean_object* v_00_u03b1_427_, lean_object* v_ref_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(v_00_u03b1_427_, v_ref_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_post_452_; lean_object* v___x_453_; 
v_post_452_ = lean_ctor_get(v___y_442_, 1);
lean_inc_ref(v_post_452_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
lean_inc(v___y_448_);
lean_inc_ref(v___y_447_);
lean_inc(v___y_446_);
lean_inc_ref(v___y_445_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v___y_442_);
v___x_453_ = lean_apply_11(v_post_452_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, lean_box(0));
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object* v_x_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v_x_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_ks_471_; lean_object* v_vs_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_498_; 
v_ks_471_ = lean_ctor_get(v_x_467_, 0);
v_vs_472_ = lean_ctor_get(v_x_467_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_x_467_);
if (v_isSharedCheck_498_ == 0)
{
v___x_474_ = v_x_467_;
v_isShared_475_ = v_isSharedCheck_498_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_vs_472_);
lean_inc(v_ks_471_);
lean_dec(v_x_467_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_498_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_array_get_size(v_ks_471_);
v___x_477_ = lean_nat_dec_lt(v_x_468_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec(v_x_468_);
v___x_478_ = lean_array_push(v_ks_471_, v_x_469_);
v___x_479_ = lean_array_push(v_vs_472_, v_x_470_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_479_);
lean_ctor_set(v___x_474_, 0, v___x_478_);
v___x_481_ = v___x_474_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v_k_x27_483_; size_t v___x_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_k_x27_483_ = lean_array_fget_borrowed(v_ks_471_, v_x_468_);
v___x_484_ = lean_ptr_addr(v_x_469_);
v___x_485_ = lean_ptr_addr(v_k_x27_483_);
v___x_486_ = lean_usize_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_488_; 
if (v_isShared_475_ == 0)
{
v___x_488_ = v___x_474_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_ks_471_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_vs_472_);
v___x_488_ = v_reuseFailAlloc_492_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_add(v_x_468_, v___x_489_);
lean_dec(v_x_468_);
v_x_467_ = v___x_488_;
v_x_468_ = v___x_490_;
goto _start;
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_493_ = lean_array_fset(v_ks_471_, v_x_468_, v_x_469_);
v___x_494_ = lean_array_fset(v_vs_472_, v_x_468_, v_x_470_);
lean_dec(v_x_468_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_494_);
lean_ctor_set(v___x_474_, 0, v___x_493_);
v___x_496_ = v___x_474_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_499_, lean_object* v_k_500_, lean_object* v_v_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_n_499_, v___x_502_, v_k_500_, v_v_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* v_x_505_, size_t v_x_506_, size_t v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v_es_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v_j_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_es_510_ = lean_ctor_get(v_x_505_, 0);
v___x_511_ = ((size_t)31ULL);
v___x_512_ = lean_usize_land(v_x_506_, v___x_511_);
v_j_513_ = lean_usize_to_nat(v___x_512_);
v___x_514_ = lean_array_get_size(v_es_510_);
v___x_515_ = lean_nat_dec_lt(v_j_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec(v_j_513_);
lean_dec(v_x_509_);
lean_dec_ref(v_x_508_);
return v_x_505_;
}
else
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_556_; 
lean_inc_ref(v_es_510_);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_x_505_, 0);
lean_dec(v_unused_557_);
v___x_517_ = v_x_505_;
v_isShared_518_ = v_isSharedCheck_556_;
goto v_resetjp_516_;
}
else
{
lean_dec(v_x_505_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_556_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_v_519_; lean_object* v___x_520_; lean_object* v_xs_x27_521_; lean_object* v___y_523_; 
v_v_519_ = lean_array_fget(v_es_510_, v_j_513_);
v___x_520_ = lean_box(0);
v_xs_x27_521_ = lean_array_fset(v_es_510_, v_j_513_, v___x_520_);
switch(lean_obj_tag(v_v_519_))
{
case 0:
{
lean_object* v_key_528_; lean_object* v_val_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_541_; 
v_key_528_ = lean_ctor_get(v_v_519_, 0);
v_val_529_ = lean_ctor_get(v_v_519_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_v_519_);
if (v_isSharedCheck_541_ == 0)
{
v___x_531_ = v_v_519_;
v_isShared_532_ = v_isSharedCheck_541_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_val_529_);
lean_inc(v_key_528_);
lean_dec(v_v_519_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_541_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
size_t v___x_533_; size_t v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_ptr_addr(v_x_508_);
v___x_534_ = lean_ptr_addr(v_key_528_);
v___x_535_ = lean_usize_dec_eq(v___x_533_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_del_object(v___x_531_);
v___x_536_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_528_, v_val_529_, v_x_508_, v_x_509_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
v___y_523_ = v___x_537_;
goto v___jp_522_;
}
else
{
lean_object* v___x_539_; 
lean_dec(v_val_529_);
lean_dec(v_key_528_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v_x_509_);
lean_ctor_set(v___x_531_, 0, v_x_508_);
v___x_539_ = v___x_531_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_x_508_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_x_509_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
v___y_523_ = v___x_539_;
goto v___jp_522_;
}
}
}
}
case 1:
{
lean_object* v_node_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_554_; 
v_node_542_ = lean_ctor_get(v_v_519_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_v_519_);
if (v_isSharedCheck_554_ == 0)
{
v___x_544_ = v_v_519_;
v_isShared_545_ = v_isSharedCheck_554_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_node_542_);
lean_dec(v_v_519_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_554_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
size_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_546_ = ((size_t)5ULL);
v___x_547_ = lean_usize_shift_right(v_x_506_, v___x_546_);
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_add(v_x_507_, v___x_548_);
v___x_550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_542_, v___x_547_, v___x_549_, v_x_508_, v_x_509_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_550_);
v___x_552_ = v___x_544_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v___y_523_ = v___x_552_;
goto v___jp_522_;
}
}
}
default: 
{
lean_object* v___x_555_; 
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_x_508_);
lean_ctor_set(v___x_555_, 1, v_x_509_);
v___y_523_ = v___x_555_;
goto v___jp_522_;
}
}
v___jp_522_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_array_fset(v_xs_x27_521_, v_j_513_, v___y_523_);
lean_dec(v_j_513_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_524_);
v___x_526_ = v___x_517_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
else
{
lean_object* v_ks_558_; lean_object* v_vs_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_577_; 
v_ks_558_ = lean_ctor_get(v_x_505_, 0);
v_vs_559_ = lean_ctor_get(v_x_505_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_577_ == 0)
{
v___x_561_ = v_x_505_;
v_isShared_562_ = v_isSharedCheck_577_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_vs_559_);
lean_inc(v_ks_558_);
lean_dec(v_x_505_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_577_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_ks_558_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_vs_559_);
v___x_564_ = v_reuseFailAlloc_576_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v_newNode_565_; size_t v___x_566_; uint8_t v___x_567_; 
v_newNode_565_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v___x_564_, v_x_508_, v_x_509_);
v___x_566_ = ((size_t)7ULL);
v___x_567_ = lean_usize_dec_le(v___x_566_, v_x_507_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_568_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_565_);
v___x_569_ = lean_unsigned_to_nat(4u);
v___x_570_ = lean_nat_dec_lt(v___x_568_, v___x_569_);
lean_dec(v___x_568_);
if (v___x_570_ == 0)
{
lean_object* v_ks_571_; lean_object* v_vs_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_ks_571_ = lean_ctor_get(v_newNode_565_, 0);
lean_inc_ref(v_ks_571_);
v_vs_572_ = lean_ctor_get(v_newNode_565_, 1);
lean_inc_ref(v_vs_572_);
lean_dec_ref(v_newNode_565_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
v___x_575_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_x_507_, v_ks_571_, v_vs_572_, v___x_573_, v___x_574_);
lean_dec_ref(v_vs_572_);
lean_dec_ref(v_ks_571_);
return v___x_575_;
}
else
{
return v_newNode_565_;
}
}
else
{
return v_newNode_565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_578_, lean_object* v_keys_579_, lean_object* v_vals_580_, lean_object* v_i_581_, lean_object* v_entries_582_){
_start:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_array_get_size(v_keys_579_);
v___x_584_ = lean_nat_dec_lt(v_i_581_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec(v_i_581_);
return v_entries_582_;
}
else
{
lean_object* v_k_585_; lean_object* v_v_586_; size_t v___x_587_; size_t v___x_588_; size_t v___x_589_; uint64_t v___x_590_; size_t v_h_591_; size_t v___x_592_; lean_object* v___x_593_; size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; size_t v_h_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_k_585_ = lean_array_fget_borrowed(v_keys_579_, v_i_581_);
v_v_586_ = lean_array_fget_borrowed(v_vals_580_, v_i_581_);
v___x_587_ = lean_ptr_addr(v_k_585_);
v___x_588_ = ((size_t)3ULL);
v___x_589_ = lean_usize_shift_right(v___x_587_, v___x_588_);
v___x_590_ = lean_usize_to_uint64(v___x_589_);
v_h_591_ = lean_uint64_to_usize(v___x_590_);
v___x_592_ = ((size_t)5ULL);
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_sub(v_depth_578_, v___x_594_);
v___x_596_ = lean_usize_mul(v___x_592_, v___x_595_);
v_h_597_ = lean_usize_shift_right(v_h_591_, v___x_596_);
v___x_598_ = lean_nat_add(v_i_581_, v___x_593_);
lean_dec(v_i_581_);
lean_inc(v_v_586_);
lean_inc(v_k_585_);
v___x_599_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_582_, v_h_597_, v_depth_578_, v_k_585_, v_v_586_);
v_i_581_ = v___x_598_;
v_entries_582_ = v___x_599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_601_, lean_object* v_keys_602_, lean_object* v_vals_603_, lean_object* v_i_604_, lean_object* v_entries_605_){
_start:
{
size_t v_depth_boxed_606_; lean_object* v_res_607_; 
v_depth_boxed_606_ = lean_unbox_usize(v_depth_601_);
lean_dec(v_depth_601_);
v_res_607_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_606_, v_keys_602_, v_vals_603_, v_i_604_, v_entries_605_);
lean_dec_ref(v_vals_603_);
lean_dec_ref(v_keys_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
size_t v_x_109973__boxed_613_; size_t v_x_109974__boxed_614_; lean_object* v_res_615_; 
v_x_109973__boxed_613_ = lean_unbox_usize(v_x_609_);
lean_dec(v_x_609_);
v_x_109974__boxed_614_ = lean_unbox_usize(v_x_610_);
lean_dec(v_x_610_);
v_res_615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_608_, v_x_109973__boxed_613_, v_x_109974__boxed_614_, v_x_611_, v_x_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; uint64_t v___x_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v___x_619_ = lean_ptr_addr(v_x_617_);
v___x_620_ = ((size_t)3ULL);
v___x_621_ = lean_usize_shift_right(v___x_619_, v___x_620_);
v___x_622_ = lean_usize_to_uint64(v___x_621_);
v___x_623_ = lean_uint64_to_usize(v___x_622_);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_616_, v___x_623_, v___x_624_, v_x_617_, v_x_618_);
return v___x_625_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_626_; double v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_float_of_nat(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* v_cls_631_, lean_object* v_msg_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_ref_638_; lean_object* v___x_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_685_; 
v_ref_638_ = lean_ctor_get(v___y_635_, 2);
v___x_639_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_685_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_685_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_685_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v_traceState_645_; lean_object* v_env_646_; lean_object* v_nextMacroScope_647_; lean_object* v_ngen_648_; lean_object* v_auxDeclNGen_649_; lean_object* v_cache_650_; lean_object* v_recordedDeps_651_; lean_object* v_messages_652_; lean_object* v_infoState_653_; lean_object* v_snapshotTasks_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_684_; 
v___x_644_ = lean_st_ref_take(v___y_636_);
v_traceState_645_ = lean_ctor_get(v___x_644_, 4);
v_env_646_ = lean_ctor_get(v___x_644_, 0);
v_nextMacroScope_647_ = lean_ctor_get(v___x_644_, 1);
v_ngen_648_ = lean_ctor_get(v___x_644_, 2);
v_auxDeclNGen_649_ = lean_ctor_get(v___x_644_, 3);
v_cache_650_ = lean_ctor_get(v___x_644_, 5);
v_recordedDeps_651_ = lean_ctor_get(v___x_644_, 6);
v_messages_652_ = lean_ctor_get(v___x_644_, 7);
v_infoState_653_ = lean_ctor_get(v___x_644_, 8);
v_snapshotTasks_654_ = lean_ctor_get(v___x_644_, 9);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_684_ == 0)
{
v___x_656_ = v___x_644_;
v_isShared_657_ = v_isSharedCheck_684_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snapshotTasks_654_);
lean_inc(v_infoState_653_);
lean_inc(v_messages_652_);
lean_inc(v_recordedDeps_651_);
lean_inc(v_cache_650_);
lean_inc(v_traceState_645_);
lean_inc(v_auxDeclNGen_649_);
lean_inc(v_ngen_648_);
lean_inc(v_nextMacroScope_647_);
lean_inc(v_env_646_);
lean_dec(v___x_644_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_684_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint64_t v_tid_658_; lean_object* v_traces_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_683_; 
v_tid_658_ = lean_ctor_get_uint64(v_traceState_645_, sizeof(void*)*1);
v_traces_659_ = lean_ctor_get(v_traceState_645_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v_traceState_645_);
if (v_isSharedCheck_683_ == 0)
{
v___x_661_ = v_traceState_645_;
v_isShared_662_ = v_isSharedCheck_683_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_traces_659_);
lean_dec(v_traceState_645_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_683_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; double v___x_665_; uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_box(0);
v___x_665_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0);
v___x_666_ = 0;
v___x_667_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1));
v___x_668_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_668_, 0, v_cls_631_);
lean_ctor_set(v___x_668_, 1, v___x_664_);
lean_ctor_set(v___x_668_, 2, v___x_667_);
lean_ctor_set_float(v___x_668_, sizeof(void*)*3, v___x_665_);
lean_ctor_set_float(v___x_668_, sizeof(void*)*3 + 8, v___x_665_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*3 + 16, v___x_666_);
v___x_669_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2));
v___x_670_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v_a_640_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
lean_inc(v_ref_638_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_ref_638_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_PersistentArray_push___redArg(v_traces_659_, v___x_671_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_672_);
v___x_674_ = v___x_661_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_672_);
lean_ctor_set_uint64(v_reuseFailAlloc_682_, sizeof(void*)*1, v_tid_658_);
v___x_674_ = v_reuseFailAlloc_682_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v___x_674_);
v___x_676_ = v___x_656_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_env_646_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_nextMacroScope_647_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_ngen_648_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_auxDeclNGen_649_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v_cache_650_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_recordedDeps_651_);
lean_ctor_set(v_reuseFailAlloc_681_, 7, v_messages_652_);
lean_ctor_set(v_reuseFailAlloc_681_, 8, v_infoState_653_);
lean_ctor_set(v_reuseFailAlloc_681_, 9, v_snapshotTasks_654_);
v___x_676_ = v_reuseFailAlloc_681_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_st_ref_put(v___y_636_, v___x_676_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_663_);
v___x_679_ = v___x_642_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_663_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* v_cls_686_, lean_object* v_msg_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_686_, v_msg_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_694_, lean_object* v_vals_695_, lean_object* v_i_696_, lean_object* v_k_697_){
_start:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_array_get_size(v_keys_694_);
v___x_699_ = lean_nat_dec_lt(v_i_696_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v_i_696_);
v___x_700_ = lean_box(0);
return v___x_700_;
}
else
{
lean_object* v_k_x27_701_; size_t v___x_702_; size_t v___x_703_; uint8_t v___x_704_; 
v_k_x27_701_ = lean_array_fget_borrowed(v_keys_694_, v_i_696_);
v___x_702_ = lean_ptr_addr(v_k_697_);
v___x_703_ = lean_ptr_addr(v_k_x27_701_);
v___x_704_ = lean_usize_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_add(v_i_696_, v___x_705_);
lean_dec(v_i_696_);
v_i_696_ = v___x_706_;
goto _start;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_array_fget_borrowed(v_vals_695_, v_i_696_);
lean_dec(v_i_696_);
lean_inc(v___x_708_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_710_, lean_object* v_vals_711_, lean_object* v_i_712_, lean_object* v_k_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_710_, v_vals_711_, v_i_712_, v_k_713_);
lean_dec_ref(v_k_713_);
lean_dec_ref(v_vals_711_);
lean_dec_ref(v_keys_710_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* v_x_715_, size_t v_x_716_, lean_object* v_x_717_){
_start:
{
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v_es_718_; lean_object* v___x_719_; size_t v___x_720_; size_t v___x_721_; lean_object* v_j_722_; lean_object* v___x_723_; 
v_es_718_ = lean_ctor_get(v_x_715_, 0);
v___x_719_ = lean_box(2);
v___x_720_ = ((size_t)31ULL);
v___x_721_ = lean_usize_land(v_x_716_, v___x_720_);
v_j_722_ = lean_usize_to_nat(v___x_721_);
v___x_723_ = lean_array_get_borrowed(v___x_719_, v_es_718_, v_j_722_);
lean_dec(v_j_722_);
switch(lean_obj_tag(v___x_723_))
{
case 0:
{
lean_object* v_key_724_; lean_object* v_val_725_; size_t v___x_726_; size_t v___x_727_; uint8_t v___x_728_; 
v_key_724_ = lean_ctor_get(v___x_723_, 0);
v_val_725_ = lean_ctor_get(v___x_723_, 1);
v___x_726_ = lean_ptr_addr(v_x_717_);
v___x_727_ = lean_ptr_addr(v_key_724_);
v___x_728_ = lean_usize_dec_eq(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
v___x_729_ = lean_box(0);
return v___x_729_;
}
else
{
lean_object* v___x_730_; 
lean_inc(v_val_725_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_val_725_);
return v___x_730_;
}
}
case 1:
{
lean_object* v_node_731_; size_t v___x_732_; size_t v___x_733_; 
v_node_731_ = lean_ctor_get(v___x_723_, 0);
v___x_732_ = ((size_t)5ULL);
v___x_733_ = lean_usize_shift_right(v_x_716_, v___x_732_);
v_x_715_ = v_node_731_;
v_x_716_ = v___x_733_;
goto _start;
}
default: 
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(0);
return v___x_735_;
}
}
}
else
{
lean_object* v_ks_736_; lean_object* v_vs_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_ks_736_ = lean_ctor_get(v_x_715_, 0);
v_vs_737_ = lean_ctor_get(v_x_715_, 1);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_ks_736_, v_vs_737_, v___x_738_, v_x_717_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
size_t v_x_110275__boxed_743_; lean_object* v_res_744_; 
v_x_110275__boxed_743_ = lean_unbox_usize(v_x_741_);
lean_dec(v_x_741_);
v_res_744_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_740_, v_x_110275__boxed_743_, v_x_742_);
lean_dec_ref(v_x_742_);
lean_dec_ref(v_x_740_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; uint64_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_747_ = lean_ptr_addr(v_x_746_);
v___x_748_ = ((size_t)3ULL);
v___x_749_ = lean_usize_shift_right(v___x_747_, v___x_748_);
v___x_750_ = lean_usize_to_uint64(v___x_749_);
v___x_751_ = lean_uint64_to_usize(v___x_750_);
v___x_752_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_745_, v___x_751_, v_x_746_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_753_, v_x_754_);
lean_dec_ref(v_x_754_);
lean_dec_ref(v_x_753_);
return v_res_755_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1));
v___x_761_ = l_Lean_Name_append(v___x_760_, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* lean_sym_simp(lean_object* v_e_u2081_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___y_783_; lean_object* v___y_784_; uint8_t v___y_785_; lean_object* v___y_817_; lean_object* v___y_818_; uint8_t v___y_819_; lean_object* v___y_820_; uint8_t v___y_821_; uint8_t v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; uint8_t v___y_828_; lean_object* v_e_u2082_831_; lean_object* v_h_u2081_832_; uint8_t v_cd_u2081_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; uint8_t v___y_951_; lean_object* v___y_954_; lean_object* v___y_955_; uint8_t v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; uint8_t v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; uint8_t v___y_966_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; uint8_t v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; uint8_t v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v_a_979_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; uint8_t v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; uint8_t v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_997_; lean_object* v___y_998_; uint8_t v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; uint8_t v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; uint8_t v___y_1009_; lean_object* v___y_1012_; lean_object* v___y_1013_; uint8_t v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; uint8_t v___y_1017_; lean_object* v___y_1018_; uint8_t v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; uint8_t v___y_1026_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; lean_object* v___y_1037_; uint8_t v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; uint8_t v___y_1043_; lean_object* v_toCold_1045_; lean_object* v_currRecDepth_1046_; lean_object* v_ref_1047_; uint16_t v_optionFlags_1048_; uint8_t v_suppressElabErrors_1049_; uint8_t v_isRecordingDeps_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1349_; 
v_toCold_1045_ = lean_ctor_get(v_a_779_, 0);
v_currRecDepth_1046_ = lean_ctor_get(v_a_779_, 1);
v_ref_1047_ = lean_ctor_get(v_a_779_, 2);
v_optionFlags_1048_ = lean_ctor_get_uint16(v_a_779_, sizeof(void*)*3);
v_suppressElabErrors_1049_ = lean_ctor_get_uint8(v_a_779_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1050_ = lean_ctor_get_uint8(v_a_779_, sizeof(void*)*3 + 3);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1052_ = v_a_779_;
v_isShared_1053_ = v_isSharedCheck_1349_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_ref_1047_);
lean_inc(v_currRecDepth_1046_);
lean_inc(v_toCold_1045_);
lean_dec(v_a_779_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1349_;
goto v_resetjp_1051_;
}
v___jp_782_:
{
if (v___y_785_ == 0)
{
lean_object* v___x_786_; lean_object* v_numSteps_787_; lean_object* v_persistentCache_788_; lean_object* v_transientCache_789_; lean_object* v_funext_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_800_; 
v___x_786_ = lean_st_ref_take(v___y_784_);
v_numSteps_787_ = lean_ctor_get(v___x_786_, 0);
v_persistentCache_788_ = lean_ctor_get(v___x_786_, 1);
v_transientCache_789_ = lean_ctor_get(v___x_786_, 2);
v_funext_790_ = lean_ctor_get(v___x_786_, 3);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_800_ == 0)
{
v___x_792_ = v___x_786_;
v_isShared_793_ = v_isSharedCheck_800_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_funext_790_);
lean_inc(v_transientCache_789_);
lean_inc(v_persistentCache_788_);
lean_inc(v_numSteps_787_);
lean_dec(v___x_786_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_800_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
lean_inc_ref(v___y_783_);
v___x_794_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_788_, v_e_u2081_771_, v___y_783_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_794_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_numSteps_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_transientCache_789_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_funext_790_);
v___x_796_ = v_reuseFailAlloc_799_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_st_ref_put(v___y_784_, v___x_796_);
lean_dec(v___y_784_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___y_783_);
return v___x_798_;
}
}
}
else
{
lean_object* v___x_801_; lean_object* v_numSteps_802_; lean_object* v_persistentCache_803_; lean_object* v_transientCache_804_; lean_object* v_funext_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
v___x_801_ = lean_st_ref_take(v___y_784_);
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
lean_inc_ref(v___y_783_);
v___x_809_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_804_, v_e_u2081_771_, v___y_783_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 2, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_numSteps_802_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_persistentCache_803_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_funext_805_);
v___x_811_ = v_reuseFailAlloc_814_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_st_ref_put(v___y_784_, v___x_811_);
lean_dec(v___y_784_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___y_783_);
return v___x_813_;
}
}
}
}
v___jp_816_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_822_, 0, v___y_818_);
lean_ctor_set(v___x_822_, 1, v___y_817_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*2, v___y_819_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*2 + 1, v___y_821_);
v___y_783_ = v___x_822_;
v___y_784_ = v___y_820_;
v___y_785_ = v___y_821_;
goto v___jp_782_;
}
v___jp_823_:
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_829_, 0, v___y_827_);
lean_ctor_set(v___x_829_, 1, v___y_826_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*2, v___y_824_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*2 + 1, v___y_828_);
v___y_783_ = v___x_829_;
v___y_784_ = v___y_825_;
v___y_785_ = v___y_828_;
goto v___jp_782_;
}
v___jp_830_:
{
lean_object* v___x_843_; 
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v_e_u2082_831_);
v___x_843_ = lean_sym_simp(v_e_u2082_831_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
if (lean_obj_tag(v_a_844_) == 0)
{
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
if (v_cd_u2081_833_ == 0)
{
uint8_t v_done_845_; uint8_t v_contextDependent_846_; 
v_done_845_ = lean_ctor_get_uint8(v_a_844_, 0);
v_contextDependent_846_ = lean_ctor_get_uint8(v_a_844_, 1);
lean_dec_ref_known(v_a_844_, 0);
v___y_817_ = v_h_u2081_832_;
v___y_818_ = v_e_u2082_831_;
v___y_819_ = v_done_845_;
v___y_820_ = v___y_836_;
v___y_821_ = v_contextDependent_846_;
goto v___jp_816_;
}
else
{
uint8_t v_done_847_; 
v_done_847_ = lean_ctor_get_uint8(v_a_844_, 0);
lean_dec_ref_known(v_a_844_, 0);
v___y_817_ = v_h_u2081_832_;
v___y_818_ = v_e_u2082_831_;
v___y_819_ = v_done_847_;
v___y_820_ = v___y_836_;
v___y_821_ = v_cd_u2081_833_;
goto v___jp_816_;
}
}
else
{
lean_object* v_e_x27_848_; lean_object* v_proof_849_; uint8_t v_done_850_; uint8_t v_contextDependent_851_; lean_object* v___x_852_; 
v_e_x27_848_ = lean_ctor_get(v_a_844_, 0);
lean_inc_ref_n(v_e_x27_848_, 2);
v_proof_849_ = lean_ctor_get(v_a_844_, 1);
lean_inc_ref(v_proof_849_);
v_done_850_ = lean_ctor_get_uint8(v_a_844_, sizeof(void*)*2);
v_contextDependent_851_ = lean_ctor_get_uint8(v_a_844_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_844_, 2);
lean_inc_ref(v_e_u2081_771_);
v___x_852_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_771_, v_e_u2082_831_, v_h_u2081_832_, v_e_x27_848_, v_proof_849_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
if (lean_obj_tag(v___x_852_) == 0)
{
if (v_cd_u2081_833_ == 0)
{
lean_object* v_a_853_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___y_824_ = v_done_850_;
v___y_825_ = v___y_836_;
v___y_826_ = v_a_853_;
v___y_827_ = v_e_x27_848_;
v___y_828_ = v_contextDependent_851_;
goto v___jp_823_;
}
else
{
lean_object* v_a_854_; 
v_a_854_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_852_, 1);
v___y_824_ = v_done_850_;
v___y_825_ = v___y_836_;
v___y_826_ = v_a_854_;
v___y_827_ = v_e_x27_848_;
v___y_828_ = v_cd_u2081_833_;
goto v___jp_823_;
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_e_x27_848_);
lean_dec(v___y_836_);
lean_dec_ref(v_e_u2081_771_);
v_a_855_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_852_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_852_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
else
{
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v_h_u2081_832_);
lean_dec_ref(v_e_u2082_831_);
lean_dec_ref(v_e_u2081_771_);
return v___x_843_;
}
}
v___jp_863_:
{
if (lean_obj_tag(v___y_873_) == 0)
{
uint8_t v_contextDependent_874_; 
lean_dec_ref(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
v_contextDependent_874_ = lean_ctor_get_uint8(v___y_873_, 1);
if (v_contextDependent_874_ == 0)
{
lean_object* v___x_875_; lean_object* v_numSteps_876_; lean_object* v_persistentCache_877_; lean_object* v_transientCache_878_; lean_object* v_funext_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_889_; 
v___x_875_ = lean_st_ref_take(v___y_864_);
v_numSteps_876_ = lean_ctor_get(v___x_875_, 0);
v_persistentCache_877_ = lean_ctor_get(v___x_875_, 1);
v_transientCache_878_ = lean_ctor_get(v___x_875_, 2);
v_funext_879_ = lean_ctor_get(v___x_875_, 3);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_889_ == 0)
{
v___x_881_ = v___x_875_;
v_isShared_882_ = v_isSharedCheck_889_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_funext_879_);
lean_inc(v_transientCache_878_);
lean_inc(v_persistentCache_877_);
lean_inc(v_numSteps_876_);
lean_dec(v___x_875_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_889_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
lean_inc_ref(v___y_873_);
v___x_883_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_877_, v_e_u2081_771_, v___y_873_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v___x_883_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_numSteps_876_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_transientCache_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_funext_879_);
v___x_885_ = v_reuseFailAlloc_888_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_st_ref_put(v___y_864_, v___x_885_);
lean_dec(v___y_864_);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___y_873_);
return v___x_887_;
}
}
}
else
{
lean_object* v___x_890_; lean_object* v_numSteps_891_; lean_object* v_persistentCache_892_; lean_object* v_transientCache_893_; lean_object* v_funext_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_904_; 
v___x_890_ = lean_st_ref_take(v___y_864_);
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
lean_inc_ref(v___y_873_);
v___x_898_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_893_, v_e_u2081_771_, v___y_873_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v___x_898_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_numSteps_891_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_persistentCache_892_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_funext_894_);
v___x_900_ = v_reuseFailAlloc_903_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_st_ref_put(v___y_864_, v___x_900_);
lean_dec(v___y_864_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___y_873_);
return v___x_902_;
}
}
}
}
else
{
uint8_t v_done_905_; 
v_done_905_ = lean_ctor_get_uint8(v___y_873_, sizeof(void*)*2);
if (v_done_905_ == 0)
{
lean_object* v_e_x27_906_; lean_object* v_proof_907_; uint8_t v_contextDependent_908_; 
v_e_x27_906_ = lean_ctor_get(v___y_873_, 0);
lean_inc_ref(v_e_x27_906_);
v_proof_907_ = lean_ctor_get(v___y_873_, 1);
lean_inc_ref(v_proof_907_);
v_contextDependent_908_ = lean_ctor_get_uint8(v___y_873_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v___y_873_, 2);
v_e_u2082_831_ = v_e_x27_906_;
v_h_u2081_832_ = v_proof_907_;
v_cd_u2081_833_ = v_contextDependent_908_;
v___y_834_ = v___y_868_;
v___y_835_ = v___y_867_;
v___y_836_ = v___y_864_;
v___y_837_ = v___y_871_;
v___y_838_ = v___y_870_;
v___y_839_ = v___y_866_;
v___y_840_ = v___y_869_;
v___y_841_ = v___y_872_;
v___y_842_ = v___y_865_;
goto v___jp_830_;
}
else
{
uint8_t v_contextDependent_909_; 
lean_dec_ref(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
v_contextDependent_909_ = lean_ctor_get_uint8(v___y_873_, sizeof(void*)*2 + 1);
if (v_contextDependent_909_ == 0)
{
lean_object* v___x_910_; lean_object* v_numSteps_911_; lean_object* v_persistentCache_912_; lean_object* v_transientCache_913_; lean_object* v_funext_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_924_; 
v___x_910_ = lean_st_ref_take(v___y_864_);
v_numSteps_911_ = lean_ctor_get(v___x_910_, 0);
v_persistentCache_912_ = lean_ctor_get(v___x_910_, 1);
v_transientCache_913_ = lean_ctor_get(v___x_910_, 2);
v_funext_914_ = lean_ctor_get(v___x_910_, 3);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_924_ == 0)
{
v___x_916_ = v___x_910_;
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_funext_914_);
lean_inc(v_transientCache_913_);
lean_inc(v_persistentCache_912_);
lean_inc(v_numSteps_911_);
lean_dec(v___x_910_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
lean_inc_ref(v___y_873_);
v___x_918_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_912_, v_e_u2081_771_, v___y_873_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_numSteps_911_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_transientCache_913_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_funext_914_);
v___x_920_ = v_reuseFailAlloc_923_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_st_ref_put(v___y_864_, v___x_920_);
lean_dec(v___y_864_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___y_873_);
return v___x_922_;
}
}
}
else
{
lean_object* v___x_925_; lean_object* v_numSteps_926_; lean_object* v_persistentCache_927_; lean_object* v_transientCache_928_; lean_object* v_funext_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_939_; 
v___x_925_ = lean_st_ref_take(v___y_864_);
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
lean_inc_ref(v___y_873_);
v___x_933_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_928_, v_e_u2081_771_, v___y_873_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v___x_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_numSteps_926_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_persistentCache_927_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_funext_929_);
v___x_935_ = v_reuseFailAlloc_938_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_st_ref_put(v___y_864_, v___x_935_);
lean_dec(v___y_864_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___y_873_);
return v___x_937_;
}
}
}
}
}
}
v___jp_940_:
{
if (v___y_951_ == 0)
{
v___y_864_ = v___y_941_;
v___y_865_ = v___y_942_;
v___y_866_ = v___y_943_;
v___y_867_ = v___y_945_;
v___y_868_ = v___y_944_;
v___y_869_ = v___y_946_;
v___y_870_ = v___y_948_;
v___y_871_ = v___y_947_;
v___y_872_ = v___y_950_;
v___y_873_ = v___y_949_;
goto v___jp_863_;
}
else
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_949_);
v___y_864_ = v___y_941_;
v___y_865_ = v___y_942_;
v___y_866_ = v___y_943_;
v___y_867_ = v___y_945_;
v___y_868_ = v___y_944_;
v___y_869_ = v___y_946_;
v___y_870_ = v___y_948_;
v___y_871_ = v___y_947_;
v___y_872_ = v___y_950_;
v___y_873_ = v___x_952_;
goto v___jp_863_;
}
}
v___jp_953_:
{
if (v___y_966_ == 0)
{
v___y_941_ = v___y_954_;
v___y_942_ = v___y_962_;
v___y_943_ = v___y_955_;
v___y_944_ = v___y_957_;
v___y_945_ = v___y_963_;
v___y_946_ = v___y_958_;
v___y_947_ = v___y_959_;
v___y_948_ = v___y_964_;
v___y_949_ = v___y_960_;
v___y_950_ = v___y_965_;
v___y_951_ = v___y_956_;
goto v___jp_940_;
}
else
{
v___y_941_ = v___y_954_;
v___y_942_ = v___y_962_;
v___y_943_ = v___y_955_;
v___y_944_ = v___y_957_;
v___y_945_ = v___y_963_;
v___y_946_ = v___y_958_;
v___y_947_ = v___y_959_;
v___y_948_ = v___y_964_;
v___y_949_ = v___y_960_;
v___y_950_ = v___y_965_;
v___y_951_ = v___y_961_;
goto v___jp_940_;
}
}
v___jp_967_:
{
if (v___y_971_ == 0)
{
v___y_864_ = v___y_968_;
v___y_865_ = v___y_969_;
v___y_866_ = v___y_970_;
v___y_867_ = v___y_973_;
v___y_868_ = v___y_972_;
v___y_869_ = v___y_974_;
v___y_870_ = v___y_977_;
v___y_871_ = v___y_976_;
v___y_872_ = v___y_978_;
v___y_873_ = v_a_979_;
goto v___jp_863_;
}
else
{
if (lean_obj_tag(v_a_979_) == 0)
{
uint8_t v_contextDependent_980_; 
v_contextDependent_980_ = lean_ctor_get_uint8(v_a_979_, 1);
v___y_954_ = v___y_968_;
v___y_955_ = v___y_970_;
v___y_956_ = v___y_971_;
v___y_957_ = v___y_972_;
v___y_958_ = v___y_974_;
v___y_959_ = v___y_976_;
v___y_960_ = v_a_979_;
v___y_961_ = v___y_975_;
v___y_962_ = v___y_969_;
v___y_963_ = v___y_973_;
v___y_964_ = v___y_977_;
v___y_965_ = v___y_978_;
v___y_966_ = v_contextDependent_980_;
goto v___jp_953_;
}
else
{
uint8_t v_contextDependent_981_; 
v_contextDependent_981_ = lean_ctor_get_uint8(v_a_979_, sizeof(void*)*2 + 1);
v___y_954_ = v___y_968_;
v___y_955_ = v___y_970_;
v___y_956_ = v___y_971_;
v___y_957_ = v___y_972_;
v___y_958_ = v___y_974_;
v___y_959_ = v___y_976_;
v___y_960_ = v_a_979_;
v___y_961_ = v___y_975_;
v___y_962_ = v___y_969_;
v___y_963_ = v___y_973_;
v___y_964_ = v___y_977_;
v___y_965_ = v___y_978_;
v___y_966_ = v_contextDependent_981_;
goto v___jp_953_;
}
}
}
v___jp_982_:
{
if (lean_obj_tag(v___y_994_) == 0)
{
lean_object* v_a_995_; 
v_a_995_ = lean_ctor_get(v___y_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___y_994_, 1);
v___y_968_ = v___y_983_;
v___y_969_ = v___y_984_;
v___y_970_ = v___y_985_;
v___y_971_ = v___y_986_;
v___y_972_ = v___y_988_;
v___y_973_ = v___y_987_;
v___y_974_ = v___y_989_;
v___y_975_ = v___y_992_;
v___y_976_ = v___y_991_;
v___y_977_ = v___y_990_;
v___y_978_ = v___y_993_;
v_a_979_ = v_a_995_;
goto v___jp_967_;
}
else
{
lean_dec_ref(v___y_993_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v_e_u2081_771_);
return v___y_994_;
}
}
v___jp_996_:
{
if (v___y_1009_ == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1002_);
v___y_968_ = v___y_997_;
v___y_969_ = v___y_1005_;
v___y_970_ = v___y_998_;
v___y_971_ = v___y_999_;
v___y_972_ = v___y_1000_;
v___y_973_ = v___y_1006_;
v___y_974_ = v___y_1001_;
v___y_975_ = v___y_1003_;
v___y_976_ = v___y_1004_;
v___y_977_ = v___y_1007_;
v___y_978_ = v___y_1008_;
v_a_979_ = v___x_1010_;
goto v___jp_967_;
}
else
{
v___y_968_ = v___y_997_;
v___y_969_ = v___y_1005_;
v___y_970_ = v___y_998_;
v___y_971_ = v___y_999_;
v___y_972_ = v___y_1000_;
v___y_973_ = v___y_1006_;
v___y_974_ = v___y_1001_;
v___y_975_ = v___y_1003_;
v___y_976_ = v___y_1004_;
v___y_977_ = v___y_1007_;
v___y_978_ = v___y_1008_;
v_a_979_ = v___y_1002_;
goto v___jp_967_;
}
}
v___jp_1011_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1027_, 0, v___y_1022_);
lean_ctor_set(v___x_1027_, 1, v___y_1025_);
lean_ctor_set_uint8(v___x_1027_, sizeof(void*)*2, v___y_1019_);
lean_ctor_set_uint8(v___x_1027_, sizeof(void*)*2 + 1, v___y_1026_);
v___y_968_ = v___y_1012_;
v___y_969_ = v___y_1020_;
v___y_970_ = v___y_1013_;
v___y_971_ = v___y_1014_;
v___y_972_ = v___y_1015_;
v___y_973_ = v___y_1021_;
v___y_974_ = v___y_1016_;
v___y_975_ = v___y_1017_;
v___y_976_ = v___y_1018_;
v___y_977_ = v___y_1023_;
v___y_978_ = v___y_1024_;
v_a_979_ = v___x_1027_;
goto v___jp_967_;
}
v___jp_1028_:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1044_, 0, v___y_1030_);
lean_ctor_set(v___x_1044_, 1, v___y_1035_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*2, v___y_1038_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*2 + 1, v___y_1043_);
v___y_968_ = v___y_1029_;
v___y_969_ = v___y_1039_;
v___y_970_ = v___y_1031_;
v___y_971_ = v___y_1032_;
v___y_972_ = v___y_1033_;
v___y_973_ = v___y_1040_;
v___y_974_ = v___y_1034_;
v___y_975_ = v___y_1036_;
v___y_976_ = v___y_1037_;
v___y_977_ = v___y_1041_;
v___y_978_ = v___y_1042_;
v_a_979_ = v___x_1044_;
goto v___jp_967_;
}
v_resetjp_1051_:
{
lean_object* v_maxRecDepth_1054_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_maxRecDepth_1054_ = lean_ctor_get(v_toCold_1045_, 3);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_nat_dec_eq(v_maxRecDepth_1054_, v___x_1345_);
if (v___x_1346_ == 0)
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_eq(v_currRecDepth_1046_, v_maxRecDepth_1054_);
if (v___x_1347_ == 0)
{
goto v___jp_1315_;
}
else
{
lean_object* v___x_1348_; 
lean_del_object(v___x_1052_);
lean_dec(v_currRecDepth_1046_);
lean_dec_ref(v_toCold_1045_);
lean_dec(v_a_780_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_e_u2081_771_);
v___x_1348_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_1047_);
return v___x_1348_;
}
}
else
{
goto v___jp_1315_;
}
v___jp_1055_:
{
lean_object* v___x_1066_; lean_object* v_persistentCache_1067_; lean_object* v_transientCache_1068_; lean_object* v_funext_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1194_; 
v___x_1066_ = lean_st_ref_take(v___y_1059_);
v_persistentCache_1067_ = lean_ctor_get(v___x_1066_, 1);
v_transientCache_1068_ = lean_ctor_get(v___x_1066_, 2);
v_funext_1069_ = lean_ctor_get(v___x_1066_, 3);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v___x_1066_, 0);
lean_dec(v_unused_1195_);
v___x_1071_ = v___x_1066_;
v_isShared_1072_ = v_isSharedCheck_1194_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_funext_1069_);
lean_inc(v_transientCache_1068_);
lean_inc(v_persistentCache_1067_);
lean_dec(v___x_1066_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1194_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___y_1056_);
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___y_1056_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_persistentCache_1067_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_transientCache_1068_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_funext_1069_);
v___x_1074_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v_pre_1076_; lean_object* v___x_1077_; 
v___x_1075_ = lean_st_ref_put(v___y_1059_, v___x_1074_);
v_pre_1076_ = lean_ctor_get(v___y_1057_, 0);
lean_inc_ref(v_pre_1076_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
lean_inc(v___y_1063_);
lean_inc_ref(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v___y_1057_);
lean_inc_ref(v_e_u2081_771_);
v___x_1077_ = lean_apply_11(v_pre_1076_, v_e_u2081_771_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, lean_box(0));
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1192_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1192_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1192_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
if (lean_obj_tag(v_a_1078_) == 0)
{
uint8_t v_done_1082_; 
v_done_1082_ = lean_ctor_get_uint8(v_a_1078_, 0);
if (v_done_1082_ == 0)
{
uint8_t v_contextDependent_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_del_object(v___x_1080_);
v_contextDependent_1083_ = lean_ctor_get_uint8(v_a_1078_, 1);
lean_dec_ref_known(v_a_1078_, 0);
v___x_1084_ = lean_box(0);
lean_inc_ref(v_e_u2081_771_);
v___x_1085_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_u2081_771_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
if (lean_obj_tag(v_a_1086_) == 0)
{
uint8_t v_done_1087_; 
v_done_1087_ = lean_ctor_get_uint8(v_a_1086_, 0);
if (v_done_1087_ == 0)
{
uint8_t v_contextDependent_1088_; lean_object* v___x_1089_; 
lean_inc_ref(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v_contextDependent_1088_ = lean_ctor_get_uint8(v_a_1086_, 1);
lean_dec_ref_known(v_a_1086_, 0);
lean_inc_ref(v_e_u2081_771_);
v___x_1089_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1084_, v_e_u2081_771_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1089_) == 0)
{
if (v_contextDependent_1088_ == 0)
{
lean_object* v_a_1090_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___y_968_ = v___y_1059_;
v___y_969_ = v___y_1065_;
v___y_970_ = v___y_1062_;
v___y_971_ = v_contextDependent_1083_;
v___y_972_ = v___y_1057_;
v___y_973_ = v___y_1058_;
v___y_974_ = v___y_1063_;
v___y_975_ = v_done_1082_;
v___y_976_ = v___y_1060_;
v___y_977_ = v___y_1061_;
v___y_978_ = v___y_1064_;
v_a_979_ = v_a_1090_;
goto v___jp_967_;
}
else
{
lean_object* v_a_1091_; 
v_a_1091_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1089_, 1);
if (lean_obj_tag(v_a_1091_) == 0)
{
uint8_t v_contextDependent_1092_; 
v_contextDependent_1092_ = lean_ctor_get_uint8(v_a_1091_, 1);
v___y_997_ = v___y_1059_;
v___y_998_ = v___y_1062_;
v___y_999_ = v_contextDependent_1083_;
v___y_1000_ = v___y_1057_;
v___y_1001_ = v___y_1063_;
v___y_1002_ = v_a_1091_;
v___y_1003_ = v_done_1082_;
v___y_1004_ = v___y_1060_;
v___y_1005_ = v___y_1065_;
v___y_1006_ = v___y_1058_;
v___y_1007_ = v___y_1061_;
v___y_1008_ = v___y_1064_;
v___y_1009_ = v_contextDependent_1092_;
goto v___jp_996_;
}
else
{
uint8_t v_contextDependent_1093_; 
v_contextDependent_1093_ = lean_ctor_get_uint8(v_a_1091_, sizeof(void*)*2 + 1);
v___y_997_ = v___y_1059_;
v___y_998_ = v___y_1062_;
v___y_999_ = v_contextDependent_1083_;
v___y_1000_ = v___y_1057_;
v___y_1001_ = v___y_1063_;
v___y_1002_ = v_a_1091_;
v___y_1003_ = v_done_1082_;
v___y_1004_ = v___y_1060_;
v___y_1005_ = v___y_1065_;
v___y_1006_ = v___y_1058_;
v___y_1007_ = v___y_1061_;
v___y_1008_ = v___y_1064_;
v___y_1009_ = v_contextDependent_1093_;
goto v___jp_996_;
}
}
}
else
{
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v_e_u2081_771_);
return v___x_1089_;
}
}
else
{
v___y_983_ = v___y_1059_;
v___y_984_ = v___y_1065_;
v___y_985_ = v___y_1062_;
v___y_986_ = v_contextDependent_1083_;
v___y_987_ = v___y_1058_;
v___y_988_ = v___y_1057_;
v___y_989_ = v___y_1063_;
v___y_990_ = v___y_1061_;
v___y_991_ = v___y_1060_;
v___y_992_ = v_done_1082_;
v___y_993_ = v___y_1064_;
v___y_994_ = v___x_1085_;
goto v___jp_982_;
}
}
else
{
uint8_t v_done_1094_; 
v_done_1094_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*2);
if (v_done_1094_ == 0)
{
lean_object* v_e_x27_1095_; lean_object* v_proof_1096_; uint8_t v_contextDependent_1097_; lean_object* v___x_1098_; 
lean_inc_ref(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v_e_x27_1095_ = lean_ctor_get(v_a_1086_, 0);
lean_inc_ref_n(v_e_x27_1095_, 2);
v_proof_1096_ = lean_ctor_get(v_a_1086_, 1);
lean_inc_ref(v_proof_1096_);
v_contextDependent_1097_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1086_, 2);
v___x_1098_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1084_, v_e_x27_1095_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
if (lean_obj_tag(v_a_1099_) == 0)
{
if (v_contextDependent_1097_ == 0)
{
uint8_t v_done_1100_; uint8_t v_contextDependent_1101_; 
v_done_1100_ = lean_ctor_get_uint8(v_a_1099_, 0);
v_contextDependent_1101_ = lean_ctor_get_uint8(v_a_1099_, 1);
lean_dec_ref_known(v_a_1099_, 0);
v___y_1012_ = v___y_1059_;
v___y_1013_ = v___y_1062_;
v___y_1014_ = v_contextDependent_1083_;
v___y_1015_ = v___y_1057_;
v___y_1016_ = v___y_1063_;
v___y_1017_ = v_done_1082_;
v___y_1018_ = v___y_1060_;
v___y_1019_ = v_done_1100_;
v___y_1020_ = v___y_1065_;
v___y_1021_ = v___y_1058_;
v___y_1022_ = v_e_x27_1095_;
v___y_1023_ = v___y_1061_;
v___y_1024_ = v___y_1064_;
v___y_1025_ = v_proof_1096_;
v___y_1026_ = v_contextDependent_1101_;
goto v___jp_1011_;
}
else
{
uint8_t v_done_1102_; 
v_done_1102_ = lean_ctor_get_uint8(v_a_1099_, 0);
lean_dec_ref_known(v_a_1099_, 0);
v___y_1012_ = v___y_1059_;
v___y_1013_ = v___y_1062_;
v___y_1014_ = v_contextDependent_1083_;
v___y_1015_ = v___y_1057_;
v___y_1016_ = v___y_1063_;
v___y_1017_ = v_done_1082_;
v___y_1018_ = v___y_1060_;
v___y_1019_ = v_done_1102_;
v___y_1020_ = v___y_1065_;
v___y_1021_ = v___y_1058_;
v___y_1022_ = v_e_x27_1095_;
v___y_1023_ = v___y_1061_;
v___y_1024_ = v___y_1064_;
v___y_1025_ = v_proof_1096_;
v___y_1026_ = v_contextDependent_1097_;
goto v___jp_1011_;
}
}
else
{
lean_object* v_e_x27_1103_; lean_object* v_proof_1104_; uint8_t v_done_1105_; uint8_t v_contextDependent_1106_; lean_object* v___x_1107_; 
v_e_x27_1103_ = lean_ctor_get(v_a_1099_, 0);
lean_inc_ref_n(v_e_x27_1103_, 2);
v_proof_1104_ = lean_ctor_get(v_a_1099_, 1);
lean_inc_ref(v_proof_1104_);
v_done_1105_ = lean_ctor_get_uint8(v_a_1099_, sizeof(void*)*2);
v_contextDependent_1106_ = lean_ctor_get_uint8(v_a_1099_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1099_, 2);
lean_inc_ref(v_e_u2081_771_);
v___x_1107_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_771_, v_e_x27_1095_, v_proof_1096_, v_e_x27_1103_, v_proof_1104_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1107_) == 0)
{
if (v_contextDependent_1097_ == 0)
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v___y_1029_ = v___y_1059_;
v___y_1030_ = v_e_x27_1103_;
v___y_1031_ = v___y_1062_;
v___y_1032_ = v_contextDependent_1083_;
v___y_1033_ = v___y_1057_;
v___y_1034_ = v___y_1063_;
v___y_1035_ = v_a_1108_;
v___y_1036_ = v_done_1082_;
v___y_1037_ = v___y_1060_;
v___y_1038_ = v_done_1105_;
v___y_1039_ = v___y_1065_;
v___y_1040_ = v___y_1058_;
v___y_1041_ = v___y_1061_;
v___y_1042_ = v___y_1064_;
v___y_1043_ = v_contextDependent_1106_;
goto v___jp_1028_;
}
else
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1107_, 1);
v___y_1029_ = v___y_1059_;
v___y_1030_ = v_e_x27_1103_;
v___y_1031_ = v___y_1062_;
v___y_1032_ = v_contextDependent_1083_;
v___y_1033_ = v___y_1057_;
v___y_1034_ = v___y_1063_;
v___y_1035_ = v_a_1109_;
v___y_1036_ = v_done_1082_;
v___y_1037_ = v___y_1060_;
v___y_1038_ = v_done_1105_;
v___y_1039_ = v___y_1065_;
v___y_1040_ = v___y_1058_;
v___y_1041_ = v___y_1061_;
v___y_1042_ = v___y_1064_;
v___y_1043_ = v_contextDependent_1097_;
goto v___jp_1028_;
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_e_x27_1103_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v_e_u2081_771_);
v_a_1110_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1107_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1107_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1096_);
lean_dec_ref(v_e_x27_1095_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v_e_u2081_771_);
return v___x_1098_;
}
}
else
{
v___y_983_ = v___y_1059_;
v___y_984_ = v___y_1065_;
v___y_985_ = v___y_1062_;
v___y_986_ = v_contextDependent_1083_;
v___y_987_ = v___y_1058_;
v___y_988_ = v___y_1057_;
v___y_989_ = v___y_1063_;
v___y_990_ = v___y_1061_;
v___y_991_ = v___y_1060_;
v___y_992_ = v_done_1082_;
v___y_993_ = v___y_1064_;
v___y_994_ = v___x_1085_;
goto v___jp_982_;
}
}
}
else
{
v___y_983_ = v___y_1059_;
v___y_984_ = v___y_1065_;
v___y_985_ = v___y_1062_;
v___y_986_ = v_contextDependent_1083_;
v___y_987_ = v___y_1058_;
v___y_988_ = v___y_1057_;
v___y_989_ = v___y_1063_;
v___y_990_ = v___y_1061_;
v___y_991_ = v___y_1060_;
v___y_992_ = v_done_1082_;
v___y_993_ = v___y_1064_;
v___y_994_ = v___x_1085_;
goto v___jp_982_;
}
}
else
{
uint8_t v_contextDependent_1118_; 
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
v_contextDependent_1118_ = lean_ctor_get_uint8(v_a_1078_, 1);
if (v_contextDependent_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v_numSteps_1120_; lean_object* v_persistentCache_1121_; lean_object* v_transientCache_1122_; lean_object* v_funext_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1135_; 
v___x_1119_ = lean_st_ref_take(v___y_1059_);
v_numSteps_1120_ = lean_ctor_get(v___x_1119_, 0);
v_persistentCache_1121_ = lean_ctor_get(v___x_1119_, 1);
v_transientCache_1122_ = lean_ctor_get(v___x_1119_, 2);
v_funext_1123_ = lean_ctor_get(v___x_1119_, 3);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1125_ = v___x_1119_;
v_isShared_1126_ = v_isSharedCheck_1135_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_funext_1123_);
lean_inc(v_transientCache_1122_);
lean_inc(v_persistentCache_1121_);
lean_inc(v_numSteps_1120_);
lean_dec(v___x_1119_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1135_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_inc_ref(v_a_1078_);
v___x_1127_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1121_, v_e_u2081_771_, v_a_1078_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_numSteps_1120_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_transientCache_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_funext_1123_);
v___x_1129_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_st_ref_put(v___y_1059_, v___x_1129_);
lean_dec(v___y_1059_);
if (v_isShared_1081_ == 0)
{
v___x_1132_ = v___x_1080_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1078_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v_numSteps_1137_; lean_object* v_persistentCache_1138_; lean_object* v_transientCache_1139_; lean_object* v_funext_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1152_; 
v___x_1136_ = lean_st_ref_take(v___y_1059_);
v_numSteps_1137_ = lean_ctor_get(v___x_1136_, 0);
v_persistentCache_1138_ = lean_ctor_get(v___x_1136_, 1);
v_transientCache_1139_ = lean_ctor_get(v___x_1136_, 2);
v_funext_1140_ = lean_ctor_get(v___x_1136_, 3);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1142_ = v___x_1136_;
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_funext_1140_);
lean_inc(v_transientCache_1139_);
lean_inc(v_persistentCache_1138_);
lean_inc(v_numSteps_1137_);
lean_dec(v___x_1136_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_inc_ref(v_a_1078_);
v___x_1144_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1139_, v_e_u2081_771_, v_a_1078_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 2, v___x_1144_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_numSteps_1137_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_persistentCache_1138_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_funext_1140_);
v___x_1146_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_st_ref_put(v___y_1059_, v___x_1146_);
lean_dec(v___y_1059_);
if (v_isShared_1081_ == 0)
{
v___x_1149_ = v___x_1080_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1078_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
else
{
uint8_t v_done_1153_; 
v_done_1153_ = lean_ctor_get_uint8(v_a_1078_, sizeof(void*)*2);
if (v_done_1153_ == 0)
{
lean_object* v_e_x27_1154_; lean_object* v_proof_1155_; uint8_t v_contextDependent_1156_; 
lean_del_object(v___x_1080_);
v_e_x27_1154_ = lean_ctor_get(v_a_1078_, 0);
lean_inc_ref(v_e_x27_1154_);
v_proof_1155_ = lean_ctor_get(v_a_1078_, 1);
lean_inc_ref(v_proof_1155_);
v_contextDependent_1156_ = lean_ctor_get_uint8(v_a_1078_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1078_, 2);
v_e_u2082_831_ = v_e_x27_1154_;
v_h_u2081_832_ = v_proof_1155_;
v_cd_u2081_833_ = v_contextDependent_1156_;
v___y_834_ = v___y_1057_;
v___y_835_ = v___y_1058_;
v___y_836_ = v___y_1059_;
v___y_837_ = v___y_1060_;
v___y_838_ = v___y_1061_;
v___y_839_ = v___y_1062_;
v___y_840_ = v___y_1063_;
v___y_841_ = v___y_1064_;
v___y_842_ = v___y_1065_;
goto v___jp_830_;
}
else
{
uint8_t v_contextDependent_1157_; 
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
v_contextDependent_1157_ = lean_ctor_get_uint8(v_a_1078_, sizeof(void*)*2 + 1);
if (v_contextDependent_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v_numSteps_1159_; lean_object* v_persistentCache_1160_; lean_object* v_transientCache_1161_; lean_object* v_funext_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1174_; 
v___x_1158_ = lean_st_ref_take(v___y_1059_);
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
lean_inc_ref(v_a_1078_);
v___x_1166_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1160_, v_e_u2081_771_, v_a_1078_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_numSteps_1159_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_transientCache_1161_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_funext_1162_);
v___x_1168_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_st_ref_put(v___y_1059_, v___x_1168_);
lean_dec(v___y_1059_);
if (v_isShared_1081_ == 0)
{
v___x_1171_ = v___x_1080_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1078_);
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
else
{
lean_object* v___x_1175_; lean_object* v_numSteps_1176_; lean_object* v_persistentCache_1177_; lean_object* v_transientCache_1178_; lean_object* v_funext_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1191_; 
v___x_1175_ = lean_st_ref_take(v___y_1059_);
v_numSteps_1176_ = lean_ctor_get(v___x_1175_, 0);
v_persistentCache_1177_ = lean_ctor_get(v___x_1175_, 1);
v_transientCache_1178_ = lean_ctor_get(v___x_1175_, 2);
v_funext_1179_ = lean_ctor_get(v___x_1175_, 3);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1181_ = v___x_1175_;
v_isShared_1182_ = v_isSharedCheck_1191_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_funext_1179_);
lean_inc(v_transientCache_1178_);
lean_inc(v_persistentCache_1177_);
lean_inc(v_numSteps_1176_);
lean_dec(v___x_1175_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1191_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_inc_ref(v_a_1078_);
v___x_1183_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1178_, v_e_u2081_771_, v_a_1078_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 2, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_numSteps_1176_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_persistentCache_1177_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_funext_1179_);
v___x_1185_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_st_ref_put(v___y_1059_, v___x_1185_);
lean_dec(v___y_1059_);
if (v_isShared_1081_ == 0)
{
v___x_1188_ = v___x_1080_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1078_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
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
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v_e_u2081_771_);
return v___x_1077_;
}
}
}
}
v___jp_1196_:
{
lean_object* v___x_1208_; lean_object* v_persistentCache_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_st_ref_get(v___y_1201_);
v_persistentCache_1209_ = lean_ctor_get(v___x_1208_, 1);
lean_inc_ref(v_persistentCache_1209_);
lean_dec(v___x_1208_);
v___x_1210_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_persistentCache_1209_, v_e_u2081_771_);
lean_dec_ref(v_persistentCache_1209_);
if (lean_obj_tag(v___x_1210_) == 1)
{
lean_object* v_toCold_1211_; lean_object* v_options_1212_; uint8_t v_hasTrace_1213_; 
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec(v___y_1197_);
v_toCold_1211_ = lean_ctor_get(v___y_1206_, 0);
v_options_1212_ = lean_ctor_get(v_toCold_1211_, 2);
v_hasTrace_1213_ = lean_ctor_get_uint8(v_options_1212_, sizeof(void*)*1);
if (v_hasTrace_1213_ == 0)
{
lean_object* v_val_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_e_u2081_771_);
v_val_1214_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1210_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_val_1214_);
lean_dec(v___x_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 0);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_val_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_val_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1253_; 
v_val_1222_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1224_ = v___x_1210_;
v_isShared_1225_ = v_isSharedCheck_1253_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_val_1222_);
lean_dec(v___x_1210_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1253_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_inheritedTraceOptions_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_inheritedTraceOptions_1226_ = lean_ctor_get(v_toCold_1211_, 11);
v___x_1227_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1228_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1226_, v_options_1212_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1231_; 
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_e_u2081_771_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 0);
v___x_1231_ = v___x_1224_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_val_1222_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_del_object(v___x_1224_);
v___x_1233_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4);
v___x_1234_ = l_Lean_MessageData_ofExpr(v_e_u2081_771_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1227_, v___x_1235_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v___x_1236_, 0);
lean_dec(v_unused_1244_);
v___x_1238_ = v___x_1236_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v___x_1236_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v_val_1222_);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_val_1222_);
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
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_val_1222_);
v_a_1245_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1236_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1236_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
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
}
}
}
else
{
lean_object* v___x_1254_; lean_object* v_transientCache_1255_; lean_object* v___x_1256_; 
lean_dec(v___x_1210_);
v___x_1254_ = lean_st_ref_get(v___y_1201_);
v_transientCache_1255_ = lean_ctor_get(v___x_1254_, 2);
lean_inc_ref(v_transientCache_1255_);
lean_dec(v___x_1254_);
v___x_1256_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_transientCache_1255_, v_e_u2081_771_);
lean_dec_ref(v_transientCache_1255_);
if (lean_obj_tag(v___x_1256_) == 1)
{
lean_object* v_toCold_1257_; lean_object* v_options_1258_; uint8_t v_hasTrace_1259_; 
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec(v___y_1197_);
v_toCold_1257_ = lean_ctor_get(v___y_1206_, 0);
v_options_1258_ = lean_ctor_get(v_toCold_1257_, 2);
v_hasTrace_1259_ = lean_ctor_get_uint8(v_options_1258_, sizeof(void*)*1);
if (v_hasTrace_1259_ == 0)
{
lean_object* v_val_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_e_u2081_771_);
v_val_1260_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1256_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_val_1260_);
lean_dec(v___x_1256_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 0);
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_val_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1299_; 
v_val_1268_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1270_ = v___x_1256_;
v_isShared_1271_ = v_isSharedCheck_1299_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_dec(v___x_1256_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1299_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_inheritedTraceOptions_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_inheritedTraceOptions_1272_ = lean_ctor_get(v_toCold_1257_, 11);
v___x_1273_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1274_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1275_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1272_, v_options_1258_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1277_; 
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_e_u2081_771_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 0);
v___x_1277_ = v___x_1270_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_val_1268_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_del_object(v___x_1270_);
v___x_1279_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6);
v___x_1280_ = l_Lean_MessageData_ofExpr(v_e_u2081_771_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1273_, v___x_1281_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v___x_1282_, 0);
lean_dec(v_unused_1290_);
v___x_1284_ = v___x_1282_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_dec(v___x_1282_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_val_1268_);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_val_1268_);
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
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_val_1268_);
v_a_1291_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1282_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1282_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
lean_dec(v___x_1256_);
v___x_1300_ = lean_nat_add(v___y_1197_, v___y_1198_);
lean_dec(v___y_1197_);
v___x_1301_ = lean_unsigned_to_nat(1000u);
v___x_1302_ = lean_nat_mod(v___x_1300_, v___x_1301_);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_nat_dec_eq(v___x_1302_, v___x_1303_);
lean_dec(v___x_1302_);
if (v___x_1304_ == 0)
{
v___y_1056_ = v___x_1300_;
v___y_1057_ = v___y_1199_;
v___y_1058_ = v___y_1200_;
v___y_1059_ = v___y_1201_;
v___y_1060_ = v___y_1202_;
v___y_1061_ = v___y_1203_;
v___y_1062_ = v___y_1204_;
v___y_1063_ = v___y_1205_;
v___y_1064_ = v___y_1206_;
v___y_1065_ = v___y_1207_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1306_ = l_Lean_Core_checkSystem(v___x_1305_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_dec_ref_known(v___x_1306_, 1);
v___y_1056_ = v___x_1300_;
v___y_1057_ = v___y_1199_;
v___y_1058_ = v___y_1200_;
v___y_1059_ = v___y_1201_;
v___y_1060_ = v___y_1202_;
v___y_1061_ = v___y_1203_;
v___y_1062_ = v___y_1204_;
v___y_1063_ = v___y_1205_;
v___y_1064_ = v___y_1206_;
v___y_1065_ = v___y_1207_;
goto v___jp_1055_;
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v___x_1300_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v_e_u2081_771_);
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
}
}
v___jp_1315_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_add(v_currRecDepth_1046_, v___x_1316_);
lean_dec(v_currRecDepth_1046_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v___x_1317_);
v___x_1319_ = v___x_1052_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_toCold_1045_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_ref_1047_);
lean_ctor_set_uint16(v_reuseFailAlloc_1344_, sizeof(void*)*3, v_optionFlags_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*3 + 2, v_suppressElabErrors_1049_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*3 + 3, v_isRecordingDeps_1050_);
v___x_1319_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v_numSteps_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_st_ref_get(v_a_774_);
v_numSteps_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_numSteps_1321_);
lean_dec(v___x_1320_);
v___x_1322_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_773_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v_maxSteps_1324_; uint8_t v___x_1325_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v_maxSteps_1324_ = lean_ctor_get(v_a_1323_, 0);
lean_inc(v_maxSteps_1324_);
lean_dec(v_a_1323_);
v___x_1325_ = lean_nat_dec_le(v_maxSteps_1324_, v_numSteps_1321_);
lean_dec(v_maxSteps_1324_);
if (v___x_1325_ == 0)
{
v___y_1197_ = v_numSteps_1321_;
v___y_1198_ = v___x_1316_;
v___y_1199_ = v_a_772_;
v___y_1200_ = v_a_773_;
v___y_1201_ = v_a_774_;
v___y_1202_ = v_a_775_;
v___y_1203_ = v_a_776_;
v___y_1204_ = v_a_777_;
v___y_1205_ = v_a_778_;
v___y_1206_ = v___x_1319_;
v___y_1207_ = v_a_780_;
goto v___jp_1196_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_numSteps_1321_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_e_u2081_771_);
v___x_1326_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8);
v___x_1327_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_1326_, v_a_777_, v_a_778_, v___x_1319_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v___x_1319_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_numSteps_1321_);
lean_dec_ref(v___x_1319_);
lean_dec(v_a_780_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_e_u2081_771_);
v_a_1336_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1322_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1322_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* v_e_u2081_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = lean_sym_simp(v_e_u2081_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* v_00_u03b2_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_1363_, v_x_1364_, v_x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* v_00_u03b2_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_1368_, v_x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* v_00_u03b2_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_1371_, v_x_1372_, v_x_1373_);
lean_dec_ref(v_x_1373_);
lean_dec_ref(v_x_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* v_cls_1375_, lean_object* v_msg_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_1375_, v_msg_1376_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* v_cls_1388_, lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_1388_, v_msg_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* v_00_u03b2_1401_, lean_object* v_x_1402_, size_t v_x_1403_, size_t v_x_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_1402_, v_x_1403_, v_x_1404_, v_x_1405_, v_x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
size_t v_x_111487__boxed_1414_; size_t v_x_111488__boxed_1415_; lean_object* v_res_1416_; 
v_x_111487__boxed_1414_ = lean_unbox_usize(v_x_1410_);
lean_dec(v_x_1410_);
v_x_111488__boxed_1415_ = lean_unbox_usize(v_x_1411_);
lean_dec(v_x_1411_);
v_res_1416_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_1408_, v_x_1409_, v_x_111487__boxed_1414_, v_x_111488__boxed_1415_, v_x_1412_, v_x_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* v_00_u03b2_1417_, lean_object* v_x_1418_, size_t v_x_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_1418_, v_x_1419_, v_x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
size_t v_x_111504__boxed_1426_; lean_object* v_res_1427_; 
v_x_111504__boxed_1426_ = lean_unbox_usize(v_x_1424_);
lean_dec(v_x_1424_);
v_res_1427_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_1422_, v_x_1423_, v_x_111504__boxed_1426_, v_x_1425_);
lean_dec_ref(v_x_1425_);
lean_dec_ref(v_x_1423_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1428_, lean_object* v_n_1429_, lean_object* v_k_1430_, lean_object* v_v_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v_n_1429_, v_k_1430_, v_v_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1433_, size_t v_depth_1434_, lean_object* v_keys_1435_, lean_object* v_vals_1436_, lean_object* v_heq_1437_, lean_object* v_i_1438_, lean_object* v_entries_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_1434_, v_keys_1435_, v_vals_1436_, v_i_1438_, v_entries_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1441_, lean_object* v_depth_1442_, lean_object* v_keys_1443_, lean_object* v_vals_1444_, lean_object* v_heq_1445_, lean_object* v_i_1446_, lean_object* v_entries_1447_){
_start:
{
size_t v_depth_boxed_1448_; lean_object* v_res_1449_; 
v_depth_boxed_1448_ = lean_unbox_usize(v_depth_1442_);
lean_dec(v_depth_1442_);
v_res_1449_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(v_00_u03b2_1441_, v_depth_boxed_1448_, v_keys_1443_, v_vals_1444_, v_heq_1445_, v_i_1446_, v_entries_1447_);
lean_dec_ref(v_vals_1444_);
lean_dec_ref(v_keys_1443_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1450_, lean_object* v_keys_1451_, lean_object* v_vals_1452_, lean_object* v_heq_1453_, lean_object* v_i_1454_, lean_object* v_k_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1451_, v_vals_1452_, v_i_1454_, v_k_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1457_, lean_object* v_keys_1458_, lean_object* v_vals_1459_, lean_object* v_heq_1460_, lean_object* v_i_1461_, lean_object* v_k_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(v_00_u03b2_1457_, v_keys_1458_, v_vals_1459_, v_heq_1460_, v_i_1461_, v_k_1462_);
lean_dec_ref(v_k_1462_);
lean_dec_ref(v_vals_1459_);
lean_dec_ref(v_keys_1458_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1465_, v_x_1466_, v_x_1467_, v_x_1468_);
return v___x_1469_;
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
