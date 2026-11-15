// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Main
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.Simp.Simproc import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.Simp.Have import Lean.Meta.Sym.Simp.Forall import Lean.Meta.Sym.InstantiateMVarsS
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateAssignedMVarHeadS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__5));
v___x_122_ = lean_unsigned_to_nat(3u);
v___x_123_ = l_Lean_Expr_isAppOfArity(v_e_103_, v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
goto v___jp_104_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = l_Lean_Expr_getAppNumArgs(v_e_103_);
v___x_126_ = lean_nat_sub(v___x_125_, v___x_124_);
lean_dec(v___x_125_);
v___x_127_ = lean_nat_sub(v___x_126_, v___x_124_);
lean_dec(v___x_126_);
v___x_128_ = l_Lean_Expr_getRevArg_x21(v_e_103_, v___x_127_);
v___x_129_ = l_Lean_Expr_isRawNatLit(v___x_128_);
lean_dec_ref(v___x_128_);
if (v___x_129_ == 0)
{
goto v___jp_104_;
}
else
{
return v___x_129_;
}
}
v___jp_104_:
{
uint8_t v___x_105_; 
v___x_105_ = l_Lean_Expr_isCharLit(v_e_103_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___closed__2));
v___x_107_ = lean_unsigned_to_nat(5u);
v___x_108_ = l_Lean_Expr_isAppOfArity(v_e_103_, v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_109_ = lean_unsigned_to_nat(2u);
v___x_110_ = l_Lean_Expr_getAppNumArgs(v_e_103_);
v___x_111_ = lean_nat_sub(v___x_110_, v___x_109_);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_sub(v___x_111_, v___x_112_);
lean_dec(v___x_111_);
v___x_114_ = l_Lean_Expr_getRevArg_x21(v_e_103_, v___x_113_);
v___x_115_ = l_Lean_Expr_isRawNatLit(v___x_114_);
lean_dec_ref(v___x_114_);
if (v___x_115_ == 0)
{
lean_dec(v___x_110_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_116_ = lean_unsigned_to_nat(4u);
v___x_117_ = lean_nat_sub(v___x_110_, v___x_116_);
lean_dec(v___x_110_);
v___x_118_ = lean_nat_sub(v___x_117_, v___x_112_);
lean_dec(v___x_117_);
v___x_119_ = l_Lean_Expr_getRevArg_x21(v_e_103_, v___x_118_);
v___x_120_ = l_Lean_Expr_isRawNatLit(v___x_119_);
lean_dec_ref(v___x_119_);
return v___x_120_;
}
}
}
else
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp___boxed(lean_object* v_e_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(v_e_130_);
lean_dec_ref(v_e_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object* v_d_133_, lean_object* v_e_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___y_143_; lean_object* v___x_146_; uint8_t v_debug_147_; 
v___x_146_ = lean_st_ref_get(v___y_136_);
v_debug_147_ = lean_ctor_get_uint8(v___x_146_, sizeof(void*)*13);
lean_dec(v___x_146_);
if (v_debug_147_ == 0)
{
v___y_143_ = v___y_136_;
goto v___jp_142_;
}
else
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_dec_ref_known(v___x_148_, 1);
v___y_143_ = v___y_136_;
goto v___jp_142_;
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v_e_134_);
lean_dec(v_d_133_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = l_Lean_Expr_mdata___override(v_d_133_, v_e_134_);
v___x_145_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_144_, v___y_143_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object* v_d_157_, lean_object* v_e_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_157_, v_e_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object* v_d_167_, lean_object* v_e_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_167_, v_e_168_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object* v_d_180_, lean_object* v_e_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(v_d_180_, v_e_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object* v_msgData_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_env_200_; uint8_t v___x_201_; lean_object* v_env_202_; lean_object* v___x_203_; lean_object* v_toCold_204_; lean_object* v_mctx_205_; lean_object* v_lctx_206_; lean_object* v_options_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_199_ = lean_st_ref_get(v___y_197_);
v_env_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_env_200_);
lean_dec(v___x_199_);
v___x_201_ = 0;
v_env_202_ = l_Lean_Environment_setRecordingDeps(v_env_200_, v___x_201_);
v___x_203_ = lean_st_ref_get(v___y_195_);
v_toCold_204_ = lean_ctor_get(v___y_196_, 0);
v_mctx_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc_ref(v_mctx_205_);
lean_dec(v___x_203_);
v_lctx_206_ = lean_ctor_get(v___y_194_, 2);
v_options_207_ = lean_ctor_get(v_toCold_204_, 2);
lean_inc_ref(v_options_207_);
lean_inc_ref(v_lctx_206_);
v___x_208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_208_, 0, v_env_202_);
lean_ctor_set(v___x_208_, 1, v_mctx_205_);
lean_ctor_set(v___x_208_, 2, v_lctx_206_);
lean_ctor_set(v___x_208_, 3, v_options_207_);
v___x_209_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v_msgData_193_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object* v_msgData_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msgData_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_ref_224_; lean_object* v___x_225_; lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_ref_224_ = lean_ctor_get(v___y_221_, 2);
v___x_225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
lean_inc(v_ref_224_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v_ref_224_);
lean_ctor_set(v___x_230_, 1, v_a_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 1);
lean_ctor_set(v___x_228_, 0, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object* v_e_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
switch(lean_obj_tag(v_e_250_))
{
case 2:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Meta_Sym_instantiateAssignedMVarHeadS_x3f(v_e_250_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_290_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_290_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_290_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_290_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
if (lean_obj_tag(v_a_262_) == 1)
{
lean_object* v_val_266_; lean_object* v___x_267_; 
lean_del_object(v___x_264_);
v_val_266_ = lean_ctor_get(v_a_262_, 0);
lean_inc_n(v_val_266_, 2);
lean_dec_ref_known(v_a_262_, 1);
v___x_267_ = l_Lean_Meta_Sym_mkEqRefl(v_val_266_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_277_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_277_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = 0;
v___x_273_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_273_, 0, v_val_266_);
lean_ctor_set(v___x_273_, 1, v_a_268_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*2, v___x_272_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*2 + 1, v___x_272_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_273_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec(v_val_266_);
v_a_278_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_267_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_267_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v___x_286_; lean_object* v___x_288_; 
lean_dec(v_a_262_);
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_286_);
v___x_288_ = v___x_264_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_a_291_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_261_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_261_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
case 5:
{
uint8_t v___x_299_; 
v___x_299_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_isLitApp(v_e_250_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref_known(v_e_250_, 2);
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
case 6:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_303_;
}
case 7:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_304_;
}
case 8:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_305_;
}
case 9:
{
lean_object* v_a_306_; 
v_a_306_ = lean_ctor_get(v_e_250_, 0);
lean_inc_ref(v_a_306_);
lean_dec_ref_known(v_e_250_, 1);
if (lean_obj_tag(v_a_306_) == 0)
{
lean_object* v_val_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_val_307_ = lean_ctor_get(v_a_306_, 0);
lean_inc(v_val_307_);
lean_dec_ref_known(v_a_306_, 1);
v___x_308_ = l_Lean_mkNatLit(v_val_307_);
v___x_309_ = l_Lean_Meta_Sym_shareCommonInc(v___x_308_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_311_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_n(v_a_310_, 2);
lean_dec_ref_known(v___x_309_, 1);
v___x_311_ = l_Lean_Meta_Sym_mkEqRefl(v_a_310_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_321_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_321_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = 0;
v___x_317_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_317_, 0, v_a_310_);
lean_ctor_set(v___x_317_, 1, v_a_312_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*2, v___x_316_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*2 + 1, v___x_316_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_a_310_);
v_a_322_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_311_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_311_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_309_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_309_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec_ref(v_a_306_);
v___x_338_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
case 10:
{
lean_object* v_data_340_; lean_object* v_expr_341_; lean_object* v___x_342_; 
v_data_340_ = lean_ctor_get(v_e_250_, 0);
lean_inc(v_data_340_);
v_expr_341_ = lean_ctor_get(v_e_250_, 1);
lean_inc_ref(v_expr_341_);
lean_dec_ref_known(v_e_250_, 2);
lean_inc(v_a_259_);
lean_inc_ref(v_a_258_);
lean_inc(v_a_257_);
lean_inc_ref(v_a_256_);
lean_inc(v_a_255_);
lean_inc_ref(v_a_254_);
lean_inc(v_a_253_);
lean_inc_ref(v_a_252_);
lean_inc(v_a_251_);
v___x_342_ = lean_sym_simp(v_expr_341_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_380_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_380_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_380_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_380_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
if (lean_obj_tag(v_a_343_) == 0)
{
uint8_t v_contextDependent_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
lean_dec(v_data_340_);
v_contextDependent_347_ = lean_ctor_get_uint8(v_a_343_, 1);
lean_dec_ref_known(v_a_343_, 0);
v___x_348_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_347_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_348_);
v___x_350_ = v___x_345_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
else
{
lean_object* v_e_x27_352_; lean_object* v_proof_353_; uint8_t v_contextDependent_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_379_; 
lean_del_object(v___x_345_);
v_e_x27_352_ = lean_ctor_get(v_a_343_, 0);
v_proof_353_ = lean_ctor_get(v_a_343_, 1);
v_contextDependent_354_ = lean_ctor_get_uint8(v_a_343_, sizeof(void*)*2 + 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_a_343_);
if (v_isSharedCheck_379_ == 0)
{
v___x_356_ = v_a_343_;
v_isShared_357_ = v_isSharedCheck_379_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_proof_353_);
lean_inc(v_e_x27_352_);
lean_dec(v_a_343_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_379_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_data_340_, v_e_x27_352_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_370_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_370_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
uint8_t v___x_363_; lean_object* v___x_365_; 
v___x_363_ = 0;
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v_a_359_);
v___x_365_ = v___x_356_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_359_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_proof_353_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, sizeof(void*)*2 + 1, v_contextDependent_354_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*2, v___x_363_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_365_);
v___x_367_ = v___x_361_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_del_object(v___x_356_);
lean_dec_ref(v_proof_353_);
v_a_371_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_358_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_358_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
}
else
{
lean_dec(v_data_340_);
return v___x_342_;
}
}
case 11:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2);
v___x_382_ = l_Lean_indentExpr(v_e_250_);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_385_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_386_;
}
default: 
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec_ref(v_e_250_);
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object* v_e_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object* v_00_u03b1_401_, lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_402_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object* v_00_u03b1_414_, lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(v_00_u03b1_414_, v_msg_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
return v_res_426_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = l_Lean_maxRecDepthErrorMessage;
v___x_433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3);
v___x_435_ = l_Lean_MessageData_ofFormat(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4);
v___x_437_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2));
v___x_438_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(lean_object* v_ref_439_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_ref_439_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(lean_object* v_ref_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(lean_object* v_00_u03b1_447_, lean_object* v_ref_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_448_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(lean_object* v_00_u03b1_460_, lean_object* v_ref_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(v_00_u03b1_460_, v_ref_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_post_485_; lean_object* v___x_486_; 
v_post_485_ = lean_ctor_get(v___y_475_, 1);
lean_inc_ref(v_post_485_);
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
lean_inc(v___y_481_);
lean_inc_ref(v___y_480_);
lean_inc(v___y_479_);
lean_inc_ref(v___y_478_);
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
lean_inc(v___y_475_);
v___x_486_ = lean_apply_11(v_post_485_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, lean_box(0));
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object* v_x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v_x_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
lean_object* v_ks_504_; lean_object* v_vs_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_531_; 
v_ks_504_ = lean_ctor_get(v_x_500_, 0);
v_vs_505_ = lean_ctor_get(v_x_500_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_531_ == 0)
{
v___x_507_ = v_x_500_;
v_isShared_508_ = v_isSharedCheck_531_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_vs_505_);
lean_inc(v_ks_504_);
lean_dec(v_x_500_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_531_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_array_get_size(v_ks_504_);
v___x_510_ = lean_nat_dec_lt(v_x_501_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
lean_dec(v_x_501_);
v___x_511_ = lean_array_push(v_ks_504_, v_x_502_);
v___x_512_ = lean_array_push(v_vs_505_, v_x_503_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_512_);
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_514_ = v___x_507_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
else
{
lean_object* v_k_x27_516_; size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v_k_x27_516_ = lean_array_fget_borrowed(v_ks_504_, v_x_501_);
v___x_517_ = lean_ptr_addr(v_x_502_);
v___x_518_ = lean_ptr_addr(v_k_x27_516_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_521_; 
if (v_isShared_508_ == 0)
{
v___x_521_ = v___x_507_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_ks_504_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_vs_505_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_x_501_, v___x_522_);
lean_dec(v_x_501_);
v_x_500_ = v___x_521_;
v_x_501_ = v___x_523_;
goto _start;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_526_ = lean_array_fset(v_ks_504_, v_x_501_, v_x_502_);
v___x_527_ = lean_array_fset(v_vs_505_, v_x_501_, v_x_503_);
lean_dec(v_x_501_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_527_);
lean_ctor_set(v___x_507_, 0, v___x_526_);
v___x_529_ = v___x_507_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_532_, lean_object* v_k_533_, lean_object* v_v_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_n_532_, v___x_535_, v_k_533_, v_v_534_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* v_x_538_, size_t v_x_539_, size_t v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v_es_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v_j_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_es_543_ = lean_ctor_get(v_x_538_, 0);
v___x_544_ = ((size_t)31ULL);
v___x_545_ = lean_usize_land(v_x_539_, v___x_544_);
v_j_546_ = lean_usize_to_nat(v___x_545_);
v___x_547_ = lean_array_get_size(v_es_543_);
v___x_548_ = lean_nat_dec_lt(v_j_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec(v_j_546_);
lean_dec(v_x_542_);
lean_dec_ref(v_x_541_);
return v_x_538_;
}
else
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_589_; 
lean_inc_ref(v_es_543_);
v_isSharedCheck_589_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v_x_538_, 0);
lean_dec(v_unused_590_);
v___x_550_ = v_x_538_;
v_isShared_551_ = v_isSharedCheck_589_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_x_538_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_589_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_v_552_; lean_object* v___x_553_; lean_object* v_xs_x27_554_; lean_object* v___y_556_; 
v_v_552_ = lean_array_fget(v_es_543_, v_j_546_);
v___x_553_ = lean_box(0);
v_xs_x27_554_ = lean_array_fset(v_es_543_, v_j_546_, v___x_553_);
switch(lean_obj_tag(v_v_552_))
{
case 0:
{
lean_object* v_key_561_; lean_object* v_val_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_574_; 
v_key_561_ = lean_ctor_get(v_v_552_, 0);
v_val_562_ = lean_ctor_get(v_v_552_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_v_552_);
if (v_isSharedCheck_574_ == 0)
{
v___x_564_ = v_v_552_;
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_val_562_);
lean_inc(v_key_561_);
lean_dec(v_v_552_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
size_t v___x_566_; size_t v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_ptr_addr(v_x_541_);
v___x_567_ = lean_ptr_addr(v_key_561_);
v___x_568_ = lean_usize_dec_eq(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_del_object(v___x_564_);
v___x_569_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_561_, v_val_562_, v_x_541_, v_x_542_);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
v___y_556_ = v___x_570_;
goto v___jp_555_;
}
else
{
lean_object* v___x_572_; 
lean_dec(v_val_562_);
lean_dec(v_key_561_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v_x_542_);
lean_ctor_set(v___x_564_, 0, v_x_541_);
v___x_572_ = v___x_564_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_x_541_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_x_542_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v___y_556_ = v___x_572_;
goto v___jp_555_;
}
}
}
}
case 1:
{
lean_object* v_node_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_587_; 
v_node_575_ = lean_ctor_get(v_v_552_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_v_552_);
if (v_isSharedCheck_587_ == 0)
{
v___x_577_ = v_v_552_;
v_isShared_578_ = v_isSharedCheck_587_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_node_575_);
lean_dec(v_v_552_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_587_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_579_ = ((size_t)5ULL);
v___x_580_ = lean_usize_shift_right(v_x_539_, v___x_579_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_add(v_x_540_, v___x_581_);
v___x_583_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_575_, v___x_580_, v___x_582_, v_x_541_, v_x_542_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_583_);
v___x_585_ = v___x_577_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
v___y_556_ = v___x_585_;
goto v___jp_555_;
}
}
}
default: 
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_x_541_);
lean_ctor_set(v___x_588_, 1, v_x_542_);
v___y_556_ = v___x_588_;
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
lean_object* v_ks_591_; lean_object* v_vs_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_610_; 
v_ks_591_ = lean_ctor_get(v_x_538_, 0);
v_vs_592_ = lean_ctor_get(v_x_538_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_610_ == 0)
{
v___x_594_ = v_x_538_;
v_isShared_595_ = v_isSharedCheck_610_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_vs_592_);
lean_inc(v_ks_591_);
lean_dec(v_x_538_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_610_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_ks_591_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_vs_592_);
v___x_597_ = v_reuseFailAlloc_609_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v_newNode_598_; size_t v___x_599_; uint8_t v___x_600_; 
v_newNode_598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v___x_597_, v_x_541_, v_x_542_);
v___x_599_ = ((size_t)7ULL);
v___x_600_ = lean_usize_dec_le(v___x_599_, v_x_540_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_598_);
v___x_602_ = lean_unsigned_to_nat(4u);
v___x_603_ = lean_nat_dec_lt(v___x_601_, v___x_602_);
lean_dec(v___x_601_);
if (v___x_603_ == 0)
{
lean_object* v_ks_604_; lean_object* v_vs_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_ks_604_ = lean_ctor_get(v_newNode_598_, 0);
lean_inc_ref(v_ks_604_);
v_vs_605_ = lean_ctor_get(v_newNode_598_, 1);
lean_inc_ref(v_vs_605_);
lean_dec_ref(v_newNode_598_);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
v___x_608_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_x_540_, v_ks_604_, v_vs_605_, v___x_606_, v___x_607_);
lean_dec_ref(v_vs_605_);
lean_dec_ref(v_ks_604_);
return v___x_608_;
}
else
{
return v_newNode_598_;
}
}
else
{
return v_newNode_598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_611_, lean_object* v_keys_612_, lean_object* v_vals_613_, lean_object* v_i_614_, lean_object* v_entries_615_){
_start:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_array_get_size(v_keys_612_);
v___x_617_ = lean_nat_dec_lt(v_i_614_, v___x_616_);
if (v___x_617_ == 0)
{
lean_dec(v_i_614_);
return v_entries_615_;
}
else
{
lean_object* v_k_618_; lean_object* v_v_619_; size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; uint64_t v___x_623_; size_t v_h_624_; size_t v___x_625_; lean_object* v___x_626_; size_t v___x_627_; size_t v___x_628_; size_t v___x_629_; size_t v_h_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_k_618_ = lean_array_fget_borrowed(v_keys_612_, v_i_614_);
v_v_619_ = lean_array_fget_borrowed(v_vals_613_, v_i_614_);
v___x_620_ = lean_ptr_addr(v_k_618_);
v___x_621_ = ((size_t)3ULL);
v___x_622_ = lean_usize_shift_right(v___x_620_, v___x_621_);
v___x_623_ = lean_usize_to_uint64(v___x_622_);
v_h_624_ = lean_uint64_to_usize(v___x_623_);
v___x_625_ = ((size_t)5ULL);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_sub(v_depth_611_, v___x_627_);
v___x_629_ = lean_usize_mul(v___x_625_, v___x_628_);
v_h_630_ = lean_usize_shift_right(v_h_624_, v___x_629_);
v___x_631_ = lean_nat_add(v_i_614_, v___x_626_);
lean_dec(v_i_614_);
lean_inc(v_v_619_);
lean_inc(v_k_618_);
v___x_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_615_, v_h_630_, v_depth_611_, v_k_618_, v_v_619_);
v_i_614_ = v___x_631_;
v_entries_615_ = v___x_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_634_, lean_object* v_keys_635_, lean_object* v_vals_636_, lean_object* v_i_637_, lean_object* v_entries_638_){
_start:
{
size_t v_depth_boxed_639_; lean_object* v_res_640_; 
v_depth_boxed_639_ = lean_unbox_usize(v_depth_634_);
lean_dec(v_depth_634_);
v_res_640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_639_, v_keys_635_, v_vals_636_, v_i_637_, v_entries_638_);
lean_dec_ref(v_vals_636_);
lean_dec_ref(v_keys_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
size_t v_x_112094__boxed_646_; size_t v_x_112095__boxed_647_; lean_object* v_res_648_; 
v_x_112094__boxed_646_ = lean_unbox_usize(v_x_642_);
lean_dec(v_x_642_);
v_x_112095__boxed_647_ = lean_unbox_usize(v_x_643_);
lean_dec(v_x_643_);
v_res_648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_641_, v_x_112094__boxed_646_, v_x_112095__boxed_647_, v_x_644_, v_x_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; uint64_t v___x_655_; size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_652_ = lean_ptr_addr(v_x_650_);
v___x_653_ = ((size_t)3ULL);
v___x_654_ = lean_usize_shift_right(v___x_652_, v___x_653_);
v___x_655_ = lean_usize_to_uint64(v___x_654_);
v___x_656_ = lean_uint64_to_usize(v___x_655_);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_649_, v___x_656_, v___x_657_, v_x_650_, v_x_651_);
return v___x_658_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_659_; double v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_float_of_nat(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* v_cls_664_, lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_ref_671_; lean_object* v___x_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_718_; 
v_ref_671_ = lean_ctor_get(v___y_668_, 2);
v___x_672_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_718_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_718_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_718_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v_traceState_678_; lean_object* v_env_679_; lean_object* v_nextMacroScope_680_; lean_object* v_ngen_681_; lean_object* v_auxDeclNGen_682_; lean_object* v_cache_683_; lean_object* v_recordedDeps_684_; lean_object* v_messages_685_; lean_object* v_infoState_686_; lean_object* v_snapshotTasks_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_717_; 
v___x_677_ = lean_st_ref_take(v___y_669_);
v_traceState_678_ = lean_ctor_get(v___x_677_, 4);
v_env_679_ = lean_ctor_get(v___x_677_, 0);
v_nextMacroScope_680_ = lean_ctor_get(v___x_677_, 1);
v_ngen_681_ = lean_ctor_get(v___x_677_, 2);
v_auxDeclNGen_682_ = lean_ctor_get(v___x_677_, 3);
v_cache_683_ = lean_ctor_get(v___x_677_, 5);
v_recordedDeps_684_ = lean_ctor_get(v___x_677_, 6);
v_messages_685_ = lean_ctor_get(v___x_677_, 7);
v_infoState_686_ = lean_ctor_get(v___x_677_, 8);
v_snapshotTasks_687_ = lean_ctor_get(v___x_677_, 9);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_717_ == 0)
{
v___x_689_ = v___x_677_;
v_isShared_690_ = v_isSharedCheck_717_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snapshotTasks_687_);
lean_inc(v_infoState_686_);
lean_inc(v_messages_685_);
lean_inc(v_recordedDeps_684_);
lean_inc(v_cache_683_);
lean_inc(v_traceState_678_);
lean_inc(v_auxDeclNGen_682_);
lean_inc(v_ngen_681_);
lean_inc(v_nextMacroScope_680_);
lean_inc(v_env_679_);
lean_dec(v___x_677_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_717_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint64_t v_tid_691_; lean_object* v_traces_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_716_; 
v_tid_691_ = lean_ctor_get_uint64(v_traceState_678_, sizeof(void*)*1);
v_traces_692_ = lean_ctor_get(v_traceState_678_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v_traceState_678_);
if (v_isSharedCheck_716_ == 0)
{
v___x_694_ = v_traceState_678_;
v_isShared_695_ = v_isSharedCheck_716_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_traces_692_);
lean_dec(v_traceState_678_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_716_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; double v___x_698_; uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_696_ = lean_box(0);
v___x_697_ = lean_box(0);
v___x_698_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0);
v___x_699_ = 0;
v___x_700_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1));
v___x_701_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_701_, 0, v_cls_664_);
lean_ctor_set(v___x_701_, 1, v___x_697_);
lean_ctor_set(v___x_701_, 2, v___x_700_);
lean_ctor_set_float(v___x_701_, sizeof(void*)*3, v___x_698_);
lean_ctor_set_float(v___x_701_, sizeof(void*)*3 + 8, v___x_698_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*3 + 16, v___x_699_);
v___x_702_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2));
v___x_703_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v_a_673_);
lean_ctor_set(v___x_703_, 2, v___x_702_);
lean_inc(v_ref_671_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_ref_671_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Lean_PersistentArray_push___redArg(v_traces_692_, v___x_704_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_705_);
v___x_707_ = v___x_694_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_705_);
lean_ctor_set_uint64(v_reuseFailAlloc_715_, sizeof(void*)*1, v_tid_691_);
v___x_707_ = v_reuseFailAlloc_715_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 4, v___x_707_);
v___x_709_ = v___x_689_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_env_679_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_nextMacroScope_680_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_ngen_681_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_auxDeclNGen_682_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_714_, 5, v_cache_683_);
lean_ctor_set(v_reuseFailAlloc_714_, 6, v_recordedDeps_684_);
lean_ctor_set(v_reuseFailAlloc_714_, 7, v_messages_685_);
lean_ctor_set(v_reuseFailAlloc_714_, 8, v_infoState_686_);
lean_ctor_set(v_reuseFailAlloc_714_, 9, v_snapshotTasks_687_);
v___x_709_ = v_reuseFailAlloc_714_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_st_ref_put(v___y_669_, v___x_709_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_696_);
v___x_712_ = v___x_675_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_696_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* v_cls_719_, lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_719_, v_msg_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_727_, lean_object* v_vals_728_, lean_object* v_i_729_, lean_object* v_k_730_){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_array_get_size(v_keys_727_);
v___x_732_ = lean_nat_dec_lt(v_i_729_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec(v_i_729_);
v___x_733_ = lean_box(0);
return v___x_733_;
}
else
{
lean_object* v_k_x27_734_; size_t v___x_735_; size_t v___x_736_; uint8_t v___x_737_; 
v_k_x27_734_ = lean_array_fget_borrowed(v_keys_727_, v_i_729_);
v___x_735_ = lean_ptr_addr(v_k_730_);
v___x_736_ = lean_ptr_addr(v_k_x27_734_);
v___x_737_ = lean_usize_dec_eq(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_nat_add(v_i_729_, v___x_738_);
lean_dec(v_i_729_);
v_i_729_ = v___x_739_;
goto _start;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_array_fget_borrowed(v_vals_728_, v_i_729_);
lean_dec(v_i_729_);
lean_inc(v___x_741_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_743_, lean_object* v_vals_744_, lean_object* v_i_745_, lean_object* v_k_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_743_, v_vals_744_, v_i_745_, v_k_746_);
lean_dec_ref(v_k_746_);
lean_dec_ref(v_vals_744_);
lean_dec_ref(v_keys_743_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* v_x_748_, size_t v_x_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v_es_751_; lean_object* v___x_752_; size_t v___x_753_; size_t v___x_754_; lean_object* v_j_755_; lean_object* v___x_756_; 
v_es_751_ = lean_ctor_get(v_x_748_, 0);
v___x_752_ = lean_box(2);
v___x_753_ = ((size_t)31ULL);
v___x_754_ = lean_usize_land(v_x_749_, v___x_753_);
v_j_755_ = lean_usize_to_nat(v___x_754_);
v___x_756_ = lean_array_get_borrowed(v___x_752_, v_es_751_, v_j_755_);
lean_dec(v_j_755_);
switch(lean_obj_tag(v___x_756_))
{
case 0:
{
lean_object* v_key_757_; lean_object* v_val_758_; size_t v___x_759_; size_t v___x_760_; uint8_t v___x_761_; 
v_key_757_ = lean_ctor_get(v___x_756_, 0);
v_val_758_ = lean_ctor_get(v___x_756_, 1);
v___x_759_ = lean_ptr_addr(v_x_750_);
v___x_760_ = lean_ptr_addr(v_key_757_);
v___x_761_ = lean_usize_dec_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
v___x_762_ = lean_box(0);
return v___x_762_;
}
else
{
lean_object* v___x_763_; 
lean_inc(v_val_758_);
v___x_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_763_, 0, v_val_758_);
return v___x_763_;
}
}
case 1:
{
lean_object* v_node_764_; size_t v___x_765_; size_t v___x_766_; 
v_node_764_ = lean_ctor_get(v___x_756_, 0);
v___x_765_ = ((size_t)5ULL);
v___x_766_ = lean_usize_shift_right(v_x_749_, v___x_765_);
v_x_748_ = v_node_764_;
v_x_749_ = v___x_766_;
goto _start;
}
default: 
{
lean_object* v___x_768_; 
v___x_768_ = lean_box(0);
return v___x_768_;
}
}
}
else
{
lean_object* v_ks_769_; lean_object* v_vs_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_ks_769_ = lean_ctor_get(v_x_748_, 0);
v_vs_770_ = lean_ctor_get(v_x_748_, 1);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_ks_769_, v_vs_770_, v___x_771_, v_x_750_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
size_t v_x_112396__boxed_776_; lean_object* v_res_777_; 
v_x_112396__boxed_776_ = lean_unbox_usize(v_x_774_);
lean_dec(v_x_774_);
v_res_777_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_773_, v_x_112396__boxed_776_, v_x_775_);
lean_dec_ref(v_x_775_);
lean_dec_ref(v_x_773_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; uint64_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_780_ = lean_ptr_addr(v_x_779_);
v___x_781_ = ((size_t)3ULL);
v___x_782_ = lean_usize_shift_right(v___x_780_, v___x_781_);
v___x_783_ = lean_usize_to_uint64(v___x_782_);
v___x_784_ = lean_uint64_to_usize(v___x_783_);
v___x_785_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_778_, v___x_784_, v_x_779_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_786_, v_x_787_);
lean_dec_ref(v_x_787_);
lean_dec_ref(v_x_786_);
return v_res_788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1));
v___x_794_ = l_Lean_Name_append(v___x_793_, v___x_792_);
return v___x_794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* lean_sym_simp(lean_object* v_e_u2081_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_834_; lean_object* v___y_835_; uint8_t v___y_836_; uint8_t v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___y_858_; lean_object* v___y_861_; uint8_t v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; uint8_t v___y_865_; lean_object* v_e_u2082_868_; lean_object* v_h_u2081_869_; uint8_t v_cd_u2081_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; uint8_t v___y_996_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; uint8_t v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; uint8_t v___y_1011_; lean_object* v___y_1013_; uint8_t v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; uint8_t v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v_a_1024_; lean_object* v___y_1028_; lean_object* v___y_1029_; uint8_t v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; uint8_t v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; uint8_t v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; uint8_t v___y_1050_; uint8_t v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; uint8_t v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; uint8_t v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; uint8_t v___y_1074_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v_toCold_1112_; lean_object* v_currRecDepth_1113_; lean_object* v_ref_1114_; uint16_t v_optionFlags_1115_; uint8_t v_suppressElabErrors_1116_; uint8_t v_checkDeprecated_1117_; uint8_t v_isRecordingDeps_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1385_; 
v_toCold_1112_ = lean_ctor_get(v_a_812_, 0);
v_currRecDepth_1113_ = lean_ctor_get(v_a_812_, 1);
v_ref_1114_ = lean_ctor_get(v_a_812_, 2);
v_optionFlags_1115_ = lean_ctor_get_uint16(v_a_812_, sizeof(void*)*3);
v_suppressElabErrors_1116_ = lean_ctor_get_uint8(v_a_812_, sizeof(void*)*3 + 2);
v_checkDeprecated_1117_ = lean_ctor_get_uint8(v_a_812_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1118_ = lean_ctor_get_uint8(v_a_812_, sizeof(void*)*3 + 4);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_a_812_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1120_ = v_a_812_;
v_isShared_1121_ = v_isSharedCheck_1385_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_ref_1114_);
lean_inc(v_currRecDepth_1113_);
lean_inc(v_toCold_1112_);
lean_dec(v_a_812_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1385_;
goto v_resetjp_1119_;
}
v___jp_815_:
{
lean_object* v___x_818_; lean_object* v_numSteps_819_; lean_object* v_persistentCache_820_; lean_object* v_transientCache_821_; lean_object* v_funext_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_832_; 
v___x_818_ = lean_st_ref_take(v___y_816_);
v_numSteps_819_ = lean_ctor_get(v___x_818_, 0);
v_persistentCache_820_ = lean_ctor_get(v___x_818_, 1);
v_transientCache_821_ = lean_ctor_get(v___x_818_, 2);
v_funext_822_ = lean_ctor_get(v___x_818_, 3);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_832_ == 0)
{
v___x_824_ = v___x_818_;
v_isShared_825_ = v_isSharedCheck_832_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_funext_822_);
lean_inc(v_transientCache_821_);
lean_inc(v_persistentCache_820_);
lean_inc(v_numSteps_819_);
lean_dec(v___x_818_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_832_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_inc_ref(v___y_817_);
v___x_826_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_821_, v_e_u2081_804_, v___y_817_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 2, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_numSteps_819_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_persistentCache_820_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_funext_822_);
v___x_828_ = v_reuseFailAlloc_831_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_st_ref_put(v___y_816_, v___x_828_);
lean_dec(v___y_816_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___y_817_);
return v___x_830_;
}
}
}
v___jp_833_:
{
if (v___y_836_ == 0)
{
uint8_t v___x_837_; 
v___x_837_ = l_Lean_Expr_hasMVar(v_e_u2081_804_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v_numSteps_839_; lean_object* v_persistentCache_840_; lean_object* v_transientCache_841_; lean_object* v_funext_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_852_; 
v___x_838_ = lean_st_ref_take(v___y_834_);
v_numSteps_839_ = lean_ctor_get(v___x_838_, 0);
v_persistentCache_840_ = lean_ctor_get(v___x_838_, 1);
v_transientCache_841_ = lean_ctor_get(v___x_838_, 2);
v_funext_842_ = lean_ctor_get(v___x_838_, 3);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_852_ == 0)
{
v___x_844_ = v___x_838_;
v_isShared_845_ = v_isSharedCheck_852_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_funext_842_);
lean_inc(v_transientCache_841_);
lean_inc(v_persistentCache_840_);
lean_inc(v_numSteps_839_);
lean_dec(v___x_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_852_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
lean_inc_ref(v___y_835_);
v___x_846_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_840_, v_e_u2081_804_, v___y_835_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_numSteps_839_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_transientCache_841_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_funext_842_);
v___x_848_ = v_reuseFailAlloc_851_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_st_ref_put(v___y_834_, v___x_848_);
lean_dec(v___y_834_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___y_835_);
return v___x_850_;
}
}
}
else
{
v___y_816_ = v___y_834_;
v___y_817_ = v___y_835_;
goto v___jp_815_;
}
}
else
{
v___y_816_ = v___y_834_;
v___y_817_ = v___y_835_;
goto v___jp_815_;
}
}
v___jp_853_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_859_, 0, v___y_857_);
lean_ctor_set(v___x_859_, 1, v___y_856_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*2, v___y_854_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*2 + 1, v___y_858_);
v___y_834_ = v___y_855_;
v___y_835_ = v___x_859_;
v___y_836_ = v___y_858_;
goto v___jp_833_;
}
v___jp_860_:
{
lean_object* v___x_866_; 
v___x_866_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_866_, 0, v___y_864_);
lean_ctor_set(v___x_866_, 1, v___y_863_);
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*2, v___y_862_);
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*2 + 1, v___y_865_);
v___y_834_ = v___y_861_;
v___y_835_ = v___x_866_;
v___y_836_ = v___y_865_;
goto v___jp_833_;
}
v___jp_867_:
{
lean_object* v___x_880_; 
lean_inc(v___y_879_);
lean_inc_ref(v___y_878_);
lean_inc(v___y_877_);
lean_inc_ref(v___y_876_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_874_);
lean_inc(v___y_873_);
lean_inc_ref(v_e_u2082_868_);
v___x_880_ = lean_sym_simp(v_e_u2082_868_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
if (lean_obj_tag(v_a_881_) == 0)
{
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
if (v_cd_u2081_870_ == 0)
{
uint8_t v_done_882_; uint8_t v_contextDependent_883_; 
v_done_882_ = lean_ctor_get_uint8(v_a_881_, 0);
v_contextDependent_883_ = lean_ctor_get_uint8(v_a_881_, 1);
lean_dec_ref_known(v_a_881_, 0);
v___y_854_ = v_done_882_;
v___y_855_ = v___y_873_;
v___y_856_ = v_h_u2081_869_;
v___y_857_ = v_e_u2082_868_;
v___y_858_ = v_contextDependent_883_;
goto v___jp_853_;
}
else
{
uint8_t v_done_884_; 
v_done_884_ = lean_ctor_get_uint8(v_a_881_, 0);
lean_dec_ref_known(v_a_881_, 0);
v___y_854_ = v_done_884_;
v___y_855_ = v___y_873_;
v___y_856_ = v_h_u2081_869_;
v___y_857_ = v_e_u2082_868_;
v___y_858_ = v_cd_u2081_870_;
goto v___jp_853_;
}
}
else
{
lean_object* v_e_x27_885_; lean_object* v_proof_886_; uint8_t v_done_887_; uint8_t v_contextDependent_888_; lean_object* v___x_889_; 
v_e_x27_885_ = lean_ctor_get(v_a_881_, 0);
lean_inc_ref_n(v_e_x27_885_, 2);
v_proof_886_ = lean_ctor_get(v_a_881_, 1);
lean_inc_ref(v_proof_886_);
v_done_887_ = lean_ctor_get_uint8(v_a_881_, sizeof(void*)*2);
v_contextDependent_888_ = lean_ctor_get_uint8(v_a_881_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_881_, 2);
lean_inc_ref(v_e_u2081_804_);
v___x_889_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_804_, v_e_u2082_868_, v_h_u2081_869_, v_e_x27_885_, v_proof_886_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
if (lean_obj_tag(v___x_889_) == 0)
{
if (v_cd_u2081_870_ == 0)
{
lean_object* v_a_890_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v___y_861_ = v___y_873_;
v___y_862_ = v_done_887_;
v___y_863_ = v_a_890_;
v___y_864_ = v_e_x27_885_;
v___y_865_ = v_contextDependent_888_;
goto v___jp_860_;
}
else
{
lean_object* v_a_891_; 
v_a_891_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_889_, 1);
v___y_861_ = v___y_873_;
v___y_862_ = v_done_887_;
v___y_863_ = v_a_891_;
v___y_864_ = v_e_x27_885_;
v___y_865_ = v_cd_u2081_870_;
goto v___jp_860_;
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v_e_x27_885_);
lean_dec(v___y_873_);
lean_dec_ref(v_e_u2081_804_);
v_a_892_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_889_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_889_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
else
{
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v_h_u2081_869_);
lean_dec_ref(v_e_u2082_868_);
lean_dec_ref(v_e_u2081_804_);
return v___x_880_;
}
}
v___jp_900_:
{
lean_object* v___x_903_; lean_object* v_numSteps_904_; lean_object* v_persistentCache_905_; lean_object* v_transientCache_906_; lean_object* v_funext_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_917_; 
v___x_903_ = lean_st_ref_take(v___y_902_);
v_numSteps_904_ = lean_ctor_get(v___x_903_, 0);
v_persistentCache_905_ = lean_ctor_get(v___x_903_, 1);
v_transientCache_906_ = lean_ctor_get(v___x_903_, 2);
v_funext_907_ = lean_ctor_get(v___x_903_, 3);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_917_ == 0)
{
v___x_909_ = v___x_903_;
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_funext_907_);
lean_inc(v_transientCache_906_);
lean_inc(v_persistentCache_905_);
lean_inc(v_numSteps_904_);
lean_dec(v___x_903_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_inc_ref(v___y_901_);
v___x_911_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_906_, v_e_u2081_804_, v___y_901_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 2, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_numSteps_904_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_persistentCache_905_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_funext_907_);
v___x_913_ = v_reuseFailAlloc_916_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_st_ref_put(v___y_902_, v___x_913_);
lean_dec(v___y_902_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___y_901_);
return v___x_915_;
}
}
}
v___jp_918_:
{
lean_object* v___x_921_; lean_object* v_numSteps_922_; lean_object* v_persistentCache_923_; lean_object* v_transientCache_924_; lean_object* v_funext_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_935_; 
v___x_921_ = lean_st_ref_take(v___y_920_);
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
lean_inc_ref(v___y_919_);
v___x_929_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_924_, v_e_u2081_804_, v___y_919_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 2, v___x_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_numSteps_922_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_persistentCache_923_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_funext_925_);
v___x_931_ = v_reuseFailAlloc_934_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_st_ref_put(v___y_920_, v___x_931_);
lean_dec(v___y_920_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___y_919_);
return v___x_933_;
}
}
}
v___jp_936_:
{
if (lean_obj_tag(v___y_946_) == 0)
{
uint8_t v_contextDependent_947_; 
lean_dec_ref(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
v_contextDependent_947_ = lean_ctor_get_uint8(v___y_946_, 1);
if (v_contextDependent_947_ == 0)
{
uint8_t v___x_948_; 
v___x_948_ = l_Lean_Expr_hasMVar(v_e_u2081_804_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v_numSteps_950_; lean_object* v_persistentCache_951_; lean_object* v_transientCache_952_; lean_object* v_funext_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_963_; 
v___x_949_ = lean_st_ref_take(v___y_945_);
v_numSteps_950_ = lean_ctor_get(v___x_949_, 0);
v_persistentCache_951_ = lean_ctor_get(v___x_949_, 1);
v_transientCache_952_ = lean_ctor_get(v___x_949_, 2);
v_funext_953_ = lean_ctor_get(v___x_949_, 3);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_963_ == 0)
{
v___x_955_ = v___x_949_;
v_isShared_956_ = v_isSharedCheck_963_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_funext_953_);
lean_inc(v_transientCache_952_);
lean_inc(v_persistentCache_951_);
lean_inc(v_numSteps_950_);
lean_dec(v___x_949_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_963_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
lean_inc_ref(v___y_946_);
v___x_957_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_951_, v_e_u2081_804_, v___y_946_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_numSteps_950_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_transientCache_952_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_funext_953_);
v___x_959_ = v_reuseFailAlloc_962_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_st_ref_put(v___y_945_, v___x_959_);
lean_dec(v___y_945_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___y_946_);
return v___x_961_;
}
}
}
else
{
v___y_901_ = v___y_946_;
v___y_902_ = v___y_945_;
goto v___jp_900_;
}
}
else
{
v___y_901_ = v___y_946_;
v___y_902_ = v___y_945_;
goto v___jp_900_;
}
}
else
{
uint8_t v_done_964_; 
v_done_964_ = lean_ctor_get_uint8(v___y_946_, sizeof(void*)*2);
if (v_done_964_ == 0)
{
lean_object* v_e_x27_965_; lean_object* v_proof_966_; uint8_t v_contextDependent_967_; 
v_e_x27_965_ = lean_ctor_get(v___y_946_, 0);
lean_inc_ref(v_e_x27_965_);
v_proof_966_ = lean_ctor_get(v___y_946_, 1);
lean_inc_ref(v_proof_966_);
v_contextDependent_967_ = lean_ctor_get_uint8(v___y_946_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v___y_946_, 2);
v_e_u2082_868_ = v_e_x27_965_;
v_h_u2081_869_ = v_proof_966_;
v_cd_u2081_870_ = v_contextDependent_967_;
v___y_871_ = v___y_942_;
v___y_872_ = v___y_940_;
v___y_873_ = v___y_945_;
v___y_874_ = v___y_943_;
v___y_875_ = v___y_937_;
v___y_876_ = v___y_944_;
v___y_877_ = v___y_938_;
v___y_878_ = v___y_939_;
v___y_879_ = v___y_941_;
goto v___jp_867_;
}
else
{
uint8_t v_contextDependent_968_; 
lean_dec_ref(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
v_contextDependent_968_ = lean_ctor_get_uint8(v___y_946_, sizeof(void*)*2 + 1);
if (v_contextDependent_968_ == 0)
{
uint8_t v___x_969_; 
v___x_969_ = l_Lean_Expr_hasMVar(v_e_u2081_804_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v_numSteps_971_; lean_object* v_persistentCache_972_; lean_object* v_transientCache_973_; lean_object* v_funext_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_984_; 
v___x_970_ = lean_st_ref_take(v___y_945_);
v_numSteps_971_ = lean_ctor_get(v___x_970_, 0);
v_persistentCache_972_ = lean_ctor_get(v___x_970_, 1);
v_transientCache_973_ = lean_ctor_get(v___x_970_, 2);
v_funext_974_ = lean_ctor_get(v___x_970_, 3);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_984_ == 0)
{
v___x_976_ = v___x_970_;
v_isShared_977_ = v_isSharedCheck_984_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_funext_974_);
lean_inc(v_transientCache_973_);
lean_inc(v_persistentCache_972_);
lean_inc(v_numSteps_971_);
lean_dec(v___x_970_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_984_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
lean_inc_ref(v___y_946_);
v___x_978_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_972_, v_e_u2081_804_, v___y_946_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_numSteps_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_transientCache_973_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v_funext_974_);
v___x_980_ = v_reuseFailAlloc_983_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_st_ref_put(v___y_945_, v___x_980_);
lean_dec(v___y_945_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___y_946_);
return v___x_982_;
}
}
}
else
{
v___y_919_ = v___y_946_;
v___y_920_ = v___y_945_;
goto v___jp_918_;
}
}
else
{
v___y_919_ = v___y_946_;
v___y_920_ = v___y_945_;
goto v___jp_918_;
}
}
}
}
v___jp_985_:
{
if (v___y_996_ == 0)
{
v___y_937_ = v___y_986_;
v___y_938_ = v___y_988_;
v___y_939_ = v___y_990_;
v___y_940_ = v___y_989_;
v___y_941_ = v___y_991_;
v___y_942_ = v___y_992_;
v___y_943_ = v___y_993_;
v___y_944_ = v___y_995_;
v___y_945_ = v___y_994_;
v___y_946_ = v___y_987_;
goto v___jp_936_;
}
else
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_987_);
v___y_937_ = v___y_986_;
v___y_938_ = v___y_988_;
v___y_939_ = v___y_990_;
v___y_940_ = v___y_989_;
v___y_941_ = v___y_991_;
v___y_942_ = v___y_992_;
v___y_943_ = v___y_993_;
v___y_944_ = v___y_995_;
v___y_945_ = v___y_994_;
v___y_946_ = v___x_997_;
goto v___jp_936_;
}
}
v___jp_998_:
{
if (v___y_1011_ == 0)
{
v___y_986_ = v___y_1005_;
v___y_987_ = v___y_999_;
v___y_988_ = v___y_1007_;
v___y_989_ = v___y_1008_;
v___y_990_ = v___y_1000_;
v___y_991_ = v___y_1001_;
v___y_992_ = v___y_1009_;
v___y_993_ = v___y_1010_;
v___y_994_ = v___y_1003_;
v___y_995_ = v___y_1004_;
v___y_996_ = v___y_1006_;
goto v___jp_985_;
}
else
{
v___y_986_ = v___y_1005_;
v___y_987_ = v___y_999_;
v___y_988_ = v___y_1007_;
v___y_989_ = v___y_1008_;
v___y_990_ = v___y_1000_;
v___y_991_ = v___y_1001_;
v___y_992_ = v___y_1009_;
v___y_993_ = v___y_1010_;
v___y_994_ = v___y_1003_;
v___y_995_ = v___y_1004_;
v___y_996_ = v___y_1002_;
goto v___jp_985_;
}
}
v___jp_1012_:
{
if (v___y_1014_ == 0)
{
v___y_937_ = v___y_1013_;
v___y_938_ = v___y_1015_;
v___y_939_ = v___y_1017_;
v___y_940_ = v___y_1016_;
v___y_941_ = v___y_1018_;
v___y_942_ = v___y_1019_;
v___y_943_ = v___y_1021_;
v___y_944_ = v___y_1023_;
v___y_945_ = v___y_1022_;
v___y_946_ = v_a_1024_;
goto v___jp_936_;
}
else
{
if (lean_obj_tag(v_a_1024_) == 0)
{
uint8_t v_contextDependent_1025_; 
v_contextDependent_1025_ = lean_ctor_get_uint8(v_a_1024_, 1);
v___y_999_ = v_a_1024_;
v___y_1000_ = v___y_1017_;
v___y_1001_ = v___y_1018_;
v___y_1002_ = v___y_1020_;
v___y_1003_ = v___y_1022_;
v___y_1004_ = v___y_1023_;
v___y_1005_ = v___y_1013_;
v___y_1006_ = v___y_1014_;
v___y_1007_ = v___y_1015_;
v___y_1008_ = v___y_1016_;
v___y_1009_ = v___y_1019_;
v___y_1010_ = v___y_1021_;
v___y_1011_ = v_contextDependent_1025_;
goto v___jp_998_;
}
else
{
uint8_t v_contextDependent_1026_; 
v_contextDependent_1026_ = lean_ctor_get_uint8(v_a_1024_, sizeof(void*)*2 + 1);
v___y_999_ = v_a_1024_;
v___y_1000_ = v___y_1017_;
v___y_1001_ = v___y_1018_;
v___y_1002_ = v___y_1020_;
v___y_1003_ = v___y_1022_;
v___y_1004_ = v___y_1023_;
v___y_1005_ = v___y_1013_;
v___y_1006_ = v___y_1014_;
v___y_1007_ = v___y_1015_;
v___y_1008_ = v___y_1016_;
v___y_1009_ = v___y_1019_;
v___y_1010_ = v___y_1021_;
v___y_1011_ = v_contextDependent_1026_;
goto v___jp_998_;
}
}
}
v___jp_1027_:
{
if (v___y_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1039_);
v___y_1013_ = v___y_1033_;
v___y_1014_ = v___y_1034_;
v___y_1015_ = v___y_1035_;
v___y_1016_ = v___y_1036_;
v___y_1017_ = v___y_1028_;
v___y_1018_ = v___y_1029_;
v___y_1019_ = v___y_1037_;
v___y_1020_ = v___y_1030_;
v___y_1021_ = v___y_1038_;
v___y_1022_ = v___y_1031_;
v___y_1023_ = v___y_1032_;
v_a_1024_ = v___x_1041_;
goto v___jp_1012_;
}
else
{
v___y_1013_ = v___y_1033_;
v___y_1014_ = v___y_1034_;
v___y_1015_ = v___y_1035_;
v___y_1016_ = v___y_1036_;
v___y_1017_ = v___y_1028_;
v___y_1018_ = v___y_1029_;
v___y_1019_ = v___y_1037_;
v___y_1020_ = v___y_1030_;
v___y_1021_ = v___y_1038_;
v___y_1022_ = v___y_1031_;
v___y_1023_ = v___y_1032_;
v_a_1024_ = v___y_1039_;
goto v___jp_1012_;
}
}
v___jp_1042_:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1058_, 0, v___y_1045_);
lean_ctor_set(v___x_1058_, 1, v___y_1055_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*2, v___y_1050_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*2 + 1, v___y_1057_);
v___y_1013_ = v___y_1049_;
v___y_1014_ = v___y_1051_;
v___y_1015_ = v___y_1052_;
v___y_1016_ = v___y_1053_;
v___y_1017_ = v___y_1043_;
v___y_1018_ = v___y_1044_;
v___y_1019_ = v___y_1054_;
v___y_1020_ = v___y_1046_;
v___y_1021_ = v___y_1056_;
v___y_1022_ = v___y_1048_;
v___y_1023_ = v___y_1047_;
v_a_1024_ = v___x_1058_;
goto v___jp_1012_;
}
v___jp_1059_:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1075_, 0, v___y_1062_);
lean_ctor_set(v___x_1075_, 1, v___y_1068_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*2, v___y_1071_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*2 + 1, v___y_1074_);
v___y_1013_ = v___y_1066_;
v___y_1014_ = v___y_1067_;
v___y_1015_ = v___y_1069_;
v___y_1016_ = v___y_1070_;
v___y_1017_ = v___y_1060_;
v___y_1018_ = v___y_1061_;
v___y_1019_ = v___y_1072_;
v___y_1020_ = v___y_1063_;
v___y_1021_ = v___y_1073_;
v___y_1022_ = v___y_1065_;
v___y_1023_ = v___y_1064_;
v_a_1024_ = v___x_1075_;
goto v___jp_1012_;
}
v___jp_1076_:
{
lean_object* v___x_1079_; lean_object* v_numSteps_1080_; lean_object* v_persistentCache_1081_; lean_object* v_transientCache_1082_; lean_object* v_funext_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1093_; 
v___x_1079_ = lean_st_ref_take(v___y_1078_);
v_numSteps_1080_ = lean_ctor_get(v___x_1079_, 0);
v_persistentCache_1081_ = lean_ctor_get(v___x_1079_, 1);
v_transientCache_1082_ = lean_ctor_get(v___x_1079_, 2);
v_funext_1083_ = lean_ctor_get(v___x_1079_, 3);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1085_ = v___x_1079_;
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_funext_1083_);
lean_inc(v_transientCache_1082_);
lean_inc(v_persistentCache_1081_);
lean_inc(v_numSteps_1080_);
lean_dec(v___x_1079_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_inc_ref(v___y_1077_);
v___x_1087_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1082_, v_e_u2081_804_, v___y_1077_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 2, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_numSteps_1080_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_persistentCache_1081_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_funext_1083_);
v___x_1089_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_st_ref_put(v___y_1078_, v___x_1089_);
lean_dec(v___y_1078_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___y_1077_);
return v___x_1091_;
}
}
}
v___jp_1094_:
{
lean_object* v___x_1097_; lean_object* v_numSteps_1098_; lean_object* v_persistentCache_1099_; lean_object* v_transientCache_1100_; lean_object* v_funext_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1111_; 
v___x_1097_ = lean_st_ref_take(v___y_1096_);
v_numSteps_1098_ = lean_ctor_get(v___x_1097_, 0);
v_persistentCache_1099_ = lean_ctor_get(v___x_1097_, 1);
v_transientCache_1100_ = lean_ctor_get(v___x_1097_, 2);
v_funext_1101_ = lean_ctor_get(v___x_1097_, 3);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1103_ = v___x_1097_;
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_funext_1101_);
lean_inc(v_transientCache_1100_);
lean_inc(v_persistentCache_1099_);
lean_inc(v_numSteps_1098_);
lean_dec(v___x_1097_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
lean_inc_ref(v___y_1095_);
v___x_1105_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_1100_, v_e_u2081_804_, v___y_1095_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 2, v___x_1105_);
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_numSteps_1098_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_persistentCache_1099_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_funext_1101_);
v___x_1107_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_st_ref_put(v___y_1096_, v___x_1107_);
lean_dec(v___y_1096_);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___y_1095_);
return v___x_1109_;
}
}
}
v_resetjp_1119_:
{
lean_object* v_maxRecDepth_1122_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_maxRecDepth_1122_ = lean_ctor_get(v_toCold_1112_, 3);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_nat_dec_eq(v_maxRecDepth_1122_, v___x_1381_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_eq(v_currRecDepth_1113_, v_maxRecDepth_1122_);
if (v___x_1383_ == 0)
{
goto v___jp_1351_;
}
else
{
lean_object* v___x_1384_; 
lean_del_object(v___x_1120_);
lean_dec(v_currRecDepth_1113_);
lean_dec_ref(v_toCold_1112_);
lean_dec(v_a_813_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_e_u2081_804_);
v___x_1384_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_1114_);
return v___x_1384_;
}
}
else
{
goto v___jp_1351_;
}
v___jp_1123_:
{
lean_object* v___x_1134_; lean_object* v_persistentCache_1135_; lean_object* v_transientCache_1136_; lean_object* v_funext_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1230_; 
v___x_1134_ = lean_st_ref_take(v___y_1127_);
v_persistentCache_1135_ = lean_ctor_get(v___x_1134_, 1);
v_transientCache_1136_ = lean_ctor_get(v___x_1134_, 2);
v_funext_1137_ = lean_ctor_get(v___x_1134_, 3);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1134_, 0);
lean_dec(v_unused_1231_);
v___x_1139_ = v___x_1134_;
v_isShared_1140_ = v_isSharedCheck_1230_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_funext_1137_);
lean_inc(v_transientCache_1136_);
lean_inc(v_persistentCache_1135_);
lean_dec(v___x_1134_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1230_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___y_1124_);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___y_1124_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_persistentCache_1135_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_transientCache_1136_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_funext_1137_);
v___x_1142_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v_pre_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_st_ref_put(v___y_1127_, v___x_1142_);
v_pre_1144_ = lean_ctor_get(v___y_1125_, 0);
lean_inc_ref(v_pre_1144_);
lean_inc(v___y_1133_);
lean_inc_ref(v___y_1132_);
lean_inc(v___y_1131_);
lean_inc_ref(v___y_1130_);
lean_inc(v___y_1129_);
lean_inc_ref(v___y_1128_);
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
lean_inc(v___y_1125_);
lean_inc_ref(v_e_u2081_804_);
v___x_1145_ = lean_apply_11(v_pre_1144_, v_e_u2081_804_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, lean_box(0));
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1228_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1228_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1228_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
if (lean_obj_tag(v_a_1146_) == 0)
{
uint8_t v_done_1150_; 
v_done_1150_ = lean_ctor_get_uint8(v_a_1146_, 0);
if (v_done_1150_ == 0)
{
uint8_t v_contextDependent_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_del_object(v___x_1148_);
v_contextDependent_1151_ = lean_ctor_get_uint8(v_a_1146_, 1);
lean_dec_ref_known(v_a_1146_, 0);
v___x_1152_ = lean_box(0);
lean_inc_ref(v_e_u2081_804_);
v___x_1153_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_u2081_804_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
if (lean_obj_tag(v_a_1154_) == 0)
{
uint8_t v_done_1155_; 
v_done_1155_ = lean_ctor_get_uint8(v_a_1154_, 0);
if (v_done_1155_ == 0)
{
uint8_t v_contextDependent_1156_; lean_object* v___x_1157_; 
v_contextDependent_1156_ = lean_ctor_get_uint8(v_a_1154_, 1);
lean_dec_ref_known(v_a_1154_, 0);
lean_inc_ref(v_e_u2081_804_);
v___x_1157_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1152_, v_e_u2081_804_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1157_) == 0)
{
if (v_contextDependent_1156_ == 0)
{
lean_object* v_a_1158_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___y_1013_ = v___y_1129_;
v___y_1014_ = v_contextDependent_1151_;
v___y_1015_ = v___y_1131_;
v___y_1016_ = v___y_1126_;
v___y_1017_ = v___y_1132_;
v___y_1018_ = v___y_1133_;
v___y_1019_ = v___y_1125_;
v___y_1020_ = v_done_1150_;
v___y_1021_ = v___y_1128_;
v___y_1022_ = v___y_1127_;
v___y_1023_ = v___y_1130_;
v_a_1024_ = v_a_1158_;
goto v___jp_1012_;
}
else
{
lean_object* v_a_1159_; 
v_a_1159_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1157_, 1);
if (lean_obj_tag(v_a_1159_) == 0)
{
uint8_t v_contextDependent_1160_; 
v_contextDependent_1160_ = lean_ctor_get_uint8(v_a_1159_, 1);
v___y_1028_ = v___y_1132_;
v___y_1029_ = v___y_1133_;
v___y_1030_ = v_done_1150_;
v___y_1031_ = v___y_1127_;
v___y_1032_ = v___y_1130_;
v___y_1033_ = v___y_1129_;
v___y_1034_ = v_contextDependent_1151_;
v___y_1035_ = v___y_1131_;
v___y_1036_ = v___y_1126_;
v___y_1037_ = v___y_1125_;
v___y_1038_ = v___y_1128_;
v___y_1039_ = v_a_1159_;
v___y_1040_ = v_contextDependent_1160_;
goto v___jp_1027_;
}
else
{
uint8_t v_contextDependent_1161_; 
v_contextDependent_1161_ = lean_ctor_get_uint8(v_a_1159_, sizeof(void*)*2 + 1);
v___y_1028_ = v___y_1132_;
v___y_1029_ = v___y_1133_;
v___y_1030_ = v_done_1150_;
v___y_1031_ = v___y_1127_;
v___y_1032_ = v___y_1130_;
v___y_1033_ = v___y_1129_;
v___y_1034_ = v_contextDependent_1151_;
v___y_1035_ = v___y_1131_;
v___y_1036_ = v___y_1126_;
v___y_1037_ = v___y_1125_;
v___y_1038_ = v___y_1128_;
v___y_1039_ = v_a_1159_;
v___y_1040_ = v_contextDependent_1161_;
goto v___jp_1027_;
}
}
}
else
{
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v_e_u2081_804_);
return v___x_1157_;
}
}
else
{
v___y_1013_ = v___y_1129_;
v___y_1014_ = v_contextDependent_1151_;
v___y_1015_ = v___y_1131_;
v___y_1016_ = v___y_1126_;
v___y_1017_ = v___y_1132_;
v___y_1018_ = v___y_1133_;
v___y_1019_ = v___y_1125_;
v___y_1020_ = v_done_1150_;
v___y_1021_ = v___y_1128_;
v___y_1022_ = v___y_1127_;
v___y_1023_ = v___y_1130_;
v_a_1024_ = v_a_1154_;
goto v___jp_1012_;
}
}
else
{
uint8_t v_done_1162_; 
v_done_1162_ = lean_ctor_get_uint8(v_a_1154_, sizeof(void*)*2);
if (v_done_1162_ == 0)
{
lean_object* v_e_x27_1163_; lean_object* v_proof_1164_; uint8_t v_contextDependent_1165_; lean_object* v___x_1166_; 
v_e_x27_1163_ = lean_ctor_get(v_a_1154_, 0);
lean_inc_ref_n(v_e_x27_1163_, 2);
v_proof_1164_ = lean_ctor_get(v_a_1154_, 1);
lean_inc_ref(v_proof_1164_);
v_contextDependent_1165_ = lean_ctor_get_uint8(v_a_1154_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1154_, 2);
v___x_1166_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_1152_, v_e_x27_1163_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
if (lean_obj_tag(v_a_1167_) == 0)
{
if (v_contextDependent_1165_ == 0)
{
uint8_t v_done_1168_; uint8_t v_contextDependent_1169_; 
v_done_1168_ = lean_ctor_get_uint8(v_a_1167_, 0);
v_contextDependent_1169_ = lean_ctor_get_uint8(v_a_1167_, 1);
lean_dec_ref_known(v_a_1167_, 0);
v___y_1043_ = v___y_1132_;
v___y_1044_ = v___y_1133_;
v___y_1045_ = v_e_x27_1163_;
v___y_1046_ = v_done_1150_;
v___y_1047_ = v___y_1130_;
v___y_1048_ = v___y_1127_;
v___y_1049_ = v___y_1129_;
v___y_1050_ = v_done_1168_;
v___y_1051_ = v_contextDependent_1151_;
v___y_1052_ = v___y_1131_;
v___y_1053_ = v___y_1126_;
v___y_1054_ = v___y_1125_;
v___y_1055_ = v_proof_1164_;
v___y_1056_ = v___y_1128_;
v___y_1057_ = v_contextDependent_1169_;
goto v___jp_1042_;
}
else
{
uint8_t v_done_1170_; 
v_done_1170_ = lean_ctor_get_uint8(v_a_1167_, 0);
lean_dec_ref_known(v_a_1167_, 0);
v___y_1043_ = v___y_1132_;
v___y_1044_ = v___y_1133_;
v___y_1045_ = v_e_x27_1163_;
v___y_1046_ = v_done_1150_;
v___y_1047_ = v___y_1130_;
v___y_1048_ = v___y_1127_;
v___y_1049_ = v___y_1129_;
v___y_1050_ = v_done_1170_;
v___y_1051_ = v_contextDependent_1151_;
v___y_1052_ = v___y_1131_;
v___y_1053_ = v___y_1126_;
v___y_1054_ = v___y_1125_;
v___y_1055_ = v_proof_1164_;
v___y_1056_ = v___y_1128_;
v___y_1057_ = v_contextDependent_1165_;
goto v___jp_1042_;
}
}
else
{
lean_object* v_e_x27_1171_; lean_object* v_proof_1172_; uint8_t v_done_1173_; uint8_t v_contextDependent_1174_; lean_object* v___x_1175_; 
v_e_x27_1171_ = lean_ctor_get(v_a_1167_, 0);
lean_inc_ref_n(v_e_x27_1171_, 2);
v_proof_1172_ = lean_ctor_get(v_a_1167_, 1);
lean_inc_ref(v_proof_1172_);
v_done_1173_ = lean_ctor_get_uint8(v_a_1167_, sizeof(void*)*2);
v_contextDependent_1174_ = lean_ctor_get_uint8(v_a_1167_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1167_, 2);
lean_inc_ref(v_e_u2081_804_);
v___x_1175_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_804_, v_e_x27_1163_, v_proof_1164_, v_e_x27_1171_, v_proof_1172_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1175_) == 0)
{
if (v_contextDependent_1165_ == 0)
{
lean_object* v_a_1176_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___y_1060_ = v___y_1132_;
v___y_1061_ = v___y_1133_;
v___y_1062_ = v_e_x27_1171_;
v___y_1063_ = v_done_1150_;
v___y_1064_ = v___y_1130_;
v___y_1065_ = v___y_1127_;
v___y_1066_ = v___y_1129_;
v___y_1067_ = v_contextDependent_1151_;
v___y_1068_ = v_a_1176_;
v___y_1069_ = v___y_1131_;
v___y_1070_ = v___y_1126_;
v___y_1071_ = v_done_1173_;
v___y_1072_ = v___y_1125_;
v___y_1073_ = v___y_1128_;
v___y_1074_ = v_contextDependent_1174_;
goto v___jp_1059_;
}
else
{
lean_object* v_a_1177_; 
v_a_1177_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1175_, 1);
v___y_1060_ = v___y_1132_;
v___y_1061_ = v___y_1133_;
v___y_1062_ = v_e_x27_1171_;
v___y_1063_ = v_done_1150_;
v___y_1064_ = v___y_1130_;
v___y_1065_ = v___y_1127_;
v___y_1066_ = v___y_1129_;
v___y_1067_ = v_contextDependent_1151_;
v___y_1068_ = v_a_1177_;
v___y_1069_ = v___y_1131_;
v___y_1070_ = v___y_1126_;
v___y_1071_ = v_done_1173_;
v___y_1072_ = v___y_1125_;
v___y_1073_ = v___y_1128_;
v___y_1074_ = v_contextDependent_1165_;
goto v___jp_1059_;
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_e_x27_1171_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v_e_u2081_804_);
v_a_1178_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1175_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1175_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1164_);
lean_dec_ref(v_e_x27_1163_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v_e_u2081_804_);
return v___x_1166_;
}
}
else
{
v___y_1013_ = v___y_1129_;
v___y_1014_ = v_contextDependent_1151_;
v___y_1015_ = v___y_1131_;
v___y_1016_ = v___y_1126_;
v___y_1017_ = v___y_1132_;
v___y_1018_ = v___y_1133_;
v___y_1019_ = v___y_1125_;
v___y_1020_ = v_done_1150_;
v___y_1021_ = v___y_1128_;
v___y_1022_ = v___y_1127_;
v___y_1023_ = v___y_1130_;
v_a_1024_ = v_a_1154_;
goto v___jp_1012_;
}
}
}
else
{
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v_e_u2081_804_);
return v___x_1153_;
}
}
else
{
uint8_t v_contextDependent_1186_; 
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
v_contextDependent_1186_ = lean_ctor_get_uint8(v_a_1146_, 1);
if (v_contextDependent_1186_ == 0)
{
uint8_t v___x_1187_; 
v___x_1187_ = l_Lean_Expr_hasMVar(v_e_u2081_804_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v_numSteps_1189_; lean_object* v_persistentCache_1190_; lean_object* v_transientCache_1191_; lean_object* v_funext_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1204_; 
v___x_1188_ = lean_st_ref_take(v___y_1127_);
v_numSteps_1189_ = lean_ctor_get(v___x_1188_, 0);
v_persistentCache_1190_ = lean_ctor_get(v___x_1188_, 1);
v_transientCache_1191_ = lean_ctor_get(v___x_1188_, 2);
v_funext_1192_ = lean_ctor_get(v___x_1188_, 3);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1194_ = v___x_1188_;
v_isShared_1195_ = v_isSharedCheck_1204_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_funext_1192_);
lean_inc(v_transientCache_1191_);
lean_inc(v_persistentCache_1190_);
lean_inc(v_numSteps_1189_);
lean_dec(v___x_1188_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1204_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_inc_ref(v_a_1146_);
v___x_1196_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1190_, v_e_u2081_804_, v_a_1146_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_numSteps_1189_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_transientCache_1191_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_funext_1192_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_st_ref_put(v___y_1127_, v___x_1198_);
lean_dec(v___y_1127_);
if (v_isShared_1149_ == 0)
{
v___x_1201_ = v___x_1148_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1146_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_del_object(v___x_1148_);
v___y_1077_ = v_a_1146_;
v___y_1078_ = v___y_1127_;
goto v___jp_1076_;
}
}
else
{
lean_del_object(v___x_1148_);
v___y_1077_ = v_a_1146_;
v___y_1078_ = v___y_1127_;
goto v___jp_1076_;
}
}
}
else
{
uint8_t v_done_1205_; 
v_done_1205_ = lean_ctor_get_uint8(v_a_1146_, sizeof(void*)*2);
if (v_done_1205_ == 0)
{
lean_object* v_e_x27_1206_; lean_object* v_proof_1207_; uint8_t v_contextDependent_1208_; 
lean_del_object(v___x_1148_);
v_e_x27_1206_ = lean_ctor_get(v_a_1146_, 0);
lean_inc_ref(v_e_x27_1206_);
v_proof_1207_ = lean_ctor_get(v_a_1146_, 1);
lean_inc_ref(v_proof_1207_);
v_contextDependent_1208_ = lean_ctor_get_uint8(v_a_1146_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1146_, 2);
v_e_u2082_868_ = v_e_x27_1206_;
v_h_u2081_869_ = v_proof_1207_;
v_cd_u2081_870_ = v_contextDependent_1208_;
v___y_871_ = v___y_1125_;
v___y_872_ = v___y_1126_;
v___y_873_ = v___y_1127_;
v___y_874_ = v___y_1128_;
v___y_875_ = v___y_1129_;
v___y_876_ = v___y_1130_;
v___y_877_ = v___y_1131_;
v___y_878_ = v___y_1132_;
v___y_879_ = v___y_1133_;
goto v___jp_867_;
}
else
{
uint8_t v_contextDependent_1209_; 
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
v_contextDependent_1209_ = lean_ctor_get_uint8(v_a_1146_, sizeof(void*)*2 + 1);
if (v_contextDependent_1209_ == 0)
{
uint8_t v___x_1210_; 
v___x_1210_ = l_Lean_Expr_hasMVar(v_e_u2081_804_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v_numSteps_1212_; lean_object* v_persistentCache_1213_; lean_object* v_transientCache_1214_; lean_object* v_funext_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1227_; 
v___x_1211_ = lean_st_ref_take(v___y_1127_);
v_numSteps_1212_ = lean_ctor_get(v___x_1211_, 0);
v_persistentCache_1213_ = lean_ctor_get(v___x_1211_, 1);
v_transientCache_1214_ = lean_ctor_get(v___x_1211_, 2);
v_funext_1215_ = lean_ctor_get(v___x_1211_, 3);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1217_ = v___x_1211_;
v_isShared_1218_ = v_isSharedCheck_1227_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_funext_1215_);
lean_inc(v_transientCache_1214_);
lean_inc(v_persistentCache_1213_);
lean_inc(v_numSteps_1212_);
lean_dec(v___x_1211_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1227_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
lean_inc_ref(v_a_1146_);
v___x_1219_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_1213_, v_e_u2081_804_, v_a_1146_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_numSteps_1212_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_transientCache_1214_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_funext_1215_);
v___x_1221_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_st_ref_put(v___y_1127_, v___x_1221_);
lean_dec(v___y_1127_);
if (v_isShared_1149_ == 0)
{
v___x_1224_ = v___x_1148_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1146_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_del_object(v___x_1148_);
v___y_1095_ = v_a_1146_;
v___y_1096_ = v___y_1127_;
goto v___jp_1094_;
}
}
else
{
lean_del_object(v___x_1148_);
v___y_1095_ = v_a_1146_;
v___y_1096_ = v___y_1127_;
goto v___jp_1094_;
}
}
}
}
}
else
{
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v_e_u2081_804_);
return v___x_1145_;
}
}
}
}
v___jp_1232_:
{
lean_object* v___x_1244_; lean_object* v_persistentCache_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_st_ref_get(v___y_1237_);
v_persistentCache_1245_ = lean_ctor_get(v___x_1244_, 1);
lean_inc_ref(v_persistentCache_1245_);
lean_dec(v___x_1244_);
v___x_1246_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_persistentCache_1245_, v_e_u2081_804_);
lean_dec_ref(v_persistentCache_1245_);
if (lean_obj_tag(v___x_1246_) == 1)
{
lean_object* v_toCold_1247_; lean_object* v_options_1248_; uint8_t v_hasTrace_1249_; 
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec(v___y_1233_);
v_toCold_1247_ = lean_ctor_get(v___y_1242_, 0);
v_options_1248_ = lean_ctor_get(v_toCold_1247_, 2);
v_hasTrace_1249_ = lean_ctor_get_uint8(v_options_1248_, sizeof(void*)*1);
if (v_hasTrace_1249_ == 0)
{
lean_object* v_val_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_e_u2081_804_);
v_val_1250_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1246_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_val_1250_);
lean_dec(v___x_1246_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 0);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_val_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v_val_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1289_; 
v_val_1258_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1260_ = v___x_1246_;
v_isShared_1261_ = v_isSharedCheck_1289_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_val_1258_);
lean_dec(v___x_1246_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1289_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_inheritedTraceOptions_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_inheritedTraceOptions_1262_ = lean_ctor_get(v_toCold_1247_, 11);
v___x_1263_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1262_, v_options_1248_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_e_u2081_804_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 0);
v___x_1267_ = v___x_1260_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_val_1258_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_del_object(v___x_1260_);
v___x_1269_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4);
v___x_1270_ = l_Lean_MessageData_ofExpr(v_e_u2081_804_);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1263_, v___x_1271_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1272_, 0);
lean_dec(v_unused_1280_);
v___x_1274_ = v___x_1272_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v___x_1272_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v_val_1258_);
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_val_1258_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_val_1258_);
v_a_1281_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1272_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1272_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1290_; lean_object* v_transientCache_1291_; lean_object* v___x_1292_; 
lean_dec(v___x_1246_);
v___x_1290_ = lean_st_ref_get(v___y_1237_);
v_transientCache_1291_ = lean_ctor_get(v___x_1290_, 2);
lean_inc_ref(v_transientCache_1291_);
lean_dec(v___x_1290_);
v___x_1292_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_transientCache_1291_, v_e_u2081_804_);
lean_dec_ref(v_transientCache_1291_);
if (lean_obj_tag(v___x_1292_) == 1)
{
lean_object* v_toCold_1293_; lean_object* v_options_1294_; uint8_t v_hasTrace_1295_; 
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec(v___y_1233_);
v_toCold_1293_ = lean_ctor_get(v___y_1242_, 0);
v_options_1294_ = lean_ctor_get(v_toCold_1293_, 2);
v_hasTrace_1295_ = lean_ctor_get_uint8(v_options_1294_, sizeof(void*)*1);
if (v_hasTrace_1295_ == 0)
{
lean_object* v_val_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_e_u2081_804_);
v_val_1296_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1292_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_val_1296_);
lean_dec(v___x_1292_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 0);
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_val_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v_val_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1335_; 
v_val_1304_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1306_ = v___x_1292_;
v_isShared_1307_ = v_isSharedCheck_1335_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_val_1304_);
lean_dec(v___x_1292_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1335_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v_inheritedTraceOptions_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_inheritedTraceOptions_1308_ = lean_ctor_get(v_toCold_1293_, 11);
v___x_1309_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1310_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_1311_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1308_, v_options_1294_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_e_u2081_804_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 0);
v___x_1313_ = v___x_1306_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_val_1304_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_del_object(v___x_1306_);
v___x_1315_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6);
v___x_1316_ = l_Lean_MessageData_ofExpr(v_e_u2081_804_);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_1309_, v___x_1317_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v___x_1318_, 0);
lean_dec(v_unused_1326_);
v___x_1320_ = v___x_1318_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_dec(v___x_1318_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v_val_1304_);
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_val_1304_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_val_1304_);
v_a_1327_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1318_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1318_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
lean_dec(v___x_1292_);
v___x_1336_ = lean_nat_add(v___y_1233_, v___y_1234_);
lean_dec(v___y_1233_);
v___x_1337_ = lean_unsigned_to_nat(1000u);
v___x_1338_ = lean_nat_mod(v___x_1336_, v___x_1337_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = lean_nat_dec_eq(v___x_1338_, v___x_1339_);
lean_dec(v___x_1338_);
if (v___x_1340_ == 0)
{
v___y_1124_ = v___x_1336_;
v___y_1125_ = v___y_1235_;
v___y_1126_ = v___y_1236_;
v___y_1127_ = v___y_1237_;
v___y_1128_ = v___y_1238_;
v___y_1129_ = v___y_1239_;
v___y_1130_ = v___y_1240_;
v___y_1131_ = v___y_1241_;
v___y_1132_ = v___y_1242_;
v___y_1133_ = v___y_1243_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_));
v___x_1342_ = l_Lean_Core_checkSystem(v___x_1341_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_dec_ref_known(v___x_1342_, 1);
v___y_1124_ = v___x_1336_;
v___y_1125_ = v___y_1235_;
v___y_1126_ = v___y_1236_;
v___y_1127_ = v___y_1237_;
v___y_1128_ = v___y_1238_;
v___y_1129_ = v___y_1239_;
v___y_1130_ = v___y_1240_;
v___y_1131_ = v___y_1241_;
v___y_1132_ = v___y_1242_;
v___y_1133_ = v___y_1243_;
goto v___jp_1123_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v___x_1336_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v_e_u2081_804_);
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
}
}
}
v___jp_1351_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = lean_unsigned_to_nat(1u);
v___x_1353_ = lean_nat_add(v_currRecDepth_1113_, v___x_1352_);
lean_dec(v_currRecDepth_1113_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___x_1353_);
v___x_1355_ = v___x_1120_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_toCold_1112_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_ref_1114_);
lean_ctor_set_uint16(v_reuseFailAlloc_1380_, sizeof(void*)*3, v_optionFlags_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, sizeof(void*)*3 + 2, v_suppressElabErrors_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, sizeof(void*)*3 + 3, v_checkDeprecated_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, sizeof(void*)*3 + 4, v_isRecordingDeps_1118_);
v___x_1355_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; lean_object* v_numSteps_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_st_ref_get(v_a_807_);
v_numSteps_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_numSteps_1357_);
lean_dec(v___x_1356_);
v___x_1358_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_806_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v_maxSteps_1360_; uint8_t v___x_1361_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v_maxSteps_1360_ = lean_ctor_get(v_a_1359_, 0);
lean_inc(v_maxSteps_1360_);
lean_dec(v_a_1359_);
v___x_1361_ = lean_nat_dec_le(v_maxSteps_1360_, v_numSteps_1357_);
lean_dec(v_maxSteps_1360_);
if (v___x_1361_ == 0)
{
v___y_1233_ = v_numSteps_1357_;
v___y_1234_ = v___x_1352_;
v___y_1235_ = v_a_805_;
v___y_1236_ = v_a_806_;
v___y_1237_ = v_a_807_;
v___y_1238_ = v_a_808_;
v___y_1239_ = v_a_809_;
v___y_1240_ = v_a_810_;
v___y_1241_ = v_a_811_;
v___y_1242_ = v___x_1355_;
v___y_1243_ = v_a_813_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_numSteps_1357_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_e_u2081_804_);
v___x_1362_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8);
v___x_1363_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_1362_, v_a_810_, v_a_811_, v___x_1355_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v___x_1355_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_numSteps_1357_);
lean_dec_ref(v___x_1355_);
lean_dec(v_a_813_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_e_u2081_804_);
v_a_1372_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1358_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1358_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* v_e_u2081_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = lean_sym_simp(v_e_u2081_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* v_00_u03b2_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_1399_, v_x_1400_, v_x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* v_00_u03b2_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_1404_, v_x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* v_00_u03b2_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_1407_, v_x_1408_, v_x_1409_);
lean_dec_ref(v_x_1409_);
lean_dec_ref(v_x_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* v_cls_1411_, lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_1411_, v_msg_1412_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* v_cls_1424_, lean_object* v_msg_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_1424_, v_msg_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* v_00_u03b2_1437_, lean_object* v_x_1438_, size_t v_x_1439_, size_t v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_1438_, v_x_1439_, v_x_1440_, v_x_1441_, v_x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
size_t v_x_113611__boxed_1450_; size_t v_x_113612__boxed_1451_; lean_object* v_res_1452_; 
v_x_113611__boxed_1450_ = lean_unbox_usize(v_x_1446_);
lean_dec(v_x_1446_);
v_x_113612__boxed_1451_ = lean_unbox_usize(v_x_1447_);
lean_dec(v_x_1447_);
v_res_1452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_1444_, v_x_1445_, v_x_113611__boxed_1450_, v_x_113612__boxed_1451_, v_x_1448_, v_x_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* v_00_u03b2_1453_, lean_object* v_x_1454_, size_t v_x_1455_, lean_object* v_x_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_1454_, v_x_1455_, v_x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_){
_start:
{
size_t v_x_113628__boxed_1462_; lean_object* v_res_1463_; 
v_x_113628__boxed_1462_ = lean_unbox_usize(v_x_1460_);
lean_dec(v_x_1460_);
v_res_1463_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_1458_, v_x_1459_, v_x_113628__boxed_1462_, v_x_1461_);
lean_dec_ref(v_x_1461_);
lean_dec_ref(v_x_1459_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1464_, lean_object* v_n_1465_, lean_object* v_k_1466_, lean_object* v_v_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v_n_1465_, v_k_1466_, v_v_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1469_, size_t v_depth_1470_, lean_object* v_keys_1471_, lean_object* v_vals_1472_, lean_object* v_heq_1473_, lean_object* v_i_1474_, lean_object* v_entries_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_1470_, v_keys_1471_, v_vals_1472_, v_i_1474_, v_entries_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1477_, lean_object* v_depth_1478_, lean_object* v_keys_1479_, lean_object* v_vals_1480_, lean_object* v_heq_1481_, lean_object* v_i_1482_, lean_object* v_entries_1483_){
_start:
{
size_t v_depth_boxed_1484_; lean_object* v_res_1485_; 
v_depth_boxed_1484_ = lean_unbox_usize(v_depth_1478_);
lean_dec(v_depth_1478_);
v_res_1485_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(v_00_u03b2_1477_, v_depth_boxed_1484_, v_keys_1479_, v_vals_1480_, v_heq_1481_, v_i_1482_, v_entries_1483_);
lean_dec_ref(v_vals_1480_);
lean_dec_ref(v_keys_1479_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1486_, lean_object* v_keys_1487_, lean_object* v_vals_1488_, lean_object* v_heq_1489_, lean_object* v_i_1490_, lean_object* v_k_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1487_, v_vals_1488_, v_i_1490_, v_k_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1493_, lean_object* v_keys_1494_, lean_object* v_vals_1495_, lean_object* v_heq_1496_, lean_object* v_i_1497_, lean_object* v_k_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(v_00_u03b2_1493_, v_keys_1494_, v_vals_1495_, v_heq_1496_, v_i_1497_, v_k_1498_);
lean_dec_ref(v_k_1498_);
lean_dec_ref(v_vals_1495_);
lean_dec_ref(v_keys_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1501_, v_x_1502_, v_x_1503_, v_x_1504_);
return v___x_1505_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
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
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
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
