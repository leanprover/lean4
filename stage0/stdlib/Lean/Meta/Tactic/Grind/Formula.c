// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Formula
// Imports: public import Lean.Meta.Basic public import Lean.Util.MonadCache import Init.Grind.Lemmas import Lean.Data.LBool
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
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
static const lean_ctor_object l_Lean_Meta_Grind_Formula_instInhabitedAdmission_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_Formula_instInhabitedAdmission_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Formula_instInhabitedAdmission_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Formula_instInhabitedAdmission_default = (const lean_object*)&l_Lean_Meta_Grind_Formula_instInhabitedAdmission_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_instInhabitedAdmission = (const lean_object*)&l_Lean_Meta_Grind_Formula_instInhabitedAdmission_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__6(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__4(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__12(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unsupported atom in formula proof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "and_imp_of_right"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 113, 184, 29, 86, 157, 229, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "and_imp_of_left"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 65, 8, 245, 192, 181, 79, 190)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "or_imp_of_imp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 236, 175, 244, 29, 176, 71, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__0(lean_object* v___x_6_, lean_object* v___x_7_, lean_object* v_e_8_, lean_object* v___x_9_, lean_object* v_s_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_box(0);
v___x_12_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_6_, v___x_7_, v_s_10_, v_e_8_, v___x_9_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_11_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__1(lean_object* v_toApplicative_14_, lean_object* v___x_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_toPure_17_; lean_object* v___x_18_; 
v_toPure_17_ = lean_ctor_get(v_toApplicative_14_, 1);
lean_inc(v_toPure_17_);
lean_dec_ref(v_toApplicative_14_);
v___x_18_ = lean_apply_2(v_toPure_17_, lean_box(0), v___x_15_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__2(lean_object* v___x_19_, lean_object* v___x_20_, lean_object* v_e_21_, lean_object* v_toApplicative_22_, lean_object* v_inst_23_, lean_object* v_toBind_24_, uint8_t v_supported_25_, lean_object* v___y_26_){
_start:
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_27_ = 2;
v___x_28_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_28_, 0, v_supported_25_);
lean_ctor_set_uint8(v___x_28_, 1, v___x_27_);
lean_inc_ref(v___x_28_);
v___f_29_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__0), 5, 4);
lean_closure_set(v___f_29_, 0, v___x_19_);
lean_closure_set(v___f_29_, 1, v___x_20_);
lean_closure_set(v___f_29_, 2, v_e_21_);
lean_closure_set(v___f_29_, 3, v___x_28_);
v___f_30_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__1), 3, 2);
lean_closure_set(v___f_30_, 0, v_toApplicative_22_);
lean_closure_set(v___f_30_, 1, v___x_28_);
lean_inc(v___y_26_);
v___x_31_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_31_, 0, lean_box(0));
lean_closure_set(v___x_31_, 1, lean_box(0));
lean_closure_set(v___x_31_, 2, lean_box(0));
lean_closure_set(v___x_31_, 3, v___y_26_);
lean_closure_set(v___x_31_, 4, v___f_29_);
v___x_32_ = lean_apply_2(v_inst_23_, lean_box(0), v___x_31_);
v___x_33_ = lean_apply_4(v_toBind_24_, lean_box(0), lean_box(0), v___x_32_, v___f_30_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__2___boxed(lean_object* v___x_34_, lean_object* v___x_35_, lean_object* v_e_36_, lean_object* v_toApplicative_37_, lean_object* v_inst_38_, lean_object* v_toBind_39_, lean_object* v_supported_40_, lean_object* v___y_41_){
_start:
{
uint8_t v_supported_boxed_42_; lean_object* v_res_43_; 
v_supported_boxed_42_ = lean_unbox(v_supported_40_);
v_res_43_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__2(v___x_34_, v___x_35_, v_e_36_, v_toApplicative_37_, v_inst_38_, v_toBind_39_, v_supported_boxed_42_, v___y_41_);
lean_dec(v___y_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__3(lean_object* v___f_44_, lean_object* v_a_45_, uint8_t v_a_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_box(v_a_46_);
lean_inc(v_a_45_);
v___x_48_ = lean_apply_2(v___f_44_, v___x_47_, v_a_45_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__3___boxed(lean_object* v___f_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
uint8_t v_a_boxed_52_; lean_object* v_res_53_; 
v_a_boxed_52_ = lean_unbox(v_a_51_);
v_res_53_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__3(v___f_49_, v_a_50_, v_a_boxed_52_);
lean_dec(v_a_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__5(lean_object* v_toApplicative_54_, lean_object* v_toBind_55_, lean_object* v___f_56_, lean_object* v_a_57_){
_start:
{
uint8_t v_supported_58_; lean_object* v_toPure_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_supported_58_ = lean_ctor_get_uint8(v_a_57_, 0);
v_toPure_59_ = lean_ctor_get(v_toApplicative_54_, 1);
lean_inc(v_toPure_59_);
lean_dec_ref(v_toApplicative_54_);
v___x_60_ = lean_box(v_supported_58_);
v___x_61_ = lean_apply_2(v_toPure_59_, lean_box(0), v___x_60_);
v___x_62_ = lean_apply_4(v_toBind_55_, lean_box(0), lean_box(0), v___x_61_, v___f_56_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__5___boxed(lean_object* v_toApplicative_63_, lean_object* v_toBind_64_, lean_object* v___f_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__5(v_toApplicative_63_, v_toBind_64_, v___f_65_, v_a_66_);
lean_dec_ref(v_a_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__6(uint8_t v_a_68_, uint8_t v_supported_69_, lean_object* v___x_70_, lean_object* v___x_71_, lean_object* v_c_72_, lean_object* v_s_73_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = lean_box(0);
v___x_75_ = l_Lean_Bool_toLBool(v_a_68_);
v___x_76_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_76_, 0, v_supported_69_);
lean_ctor_set_uint8(v___x_76_, 1, v___x_75_);
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_70_, v___x_71_, v_s_73_, v_c_72_, v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_74_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__6___boxed(lean_object* v_a_79_, lean_object* v_supported_80_, lean_object* v___x_81_, lean_object* v___x_82_, lean_object* v_c_83_, lean_object* v_s_84_){
_start:
{
uint8_t v_a_boxed_85_; uint8_t v_supported_boxed_86_; lean_object* v_res_87_; 
v_a_boxed_85_ = lean_unbox(v_a_79_);
v_supported_boxed_86_ = lean_unbox(v_supported_80_);
v_res_87_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__6(v_a_boxed_85_, v_supported_boxed_86_, v___x_81_, v___x_82_, v_c_83_, v_s_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__4(lean_object* v_toApplicative_88_, uint8_t v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_toPure_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_toPure_91_ = lean_ctor_get(v_toApplicative_88_, 1);
lean_inc(v_toPure_91_);
lean_dec_ref(v_toApplicative_88_);
v___x_92_ = lean_box(v_a_89_);
v___x_93_ = lean_apply_2(v_toPure_91_, lean_box(0), v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__4___boxed(lean_object* v_toApplicative_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
uint8_t v_a_boxed_97_; lean_object* v_res_98_; 
v_a_boxed_97_ = lean_unbox(v_a_95_);
v_res_98_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__4(v_toApplicative_94_, v_a_boxed_97_, v_a_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__7(uint8_t v_supported_99_, lean_object* v___x_100_, lean_object* v___x_101_, lean_object* v_c_102_, lean_object* v_toApplicative_103_, lean_object* v___y_104_, lean_object* v_inst_105_, lean_object* v_toBind_106_, uint8_t v_a_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_108_ = lean_box(v_a_107_);
v___x_109_ = lean_box(v_supported_99_);
v___f_110_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__6___boxed), 6, 5);
lean_closure_set(v___f_110_, 0, v___x_108_);
lean_closure_set(v___f_110_, 1, v___x_109_);
lean_closure_set(v___f_110_, 2, v___x_100_);
lean_closure_set(v___f_110_, 3, v___x_101_);
lean_closure_set(v___f_110_, 4, v_c_102_);
v___x_111_ = lean_box(v_a_107_);
v___f_112_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_112_, 0, v_toApplicative_103_);
lean_closure_set(v___f_112_, 1, v___x_111_);
lean_inc(v___y_104_);
v___x_113_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_113_, 0, lean_box(0));
lean_closure_set(v___x_113_, 1, lean_box(0));
lean_closure_set(v___x_113_, 2, lean_box(0));
lean_closure_set(v___x_113_, 3, v___y_104_);
lean_closure_set(v___x_113_, 4, v___f_110_);
v___x_114_ = lean_apply_2(v_inst_105_, lean_box(0), v___x_113_);
v___x_115_ = lean_apply_4(v_toBind_106_, lean_box(0), lean_box(0), v___x_114_, v___f_112_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__7___boxed(lean_object* v_supported_116_, lean_object* v___x_117_, lean_object* v___x_118_, lean_object* v_c_119_, lean_object* v_toApplicative_120_, lean_object* v___y_121_, lean_object* v_inst_122_, lean_object* v_toBind_123_, lean_object* v_a_124_){
_start:
{
uint8_t v_supported_boxed_125_; uint8_t v_a_boxed_126_; lean_object* v_res_127_; 
v_supported_boxed_125_ = lean_unbox(v_supported_116_);
v_a_boxed_126_ = lean_unbox(v_a_124_);
v_res_127_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__7(v_supported_boxed_125_, v___x_117_, v___x_118_, v_c_119_, v_toApplicative_120_, v___y_121_, v_inst_122_, v_toBind_123_, v_a_boxed_126_);
lean_dec(v___y_121_);
return v_res_127_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__8(lean_object* v___x_128_, lean_object* v___x_129_, lean_object* v_a_130_, lean_object* v_sub_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_128_, v___x_129_, v_a_130_, v_sub_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
else
{
lean_object* v_val_134_; uint8_t v_supported_135_; 
v_val_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v___x_132_, 1);
v_supported_135_ = lean_ctor_get_uint8(v_val_134_, 0);
lean_dec(v_val_134_);
return v_supported_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__8___boxed(lean_object* v___x_136_, lean_object* v___x_137_, lean_object* v_a_138_, lean_object* v_sub_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__8(v___x_136_, v___x_137_, v_a_138_, v_sub_139_);
lean_dec_ref(v_a_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__9(lean_object* v___x_142_, lean_object* v___x_143_, lean_object* v_admitConjunct_144_, lean_object* v_c_145_, lean_object* v_toBind_146_, lean_object* v___f_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___f_149_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_149_, 0, v___x_142_);
lean_closure_set(v___f_149_, 1, v___x_143_);
lean_closure_set(v___f_149_, 2, v_a_148_);
v___x_150_ = lean_apply_2(v_admitConjunct_144_, v_c_145_, v___f_149_);
v___x_151_ = lean_apply_4(v_toBind_146_, lean_box(0), lean_box(0), v___x_150_, v___f_147_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__10(lean_object* v_toApplicative_152_, lean_object* v___x_153_, lean_object* v___x_154_, lean_object* v_c_155_, lean_object* v___y_156_, lean_object* v_inst_157_, lean_object* v_toBind_158_, lean_object* v_admitConjunct_159_, lean_object* v_a_160_){
_start:
{
uint8_t v_supported_161_; 
v_supported_161_ = lean_ctor_get_uint8(v_a_160_, 0);
if (v_supported_161_ == 0)
{
lean_object* v_toPure_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_admitConjunct_159_);
lean_dec(v_toBind_158_);
lean_dec(v_inst_157_);
lean_dec_ref(v_c_155_);
lean_dec_ref(v___x_154_);
lean_dec_ref(v___x_153_);
v_toPure_162_ = lean_ctor_get(v_toApplicative_152_, 1);
lean_inc(v_toPure_162_);
lean_dec_ref(v_toApplicative_152_);
v___x_163_ = lean_box(v_supported_161_);
v___x_164_ = lean_apply_2(v_toPure_162_, lean_box(0), v___x_163_);
return v___x_164_;
}
else
{
uint8_t v_conjunct_165_; 
v_conjunct_165_ = lean_ctor_get_uint8(v_a_160_, 1);
switch(v_conjunct_165_)
{
case 0:
{
lean_object* v_toPure_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_admitConjunct_159_);
lean_dec(v_toBind_158_);
lean_dec(v_inst_157_);
lean_dec_ref(v_c_155_);
lean_dec_ref(v___x_154_);
lean_dec_ref(v___x_153_);
v_toPure_166_ = lean_ctor_get(v_toApplicative_152_, 1);
lean_inc(v_toPure_166_);
lean_dec_ref(v_toApplicative_152_);
v___x_167_ = 0;
v___x_168_ = lean_box(v___x_167_);
v___x_169_ = lean_apply_2(v_toPure_166_, lean_box(0), v___x_168_);
return v___x_169_;
}
case 1:
{
lean_object* v_toPure_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_admitConjunct_159_);
lean_dec(v_toBind_158_);
lean_dec(v_inst_157_);
lean_dec_ref(v_c_155_);
lean_dec_ref(v___x_154_);
lean_dec_ref(v___x_153_);
v_toPure_170_ = lean_ctor_get(v_toApplicative_152_, 1);
lean_inc(v_toPure_170_);
lean_dec_ref(v_toApplicative_152_);
v___x_171_ = lean_box(v_supported_161_);
v___x_172_ = lean_apply_2(v_toPure_170_, lean_box(0), v___x_171_);
return v___x_172_;
}
default: 
{
lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_173_ = lean_box(v_supported_161_);
lean_inc_n(v_toBind_158_, 2);
lean_inc(v_inst_157_);
lean_inc_n(v___y_156_, 2);
lean_inc_ref(v_c_155_);
lean_inc_ref(v___x_154_);
lean_inc_ref(v___x_153_);
v___f_174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__7___boxed), 9, 8);
lean_closure_set(v___f_174_, 0, v___x_173_);
lean_closure_set(v___f_174_, 1, v___x_153_);
lean_closure_set(v___f_174_, 2, v___x_154_);
lean_closure_set(v___f_174_, 3, v_c_155_);
lean_closure_set(v___f_174_, 4, v_toApplicative_152_);
lean_closure_set(v___f_174_, 5, v___y_156_);
lean_closure_set(v___f_174_, 6, v_inst_157_);
lean_closure_set(v___f_174_, 7, v_toBind_158_);
v___f_175_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__9), 7, 6);
lean_closure_set(v___f_175_, 0, v___x_153_);
lean_closure_set(v___f_175_, 1, v___x_154_);
lean_closure_set(v___f_175_, 2, v_admitConjunct_159_);
lean_closure_set(v___f_175_, 3, v_c_155_);
lean_closure_set(v___f_175_, 4, v_toBind_158_);
lean_closure_set(v___f_175_, 5, v___f_174_);
v___x_176_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_176_, 0, lean_box(0));
lean_closure_set(v___x_176_, 1, lean_box(0));
lean_closure_set(v___x_176_, 2, v___y_156_);
v___x_177_ = lean_apply_2(v_inst_157_, lean_box(0), v___x_176_);
v___x_178_ = lean_apply_4(v_toBind_158_, lean_box(0), lean_box(0), v___x_177_, v___f_175_);
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__10___boxed(lean_object* v_toApplicative_179_, lean_object* v___x_180_, lean_object* v___x_181_, lean_object* v_c_182_, lean_object* v___y_183_, lean_object* v_inst_184_, lean_object* v_toBind_185_, lean_object* v_admitConjunct_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__10(v_toApplicative_179_, v___x_180_, v___x_181_, v_c_182_, v___y_183_, v_inst_184_, v_toBind_185_, v_admitConjunct_186_, v_a_187_);
lean_dec_ref(v_a_187_);
lean_dec(v___y_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__13(lean_object* v_toApplicative_189_, lean_object* v_toBind_190_, lean_object* v___f_191_, uint8_t v_a_192_, uint8_t v_a_193_){
_start:
{
uint8_t v___y_195_; 
if (v_a_192_ == 0)
{
v___y_195_ = v_a_193_;
goto v___jp_194_;
}
else
{
v___y_195_ = v_a_192_;
goto v___jp_194_;
}
v___jp_194_:
{
lean_object* v_toPure_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_toPure_196_ = lean_ctor_get(v_toApplicative_189_, 1);
lean_inc(v_toPure_196_);
lean_dec_ref(v_toApplicative_189_);
v___x_197_ = lean_box(v___y_195_);
v___x_198_ = lean_apply_2(v_toPure_196_, lean_box(0), v___x_197_);
v___x_199_ = lean_apply_4(v_toBind_190_, lean_box(0), lean_box(0), v___x_198_, v___f_191_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__13___boxed(lean_object* v_toApplicative_200_, lean_object* v_toBind_201_, lean_object* v___f_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
uint8_t v_a_boxed_205_; uint8_t v_a_boxed_206_; lean_object* v_res_207_; 
v_a_boxed_205_ = lean_unbox(v_a_203_);
v_a_boxed_206_ = lean_unbox(v_a_204_);
v_res_207_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__13(v_toApplicative_200_, v_toBind_201_, v___f_202_, v_a_boxed_205_, v_a_boxed_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__14(lean_object* v_toApplicative_208_, lean_object* v_toBind_209_, lean_object* v___f_210_, lean_object* v___f_211_, lean_object* v_arg_212_, lean_object* v_a_213_, uint8_t v_a_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = lean_box(v_a_214_);
lean_inc(v_toBind_209_);
v___f_216_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__13___boxed), 5, 4);
lean_closure_set(v___f_216_, 0, v_toApplicative_208_);
lean_closure_set(v___f_216_, 1, v_toBind_209_);
lean_closure_set(v___f_216_, 2, v___f_210_);
lean_closure_set(v___f_216_, 3, v___x_215_);
lean_inc(v_a_213_);
v___x_217_ = lean_apply_2(v___f_211_, v_arg_212_, v_a_213_);
v___x_218_ = lean_apply_4(v_toBind_209_, lean_box(0), lean_box(0), v___x_217_, v___f_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__14___boxed(lean_object* v_toApplicative_219_, lean_object* v_toBind_220_, lean_object* v___f_221_, lean_object* v___f_222_, lean_object* v_arg_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
uint8_t v_a_boxed_226_; lean_object* v_res_227_; 
v_a_boxed_226_ = lean_unbox(v_a_225_);
v_res_227_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__14(v_toApplicative_219_, v_toBind_220_, v___f_221_, v___f_222_, v_arg_223_, v_a_224_, v_a_boxed_226_);
lean_dec(v_a_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__12(lean_object* v___f_228_, lean_object* v___y_229_, uint8_t v_a_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_box(v_a_230_);
lean_inc(v___y_229_);
v___x_232_ = lean_apply_2(v___f_228_, v___x_231_, v___y_229_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__12___boxed(lean_object* v___f_233_, lean_object* v___y_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_a_boxed_236_; lean_object* v_res_237_; 
v_a_boxed_236_ = lean_unbox(v_a_235_);
v_res_237_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__12(v___f_233_, v___y_234_, v_a_boxed_236_);
lean_dec(v___y_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__11___boxed(lean_object* v_toApplicative_240_, lean_object* v___x_241_, lean_object* v___x_242_, lean_object* v_inst_243_, lean_object* v_toBind_244_, lean_object* v_admitConjunct_245_, lean_object* v_inst_246_, lean_object* v_canContribute_247_, lean_object* v_c_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__11(v_toApplicative_240_, v___x_241_, v___x_242_, v_inst_243_, v_toBind_244_, v_admitConjunct_245_, v_inst_246_, v_canContribute_247_, v_c_248_, v___y_249_);
lean_dec(v___y_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__15(lean_object* v_toApplicative_251_, lean_object* v_toBind_252_, lean_object* v___f_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_canContribute_256_, lean_object* v_admitConjunct_257_, lean_object* v_snd_258_, lean_object* v_a_259_, lean_object* v___f_260_, lean_object* v_a_261_){
_start:
{
uint8_t v_supported_262_; 
v_supported_262_ = lean_ctor_get_uint8(v_a_261_, 0);
if (v_supported_262_ == 0)
{
lean_object* v_toPure_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v___f_260_);
lean_dec_ref(v_snd_258_);
lean_dec(v_admitConjunct_257_);
lean_dec_ref(v_canContribute_256_);
lean_dec(v_inst_255_);
lean_dec_ref(v_inst_254_);
v_toPure_263_ = lean_ctor_get(v_toApplicative_251_, 1);
lean_inc(v_toPure_263_);
lean_dec_ref(v_toApplicative_251_);
v___x_264_ = lean_box(v_supported_262_);
v___x_265_ = lean_apply_2(v_toPure_263_, lean_box(0), v___x_264_);
v___x_266_ = lean_apply_4(v_toBind_252_, lean_box(0), lean_box(0), v___x_265_, v___f_253_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v___f_253_);
lean_dec_ref(v_toApplicative_251_);
v___x_267_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg(v_inst_254_, v_inst_255_, v_canContribute_256_, v_admitConjunct_257_, v_snd_258_, v_a_259_);
v___x_268_ = lean_apply_4(v_toBind_252_, lean_box(0), lean_box(0), v___x_267_, v___f_260_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__15___boxed(lean_object* v_toApplicative_269_, lean_object* v_toBind_270_, lean_object* v___f_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_canContribute_274_, lean_object* v_admitConjunct_275_, lean_object* v_snd_276_, lean_object* v_a_277_, lean_object* v___f_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__15(v_toApplicative_269_, v_toBind_270_, v___f_271_, v_inst_272_, v_inst_273_, v_canContribute_274_, v_admitConjunct_275_, v_snd_276_, v_a_277_, v___f_278_, v_a_279_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16(lean_object* v___x_287_, lean_object* v___x_288_, lean_object* v_e_289_, lean_object* v_toApplicative_290_, lean_object* v___f_291_, lean_object* v_canContribute_292_, lean_object* v_toBind_293_, lean_object* v_a_294_, lean_object* v___f_295_, lean_object* v___f_296_, lean_object* v___f_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_admitConjunct_300_, lean_object* v___f_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___y_304_; lean_object* v_fst_311_; lean_object* v_snd_312_; lean_object* v___x_316_; 
lean_inc_ref(v_e_289_);
v___x_316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_287_, v___x_288_, v_a_302_, v_e_289_);
if (lean_obj_tag(v___x_316_) == 1)
{
lean_object* v_val_317_; lean_object* v_toPure_318_; lean_object* v___x_319_; 
lean_dec(v___f_301_);
lean_dec(v_admitConjunct_300_);
lean_dec(v_inst_299_);
lean_dec_ref(v_inst_298_);
lean_dec(v___f_297_);
lean_dec(v___f_296_);
lean_dec(v___f_295_);
lean_dec(v_toBind_293_);
lean_dec_ref(v_canContribute_292_);
lean_dec(v___f_291_);
lean_dec_ref(v_e_289_);
v_val_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v___x_316_, 1);
v_toPure_318_ = lean_ctor_get(v_toApplicative_290_, 1);
lean_inc(v_toPure_318_);
lean_dec_ref(v_toApplicative_290_);
v___x_319_ = lean_apply_2(v_toPure_318_, lean_box(0), v_val_317_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; uint8_t v___x_321_; 
lean_dec(v___x_316_);
v___x_320_ = l_Lean_Expr_cleanupAnnotations(v_e_289_);
v___x_321_ = l_Lean_Expr_isApp(v___x_320_);
if (v___x_321_ == 0)
{
lean_dec_ref(v___x_320_);
lean_dec(v___f_301_);
lean_dec(v_admitConjunct_300_);
lean_dec(v_inst_299_);
lean_dec_ref(v_inst_298_);
lean_dec(v___f_297_);
lean_dec(v___f_296_);
lean_dec(v___f_295_);
v___y_304_ = v_a_294_;
goto v___jp_303_;
}
else
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_320_);
v___x_323_ = l_Lean_Expr_isApp(v___x_322_);
if (v___x_323_ == 0)
{
lean_dec_ref(v___x_322_);
lean_dec_ref(v___x_320_);
lean_dec(v___f_301_);
lean_dec(v_admitConjunct_300_);
lean_dec(v_inst_299_);
lean_dec_ref(v_inst_298_);
lean_dec(v___f_297_);
lean_dec(v___f_296_);
lean_dec(v___f_295_);
v___y_304_ = v_a_294_;
goto v___jp_303_;
}
else
{
lean_object* v_arg_324_; lean_object* v_arg_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_arg_324_ = lean_ctor_get(v___x_320_, 1);
lean_inc_ref(v_arg_324_);
lean_dec_ref(v___x_320_);
v_arg_325_ = lean_ctor_get(v___x_322_, 1);
lean_inc_ref(v_arg_325_);
v___x_326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_322_);
lean_dec_ref(v___x_322_);
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__1));
v___x_328_ = l_Lean_Expr_isConstOf(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
lean_dec(v___f_301_);
lean_dec(v_admitConjunct_300_);
lean_dec(v_inst_299_);
lean_dec_ref(v_inst_298_);
lean_dec(v___f_297_);
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__3));
v___x_330_ = l_Lean_Expr_isConstOf(v___x_326_, v___x_329_);
lean_dec_ref(v___x_326_);
if (v___x_330_ == 0)
{
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_324_);
lean_dec(v___f_296_);
lean_dec(v___f_295_);
v___y_304_ = v_a_294_;
goto v___jp_303_;
}
else
{
lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec_ref(v_canContribute_292_);
lean_dec(v___f_291_);
lean_dec_ref(v_e_289_);
lean_inc_n(v_a_294_, 2);
lean_inc(v___f_296_);
lean_inc(v_toBind_293_);
v___f_331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__14___boxed), 7, 6);
lean_closure_set(v___f_331_, 0, v_toApplicative_290_);
lean_closure_set(v___f_331_, 1, v_toBind_293_);
lean_closure_set(v___f_331_, 2, v___f_295_);
lean_closure_set(v___f_331_, 3, v___f_296_);
lean_closure_set(v___f_331_, 4, v_arg_324_);
lean_closure_set(v___f_331_, 5, v_a_294_);
v___x_332_ = lean_apply_2(v___f_296_, v_arg_325_, v_a_294_);
v___x_333_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v___x_332_, v___f_331_);
return v___x_333_;
}
}
else
{
uint32_t v___x_334_; uint32_t v___x_335_; uint8_t v___x_336_; 
lean_dec_ref(v___x_326_);
lean_dec(v___f_296_);
lean_dec(v___f_295_);
lean_dec(v___f_291_);
lean_dec_ref(v_e_289_);
v___x_334_ = l_Lean_Expr_approxDepth(v_arg_325_);
v___x_335_ = l_Lean_Expr_approxDepth(v_arg_324_);
v___x_336_ = lean_uint32_dec_le(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
v_fst_311_ = v_arg_324_;
v_snd_312_ = v_arg_325_;
goto v___jp_310_;
}
else
{
v_fst_311_ = v_arg_325_;
v_snd_312_ = v_arg_324_;
goto v___jp_310_;
}
}
}
}
}
v___jp_303_:
{
lean_object* v_toPure_305_; lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_toPure_305_ = lean_ctor_get(v_toApplicative_290_, 1);
lean_inc(v_toPure_305_);
lean_dec_ref(v_toApplicative_290_);
lean_inc(v___y_304_);
v___f_306_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__12___boxed), 3, 2);
lean_closure_set(v___f_306_, 0, v___f_291_);
lean_closure_set(v___f_306_, 1, v___y_304_);
v___x_307_ = lean_apply_1(v_canContribute_292_, v_e_289_);
v___x_308_ = lean_apply_2(v_toPure_305_, lean_box(0), v___x_307_);
v___x_309_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v___x_308_, v___f_306_);
return v___x_309_;
}
v___jp_310_:
{
lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_inc(v_a_294_);
lean_inc(v_admitConjunct_300_);
lean_inc_ref(v_canContribute_292_);
lean_inc(v_inst_299_);
lean_inc_ref(v_inst_298_);
lean_inc(v_toBind_293_);
v___f_313_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__15___boxed), 11, 10);
lean_closure_set(v___f_313_, 0, v_toApplicative_290_);
lean_closure_set(v___f_313_, 1, v_toBind_293_);
lean_closure_set(v___f_313_, 2, v___f_297_);
lean_closure_set(v___f_313_, 3, v_inst_298_);
lean_closure_set(v___f_313_, 4, v_inst_299_);
lean_closure_set(v___f_313_, 5, v_canContribute_292_);
lean_closure_set(v___f_313_, 6, v_admitConjunct_300_);
lean_closure_set(v___f_313_, 7, v_snd_312_);
lean_closure_set(v___f_313_, 8, v_a_294_);
lean_closure_set(v___f_313_, 9, v___f_301_);
v___x_314_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg(v_inst_298_, v_inst_299_, v_canContribute_292_, v_admitConjunct_300_, v_fst_311_, v_a_294_);
v___x_315_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v___x_314_, v___f_313_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___boxed(lean_object* v___x_337_, lean_object* v___x_338_, lean_object* v_e_339_, lean_object* v_toApplicative_340_, lean_object* v___f_341_, lean_object* v_canContribute_342_, lean_object* v_toBind_343_, lean_object* v_a_344_, lean_object* v___f_345_, lean_object* v___f_346_, lean_object* v___f_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_admitConjunct_350_, lean_object* v___f_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16(v___x_337_, v___x_338_, v_e_339_, v_toApplicative_340_, v___f_341_, v_canContribute_342_, v_toBind_343_, v_a_344_, v___f_345_, v___f_346_, v___f_347_, v_inst_348_, v_inst_349_, v_admitConjunct_350_, v___f_351_, v_a_352_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_344_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg(lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_canContribute_356_, lean_object* v_admitConjunct_357_, lean_object* v_e_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_toApplicative_360_; lean_object* v_toBind_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___f_366_; lean_object* v___f_367_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_toApplicative_360_ = lean_ctor_get(v_inst_354_, 0);
lean_inc_ref_n(v_toApplicative_360_, 4);
v_toBind_361_ = lean_ctor_get(v_inst_354_, 1);
lean_inc_n(v_toBind_361_, 5);
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__0));
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__1));
lean_inc_n(v_inst_355_, 3);
lean_inc_ref(v_e_358_);
v___f_364_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_364_, 0, v___x_362_);
lean_closure_set(v___f_364_, 1, v___x_363_);
lean_closure_set(v___f_364_, 2, v_e_358_);
lean_closure_set(v___f_364_, 3, v_toApplicative_360_);
lean_closure_set(v___f_364_, 4, v_inst_355_);
lean_closure_set(v___f_364_, 5, v_toBind_361_);
lean_inc_n(v_a_359_, 3);
lean_inc_ref(v___f_364_);
v___f_365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_365_, 0, v___f_364_);
lean_closure_set(v___f_365_, 1, v_a_359_);
lean_inc_ref_n(v___f_365_, 2);
v___f_366_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_366_, 0, v_toApplicative_360_);
lean_closure_set(v___f_366_, 1, v_toBind_361_);
lean_closure_set(v___f_366_, 2, v___f_365_);
lean_inc_ref(v_canContribute_356_);
lean_inc_ref(v_inst_354_);
lean_inc(v_admitConjunct_357_);
v___f_367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__11___boxed), 10, 8);
lean_closure_set(v___f_367_, 0, v_toApplicative_360_);
lean_closure_set(v___f_367_, 1, v___x_362_);
lean_closure_set(v___f_367_, 2, v___x_363_);
lean_closure_set(v___f_367_, 3, v_inst_355_);
lean_closure_set(v___f_367_, 4, v_toBind_361_);
lean_closure_set(v___f_367_, 5, v_admitConjunct_357_);
lean_closure_set(v___f_367_, 6, v_inst_354_);
lean_closure_set(v___f_367_, 7, v_canContribute_356_);
v___f_368_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___boxed), 16, 15);
lean_closure_set(v___f_368_, 0, v___x_362_);
lean_closure_set(v___f_368_, 1, v___x_363_);
lean_closure_set(v___f_368_, 2, v_e_358_);
lean_closure_set(v___f_368_, 3, v_toApplicative_360_);
lean_closure_set(v___f_368_, 4, v___f_364_);
lean_closure_set(v___f_368_, 5, v_canContribute_356_);
lean_closure_set(v___f_368_, 6, v_toBind_361_);
lean_closure_set(v___f_368_, 7, v_a_359_);
lean_closure_set(v___f_368_, 8, v___f_365_);
lean_closure_set(v___f_368_, 9, v___f_367_);
lean_closure_set(v___f_368_, 10, v___f_365_);
lean_closure_set(v___f_368_, 11, v_inst_354_);
lean_closure_set(v___f_368_, 12, v_inst_355_);
lean_closure_set(v___f_368_, 13, v_admitConjunct_357_);
lean_closure_set(v___f_368_, 14, v___f_366_);
v___x_369_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, lean_box(0));
lean_closure_set(v___x_369_, 2, v_a_359_);
v___x_370_ = lean_apply_2(v_inst_355_, lean_box(0), v___x_369_);
v___x_371_ = lean_apply_4(v_toBind_361_, lean_box(0), lean_box(0), v___x_370_, v___f_368_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__11(lean_object* v_toApplicative_372_, lean_object* v___x_373_, lean_object* v___x_374_, lean_object* v_inst_375_, lean_object* v_toBind_376_, lean_object* v_admitConjunct_377_, lean_object* v_inst_378_, lean_object* v_canContribute_379_, lean_object* v_c_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_inc(v_admitConjunct_377_);
lean_inc(v_toBind_376_);
lean_inc(v_inst_375_);
lean_inc(v___y_381_);
lean_inc_ref(v_c_380_);
v___f_382_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__10___boxed), 9, 8);
lean_closure_set(v___f_382_, 0, v_toApplicative_372_);
lean_closure_set(v___f_382_, 1, v___x_373_);
lean_closure_set(v___f_382_, 2, v___x_374_);
lean_closure_set(v___f_382_, 3, v_c_380_);
lean_closure_set(v___f_382_, 4, v___y_381_);
lean_closure_set(v___f_382_, 5, v_inst_375_);
lean_closure_set(v___f_382_, 6, v_toBind_376_);
lean_closure_set(v___f_382_, 7, v_admitConjunct_377_);
v___x_383_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg(v_inst_378_, v_inst_375_, v_canContribute_379_, v_admitConjunct_377_, v_c_380_, v___y_381_);
v___x_384_ = lean_apply_4(v_toBind_376_, lean_box(0), lean_box(0), v___x_383_, v___f_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___boxed(lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_canContribute_387_, lean_object* v_admitConjunct_388_, lean_object* v_e_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg(v_inst_385_, v_inst_386_, v_canContribute_387_, v_admitConjunct_388_, v_e_389_, v_a_390_);
lean_dec(v_a_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect(lean_object* v_m_392_, lean_object* v_00_u03c9_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_canContribute_396_, lean_object* v_admitConjunct_397_, lean_object* v_e_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg(v_inst_394_, v_inst_395_, v_canContribute_396_, v_admitConjunct_397_, v_e_398_, v_a_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___boxed(lean_object* v_m_401_, lean_object* v_00_u03c9_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_canContribute_405_, lean_object* v_admitConjunct_406_, lean_object* v_e_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect(v_m_401_, v_00_u03c9_402_, v_inst_403_, v_inst_404_, v_canContribute_405_, v_admitConjunct_406_, v_e_407_, v_a_408_);
lean_dec(v_a_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__0(lean_object* v_toApplicative_410_, lean_object* v_result_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_toPure_413_; lean_object* v___x_414_; 
v_toPure_413_ = lean_ctor_get(v_toApplicative_410_, 1);
lean_inc(v_toPure_413_);
lean_dec_ref(v_toApplicative_410_);
v___x_414_ = lean_apply_2(v_toPure_413_, lean_box(0), v_result_411_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__0___boxed(lean_object* v_toApplicative_415_, lean_object* v_result_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__0(v_toApplicative_415_, v_result_416_, v___y_417_);
lean_dec(v___y_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__10(lean_object* v_toApplicative_419_, lean_object* v___x_420_, lean_object* v___x_421_, lean_object* v_e_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_toPure_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_toPure_424_ = lean_ctor_get(v_toApplicative_419_, 1);
lean_inc(v_toPure_424_);
lean_dec_ref(v_toApplicative_419_);
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_420_, v___x_421_, v_a_423_, v_e_422_);
v___x_426_ = lean_apply_2(v_toPure_424_, lean_box(0), v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__10___boxed(lean_object* v_toApplicative_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v_e_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__10(v_toApplicative_427_, v___x_428_, v___x_429_, v_e_430_, v_a_431_);
lean_dec_ref(v_a_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__7(lean_object* v_toApplicative_433_, lean_object* v_or_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_toPure_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_toPure_437_ = lean_ctor_get(v_toApplicative_433_, 1);
lean_inc(v_toPure_437_);
lean_dec_ref(v_toApplicative_433_);
v___x_438_ = lean_apply_2(v_or_434_, v_a_435_, v_a_436_);
v___x_439_ = lean_apply_2(v_toPure_437_, lean_box(0), v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__5(lean_object* v_toApplicative_440_, lean_object* v_and_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_toPure_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_toPure_444_ = lean_ctor_get(v_toApplicative_440_, 1);
lean_inc(v_toPure_444_);
lean_dec_ref(v_toApplicative_440_);
v___x_445_ = lean_apply_2(v_and_441_, v_a_442_, v_a_443_);
v___x_446_ = lean_apply_2(v_toPure_444_, lean_box(0), v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__6(lean_object* v_toApplicative_447_, lean_object* v_and_448_, lean_object* v_child_449_, lean_object* v_arg_450_, lean_object* v_a_451_, lean_object* v_toBind_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___f_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___f_454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__5), 4, 3);
lean_closure_set(v___f_454_, 0, v_toApplicative_447_);
lean_closure_set(v___f_454_, 1, v_and_448_);
lean_closure_set(v___f_454_, 2, v_a_453_);
lean_inc(v_a_451_);
v___x_455_ = lean_apply_2(v_child_449_, v_arg_450_, v_a_451_);
v___x_456_ = lean_apply_4(v_toBind_452_, lean_box(0), lean_box(0), v___x_455_, v___f_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__6___boxed(lean_object* v_toApplicative_457_, lean_object* v_and_458_, lean_object* v_child_459_, lean_object* v_arg_460_, lean_object* v_a_461_, lean_object* v_toBind_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__6(v_toApplicative_457_, v_and_458_, v_child_459_, v_arg_460_, v_a_461_, v_toBind_462_, v_a_463_);
lean_dec(v_a_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__3(lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_s_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_465_, v___x_466_, v_s_469_, v_e_467_, v_a_468_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__2(lean_object* v_toApplicative_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_toPure_476_; lean_object* v___x_477_; 
v_toPure_476_ = lean_ctor_get(v_toApplicative_473_, 1);
lean_inc(v_toPure_476_);
lean_dec_ref(v_toApplicative_473_);
v___x_477_ = lean_apply_2(v_toPure_476_, lean_box(0), v_a_474_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__4(lean_object* v_toApplicative_478_, lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v_e_481_, lean_object* v_a_482_, lean_object* v_inst_483_, lean_object* v_toBind_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___f_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_inc(v_a_485_);
v___f_486_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__2), 3, 2);
lean_closure_set(v___f_486_, 0, v_toApplicative_478_);
lean_closure_set(v___f_486_, 1, v_a_485_);
v___f_487_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__3), 5, 4);
lean_closure_set(v___f_487_, 0, v___x_479_);
lean_closure_set(v___f_487_, 1, v___x_480_);
lean_closure_set(v___f_487_, 2, v_e_481_);
lean_closure_set(v___f_487_, 3, v_a_485_);
lean_inc(v_a_482_);
v___x_488_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_488_, 0, lean_box(0));
lean_closure_set(v___x_488_, 1, lean_box(0));
lean_closure_set(v___x_488_, 2, lean_box(0));
lean_closure_set(v___x_488_, 3, v_a_482_);
lean_closure_set(v___x_488_, 4, v___f_487_);
v___x_489_ = lean_apply_2(v_inst_483_, lean_box(0), v___x_488_);
v___x_490_ = lean_apply_4(v_toBind_484_, lean_box(0), lean_box(0), v___x_489_, v___f_486_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__4___boxed(lean_object* v_toApplicative_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v_e_494_, lean_object* v_a_495_, lean_object* v_inst_496_, lean_object* v_toBind_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__4(v_toApplicative_491_, v___x_492_, v___x_493_, v_e_494_, v_a_495_, v_inst_496_, v_toBind_497_, v_a_498_);
lean_dec(v_a_495_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__1___boxed(lean_object* v_skipConjunct_x3f_500_, lean_object* v___f_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_atom_504_, lean_object* v_and_505_, lean_object* v_or_506_, lean_object* v_skip_x3f_507_, lean_object* v_finishOr_x3f_508_, lean_object* v_e_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__1(v_skipConjunct_x3f_500_, v___f_501_, v_inst_502_, v_inst_503_, v_atom_504_, v_and_505_, v_or_506_, v_skip_x3f_507_, v_finishOr_x3f_508_, v_e_509_, v___y_510_);
lean_dec(v___y_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__8(lean_object* v_finishOr_x3f_512_, lean_object* v___f_513_, lean_object* v_a_514_, lean_object* v_toApplicative_515_, lean_object* v_or_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_atom_519_, lean_object* v_and_520_, lean_object* v_skip_x3f_521_, lean_object* v_skipConjunct_x3f_522_, lean_object* v_arg_523_, lean_object* v_toBind_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_526_; 
lean_inc_ref(v_finishOr_x3f_512_);
lean_inc(v_a_525_);
v___x_526_ = lean_apply_1(v_finishOr_x3f_512_, v_a_525_);
if (lean_obj_tag(v___x_526_) == 1)
{
lean_object* v_val_527_; lean_object* v___x_528_; 
lean_dec(v_a_525_);
lean_dec(v_toBind_524_);
lean_dec_ref(v_arg_523_);
lean_dec_ref(v_skipConjunct_x3f_522_);
lean_dec_ref(v_skip_x3f_521_);
lean_dec(v_and_520_);
lean_dec(v_atom_519_);
lean_dec(v_inst_518_);
lean_dec_ref(v_inst_517_);
lean_dec(v_or_516_);
lean_dec_ref(v_toApplicative_515_);
lean_dec_ref(v_finishOr_x3f_512_);
v_val_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v___x_526_, 1);
lean_inc(v_a_514_);
v___x_528_ = lean_apply_2(v___f_513_, v_val_527_, v_a_514_);
return v___x_528_;
}
else
{
lean_object* v___f_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec(v___x_526_);
lean_dec(v___f_513_);
lean_inc(v_or_516_);
v___f_529_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__7), 4, 3);
lean_closure_set(v___f_529_, 0, v_toApplicative_515_);
lean_closure_set(v___f_529_, 1, v_or_516_);
lean_closure_set(v___f_529_, 2, v_a_525_);
v___x_530_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg(v_inst_517_, v_inst_518_, v_atom_519_, v_and_520_, v_or_516_, v_skip_x3f_521_, v_skipConjunct_x3f_522_, v_finishOr_x3f_512_, v_arg_523_, v_a_514_);
v___x_531_ = lean_apply_4(v_toBind_524_, lean_box(0), lean_box(0), v___x_530_, v___f_529_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__8___boxed(lean_object* v_finishOr_x3f_532_, lean_object* v___f_533_, lean_object* v_a_534_, lean_object* v_toApplicative_535_, lean_object* v_or_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_atom_539_, lean_object* v_and_540_, lean_object* v_skip_x3f_541_, lean_object* v_skipConjunct_x3f_542_, lean_object* v_arg_543_, lean_object* v_toBind_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__8(v_finishOr_x3f_532_, v___f_533_, v_a_534_, v_toApplicative_535_, v_or_536_, v_inst_537_, v_inst_538_, v_atom_539_, v_and_540_, v_skip_x3f_541_, v_skipConjunct_x3f_542_, v_arg_543_, v_toBind_544_, v_a_545_);
lean_dec(v_a_534_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__9(lean_object* v_skip_x3f_547_, lean_object* v_e_548_, lean_object* v___f_549_, lean_object* v_a_550_, lean_object* v_toBind_551_, lean_object* v___f_552_, lean_object* v_atom_553_, lean_object* v_toApplicative_554_, lean_object* v_and_555_, lean_object* v_child_556_, lean_object* v_finishOr_x3f_557_, lean_object* v_or_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_skipConjunct_x3f_561_, lean_object* v_a_562_){
_start:
{
if (lean_obj_tag(v_a_562_) == 0)
{
lean_object* v___x_563_; 
lean_inc_ref(v_skip_x3f_547_);
lean_inc_ref(v_e_548_);
v___x_563_ = lean_apply_1(v_skip_x3f_547_, v_e_548_);
if (lean_obj_tag(v___x_563_) == 1)
{
lean_object* v_val_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v_skipConjunct_x3f_561_);
lean_dec(v_inst_560_);
lean_dec_ref(v_inst_559_);
lean_dec(v_or_558_);
lean_dec_ref(v_finishOr_x3f_557_);
lean_dec(v_child_556_);
lean_dec(v_and_555_);
lean_dec_ref(v_toApplicative_554_);
lean_dec(v_atom_553_);
lean_dec_ref(v_e_548_);
lean_dec_ref(v_skip_x3f_547_);
v_val_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v___x_563_, 1);
lean_inc(v_a_550_);
v___x_565_ = lean_apply_2(v___f_549_, v_val_564_, v_a_550_);
v___x_566_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_565_, v___f_552_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; uint8_t v___x_568_; 
lean_dec(v___x_563_);
v___x_567_ = l_Lean_Expr_cleanupAnnotations(v_e_548_);
v___x_568_ = l_Lean_Expr_isApp(v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec_ref(v___x_567_);
lean_dec_ref(v_skipConjunct_x3f_561_);
lean_dec(v_inst_560_);
lean_dec_ref(v_inst_559_);
lean_dec(v_or_558_);
lean_dec_ref(v_finishOr_x3f_557_);
lean_dec(v_child_556_);
lean_dec(v_and_555_);
lean_dec_ref(v_toApplicative_554_);
lean_dec(v___f_549_);
lean_dec_ref(v_skip_x3f_547_);
v___x_569_ = lean_apply_1(v_atom_553_, v_e_548_);
v___x_570_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_569_, v___f_552_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = l_Lean_Expr_appFnCleanup___redArg(v___x_567_);
v___x_572_ = l_Lean_Expr_isApp(v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v___x_571_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v_skipConjunct_x3f_561_);
lean_dec(v_inst_560_);
lean_dec_ref(v_inst_559_);
lean_dec(v_or_558_);
lean_dec_ref(v_finishOr_x3f_557_);
lean_dec(v_child_556_);
lean_dec(v_and_555_);
lean_dec_ref(v_toApplicative_554_);
lean_dec(v___f_549_);
lean_dec_ref(v_skip_x3f_547_);
v___x_573_ = lean_apply_1(v_atom_553_, v_e_548_);
v___x_574_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_573_, v___f_552_);
return v___x_574_;
}
else
{
lean_object* v_arg_575_; lean_object* v_arg_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_arg_575_ = lean_ctor_get(v___x_567_, 1);
lean_inc_ref(v_arg_575_);
lean_dec_ref(v___x_567_);
v_arg_576_ = lean_ctor_get(v___x_571_, 1);
lean_inc_ref(v_arg_576_);
v___x_577_ = l_Lean_Expr_appFnCleanup___redArg(v___x_571_);
lean_dec_ref(v___x_571_);
v___x_578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__1));
v___x_579_ = l_Lean_Expr_isConstOf(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; uint8_t v___x_581_; 
lean_dec_ref(v_skipConjunct_x3f_561_);
lean_dec(v_inst_560_);
lean_dec_ref(v_inst_559_);
lean_dec(v_or_558_);
lean_dec_ref(v_finishOr_x3f_557_);
lean_dec(v___f_549_);
lean_dec_ref(v_skip_x3f_547_);
v___x_580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__3));
v___x_581_ = l_Lean_Expr_isConstOf(v___x_577_, v___x_580_);
lean_dec_ref(v___x_577_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_575_);
lean_dec(v_child_556_);
lean_dec(v_and_555_);
lean_dec_ref(v_toApplicative_554_);
v___x_582_ = lean_apply_1(v_atom_553_, v_e_548_);
v___x_583_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_582_, v___f_552_);
return v___x_583_;
}
else
{
lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_atom_553_);
lean_dec_ref(v_e_548_);
lean_inc_n(v_toBind_551_, 2);
lean_inc_n(v_a_550_, 2);
lean_inc(v_child_556_);
v___f_584_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_584_, 0, v_toApplicative_554_);
lean_closure_set(v___f_584_, 1, v_and_555_);
lean_closure_set(v___f_584_, 2, v_child_556_);
lean_closure_set(v___f_584_, 3, v_arg_575_);
lean_closure_set(v___f_584_, 4, v_a_550_);
lean_closure_set(v___f_584_, 5, v_toBind_551_);
v___x_585_ = lean_apply_2(v_child_556_, v_arg_576_, v_a_550_);
v___x_586_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_585_, v___f_584_);
v___x_587_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_586_, v___f_552_);
return v___x_587_;
}
}
else
{
lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec_ref(v___x_577_);
lean_dec(v_child_556_);
lean_dec_ref(v_e_548_);
lean_inc_n(v_toBind_551_, 2);
lean_inc_ref(v_skipConjunct_x3f_561_);
lean_inc_ref(v_skip_x3f_547_);
lean_inc(v_and_555_);
lean_inc(v_atom_553_);
lean_inc(v_inst_560_);
lean_inc_ref(v_inst_559_);
lean_inc(v_or_558_);
lean_inc(v_a_550_);
lean_inc_ref(v_finishOr_x3f_557_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__8___boxed), 14, 13);
lean_closure_set(v___f_588_, 0, v_finishOr_x3f_557_);
lean_closure_set(v___f_588_, 1, v___f_549_);
lean_closure_set(v___f_588_, 2, v_a_550_);
lean_closure_set(v___f_588_, 3, v_toApplicative_554_);
lean_closure_set(v___f_588_, 4, v_or_558_);
lean_closure_set(v___f_588_, 5, v_inst_559_);
lean_closure_set(v___f_588_, 6, v_inst_560_);
lean_closure_set(v___f_588_, 7, v_atom_553_);
lean_closure_set(v___f_588_, 8, v_and_555_);
lean_closure_set(v___f_588_, 9, v_skip_x3f_547_);
lean_closure_set(v___f_588_, 10, v_skipConjunct_x3f_561_);
lean_closure_set(v___f_588_, 11, v_arg_575_);
lean_closure_set(v___f_588_, 12, v_toBind_551_);
v___x_589_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg(v_inst_559_, v_inst_560_, v_atom_553_, v_and_555_, v_or_558_, v_skip_x3f_547_, v_skipConjunct_x3f_561_, v_finishOr_x3f_557_, v_arg_576_, v_a_550_);
v___x_590_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_589_, v___f_588_);
v___x_591_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_590_, v___f_552_);
return v___x_591_;
}
}
}
}
}
else
{
lean_object* v_val_592_; lean_object* v_toPure_593_; lean_object* v___x_594_; 
lean_dec_ref(v_skipConjunct_x3f_561_);
lean_dec(v_inst_560_);
lean_dec_ref(v_inst_559_);
lean_dec(v_or_558_);
lean_dec_ref(v_finishOr_x3f_557_);
lean_dec(v_child_556_);
lean_dec(v_and_555_);
lean_dec(v_atom_553_);
lean_dec(v___f_552_);
lean_dec(v_toBind_551_);
lean_dec(v___f_549_);
lean_dec_ref(v_e_548_);
lean_dec_ref(v_skip_x3f_547_);
v_val_592_ = lean_ctor_get(v_a_562_, 0);
lean_inc(v_val_592_);
lean_dec_ref_known(v_a_562_, 1);
v_toPure_593_ = lean_ctor_get(v_toApplicative_554_, 1);
lean_inc(v_toPure_593_);
lean_dec_ref(v_toApplicative_554_);
v___x_594_ = lean_apply_2(v_toPure_593_, lean_box(0), v_val_592_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__9___boxed(lean_object* v_skip_x3f_595_, lean_object* v_e_596_, lean_object* v___f_597_, lean_object* v_a_598_, lean_object* v_toBind_599_, lean_object* v___f_600_, lean_object* v_atom_601_, lean_object* v_toApplicative_602_, lean_object* v_and_603_, lean_object* v_child_604_, lean_object* v_finishOr_x3f_605_, lean_object* v_or_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_skipConjunct_x3f_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__9(v_skip_x3f_595_, v_e_596_, v___f_597_, v_a_598_, v_toBind_599_, v___f_600_, v_atom_601_, v_toApplicative_602_, v_and_603_, v_child_604_, v_finishOr_x3f_605_, v_or_606_, v_inst_607_, v_inst_608_, v_skipConjunct_x3f_609_, v_a_610_);
lean_dec(v_a_598_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg(lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_atom_614_, lean_object* v_and_615_, lean_object* v_or_616_, lean_object* v_skip_x3f_617_, lean_object* v_skipConjunct_x3f_618_, lean_object* v_finishOr_x3f_619_, lean_object* v_e_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_toApplicative_622_; lean_object* v_toBind_623_; lean_object* v___f_624_; lean_object* v_child_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_toApplicative_622_ = lean_ctor_get(v_inst_612_, 0);
lean_inc_ref_n(v_toApplicative_622_, 4);
v_toBind_623_ = lean_ctor_get(v_inst_612_, 1);
lean_inc_n(v_toBind_623_, 4);
v___f_624_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_624_, 0, v_toApplicative_622_);
lean_inc_ref(v_finishOr_x3f_619_);
lean_inc_ref(v_skip_x3f_617_);
lean_inc(v_or_616_);
lean_inc(v_and_615_);
lean_inc(v_atom_614_);
lean_inc_n(v_inst_613_, 3);
lean_inc_ref(v_inst_612_);
lean_inc_ref(v___f_624_);
lean_inc_ref(v_skipConjunct_x3f_618_);
v_child_625_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v_child_625_, 0, v_skipConjunct_x3f_618_);
lean_closure_set(v_child_625_, 1, v___f_624_);
lean_closure_set(v_child_625_, 2, v_inst_612_);
lean_closure_set(v_child_625_, 3, v_inst_613_);
lean_closure_set(v_child_625_, 4, v_atom_614_);
lean_closure_set(v_child_625_, 5, v_and_615_);
lean_closure_set(v_child_625_, 6, v_or_616_);
lean_closure_set(v_child_625_, 7, v_skip_x3f_617_);
lean_closure_set(v_child_625_, 8, v_finishOr_x3f_619_);
v___x_626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__0));
v___x_627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__1));
lean_inc_n(v_a_621_, 3);
lean_inc_ref_n(v_e_620_, 2);
v___f_628_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_628_, 0, v_toApplicative_622_);
lean_closure_set(v___f_628_, 1, v___x_626_);
lean_closure_set(v___f_628_, 2, v___x_627_);
lean_closure_set(v___f_628_, 3, v_e_620_);
lean_closure_set(v___f_628_, 4, v_a_621_);
lean_closure_set(v___f_628_, 5, v_inst_613_);
lean_closure_set(v___f_628_, 6, v_toBind_623_);
v___f_629_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__9___boxed), 16, 15);
lean_closure_set(v___f_629_, 0, v_skip_x3f_617_);
lean_closure_set(v___f_629_, 1, v_e_620_);
lean_closure_set(v___f_629_, 2, v___f_624_);
lean_closure_set(v___f_629_, 3, v_a_621_);
lean_closure_set(v___f_629_, 4, v_toBind_623_);
lean_closure_set(v___f_629_, 5, v___f_628_);
lean_closure_set(v___f_629_, 6, v_atom_614_);
lean_closure_set(v___f_629_, 7, v_toApplicative_622_);
lean_closure_set(v___f_629_, 8, v_and_615_);
lean_closure_set(v___f_629_, 9, v_child_625_);
lean_closure_set(v___f_629_, 10, v_finishOr_x3f_619_);
lean_closure_set(v___f_629_, 11, v_or_616_);
lean_closure_set(v___f_629_, 12, v_inst_612_);
lean_closure_set(v___f_629_, 13, v_inst_613_);
lean_closure_set(v___f_629_, 14, v_skipConjunct_x3f_618_);
v___f_630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_630_, 0, v_toApplicative_622_);
lean_closure_set(v___f_630_, 1, v___x_626_);
lean_closure_set(v___f_630_, 2, v___x_627_);
lean_closure_set(v___f_630_, 3, v_e_620_);
v___x_631_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_631_, 0, lean_box(0));
lean_closure_set(v___x_631_, 1, lean_box(0));
lean_closure_set(v___x_631_, 2, v_a_621_);
v___x_632_ = lean_apply_2(v_inst_613_, lean_box(0), v___x_631_);
v___x_633_ = lean_apply_4(v_toBind_623_, lean_box(0), lean_box(0), v___x_632_, v___f_630_);
v___x_634_ = lean_apply_4(v_toBind_623_, lean_box(0), lean_box(0), v___x_633_, v___f_629_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__1(lean_object* v_skipConjunct_x3f_635_, lean_object* v___f_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_atom_639_, lean_object* v_and_640_, lean_object* v_or_641_, lean_object* v_skip_x3f_642_, lean_object* v_finishOr_x3f_643_, lean_object* v_e_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_646_; 
lean_inc_ref(v_skipConjunct_x3f_635_);
lean_inc_ref(v_e_644_);
v___x_646_ = lean_apply_1(v_skipConjunct_x3f_635_, v_e_644_);
if (lean_obj_tag(v___x_646_) == 1)
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_dec_ref(v_e_644_);
lean_dec_ref(v_finishOr_x3f_643_);
lean_dec_ref(v_skip_x3f_642_);
lean_dec(v_or_641_);
lean_dec(v_and_640_);
lean_dec(v_atom_639_);
lean_dec(v_inst_638_);
lean_dec_ref(v_inst_637_);
lean_dec_ref(v_skipConjunct_x3f_635_);
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_646_, 1);
lean_inc(v___y_645_);
v___x_648_ = lean_apply_2(v___f_636_, v_val_647_, v___y_645_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; 
lean_dec(v___x_646_);
lean_dec(v___f_636_);
v___x_649_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg(v_inst_637_, v_inst_638_, v_atom_639_, v_and_640_, v_or_641_, v_skip_x3f_642_, v_skipConjunct_x3f_635_, v_finishOr_x3f_643_, v_e_644_, v___y_645_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___boxed(lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_atom_652_, lean_object* v_and_653_, lean_object* v_or_654_, lean_object* v_skip_x3f_655_, lean_object* v_skipConjunct_x3f_656_, lean_object* v_finishOr_x3f_657_, lean_object* v_e_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg(v_inst_650_, v_inst_651_, v_atom_652_, v_and_653_, v_or_654_, v_skip_x3f_655_, v_skipConjunct_x3f_656_, v_finishOr_x3f_657_, v_e_658_, v_a_659_);
lean_dec(v_a_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit(lean_object* v_m_661_, lean_object* v_00_u03c9_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_00_u03c3_666_, lean_object* v_inst_667_, lean_object* v_atom_668_, lean_object* v_and_669_, lean_object* v_or_670_, lean_object* v_skip_x3f_671_, lean_object* v_skipConjunct_x3f_672_, lean_object* v_finishOr_x3f_673_, lean_object* v_e_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg(v_inst_663_, v_inst_665_, v_atom_668_, v_and_669_, v_or_670_, v_skip_x3f_671_, v_skipConjunct_x3f_672_, v_finishOr_x3f_673_, v_e_674_, v_a_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___boxed(lean_object* v_m_677_, lean_object* v_00_u03c9_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_00_u03c3_682_, lean_object* v_inst_683_, lean_object* v_atom_684_, lean_object* v_and_685_, lean_object* v_or_686_, lean_object* v_skip_x3f_687_, lean_object* v_skipConjunct_x3f_688_, lean_object* v_finishOr_x3f_689_, lean_object* v_e_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit(v_m_677_, v_00_u03c9_678_, v_inst_679_, v_inst_680_, v_inst_681_, v_00_u03c3_682_, v_inst_683_, v_atom_684_, v_and_685_, v_or_686_, v_skip_x3f_687_, v_skipConjunct_x3f_688_, v_finishOr_x3f_689_, v_e_690_, v_a_691_);
lean_dec(v_a_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___redArg(lean_object* v_a_693_, lean_object* v_x_694_){
_start:
{
if (lean_obj_tag(v_x_694_) == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_box(0);
return v___x_695_;
}
else
{
lean_object* v_key_696_; lean_object* v_value_697_; lean_object* v_tail_698_; uint8_t v___x_699_; 
v_key_696_ = lean_ctor_get(v_x_694_, 0);
v_value_697_ = lean_ctor_get(v_x_694_, 1);
v_tail_698_ = lean_ctor_get(v_x_694_, 2);
v___x_699_ = l_Lean_ExprStructEq_beq(v_key_696_, v_a_693_);
if (v___x_699_ == 0)
{
v_x_694_ = v_tail_698_;
goto _start;
}
else
{
lean_object* v___x_701_; 
lean_inc(v_value_697_);
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v_value_697_);
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_702_, lean_object* v_x_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___redArg(v_a_702_, v_x_703_);
lean_dec(v_x_703_);
lean_dec_ref(v_a_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___redArg(lean_object* v_m_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_buckets_707_; lean_object* v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v_fold_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_buckets_707_ = lean_ctor_get(v_m_705_, 1);
v___x_708_ = lean_array_get_size(v_buckets_707_);
v___x_709_ = l_Lean_ExprStructEq_hash(v_a_706_);
v___x_710_ = 32ULL;
v___x_711_ = lean_uint64_shift_right(v___x_709_, v___x_710_);
v_fold_712_ = lean_uint64_xor(v___x_709_, v___x_711_);
v___x_713_ = 16ULL;
v___x_714_ = lean_uint64_shift_right(v_fold_712_, v___x_713_);
v___x_715_ = lean_uint64_xor(v_fold_712_, v___x_714_);
v___x_716_ = lean_uint64_to_usize(v___x_715_);
v___x_717_ = lean_usize_of_nat(v___x_708_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_sub(v___x_717_, v___x_718_);
v___x_720_ = lean_usize_land(v___x_716_, v___x_719_);
v___x_721_ = lean_array_uget_borrowed(v_buckets_707_, v___x_720_);
v___x_722_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___redArg(v_a_706_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___redArg___boxed(lean_object* v_m_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___redArg(v_m_723_, v_a_724_);
lean_dec_ref(v_a_724_);
lean_dec_ref(v_m_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f___redArg(lean_object* v_s_726_, lean_object* v_e_727_){
_start:
{
lean_object* v_entries_728_; lean_object* v___x_729_; 
v_entries_728_ = lean_ctor_get(v_s_726_, 1);
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___redArg(v_entries_728_, v_e_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f___redArg___boxed(lean_object* v_s_730_, lean_object* v_e_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Meta_Grind_Formula_Summary_find_x3f___redArg(v_s_730_, v_e_731_);
lean_dec_ref(v_e_731_);
lean_dec_ref(v_s_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f(lean_object* v_00_u03c3_733_, lean_object* v_s_734_, lean_object* v_e_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_Grind_Formula_Summary_find_x3f___redArg(v_s_734_, v_e_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f___boxed(lean_object* v_00_u03c3_737_, lean_object* v_s_738_, lean_object* v_e_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Meta_Grind_Formula_Summary_find_x3f(v_00_u03c3_737_, v_s_738_, v_e_739_);
lean_dec_ref(v_e_739_);
lean_dec_ref(v_s_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0(lean_object* v_00_u03b2_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___redArg(v_m_742_, v_a_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_745_, lean_object* v_m_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0(v_00_u03b2_745_, v_m_746_, v_a_747_);
lean_dec_ref(v_a_747_);
lean_dec_ref(v_m_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_749_, lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___redArg(v_a_750_, v_x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_753_, lean_object* v_a_754_, lean_object* v_x_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Formula_Summary_find_x3f_spec__0_spec__0(v_00_u03b2_753_, v_a_754_, v_x_755_);
lean_dec(v_x_755_);
lean_dec_ref(v_a_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__0(lean_object* v_toPure_757_, lean_object* v_____x_758_){
_start:
{
lean_object* v_fst_759_; lean_object* v_snd_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
v_fst_759_ = lean_ctor_get(v_____x_758_, 0);
v_snd_760_ = lean_ctor_get(v_____x_758_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_____x_758_);
if (v_isSharedCheck_768_ == 0)
{
v___x_762_ = v_____x_758_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_snd_760_);
lean_inc(v_fst_759_);
lean_dec(v_____x_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_fst_759_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_snd_760_);
v___x_765_ = v_reuseFailAlloc_767_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; 
v___x_766_ = lean_apply_2(v_toPure_757_, lean_box(0), v___x_765_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__1(lean_object* v_a_769_, lean_object* v_toPure_770_, lean_object* v_s_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_a_769_);
lean_ctor_set(v___x_772_, 1, v_s_771_);
v___x_773_ = lean_apply_2(v_toPure_770_, lean_box(0), v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__2(lean_object* v_toPure_774_, lean_object* v_ref_775_, lean_object* v_inst_776_, lean_object* v_toBind_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___f_779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__1), 3, 2);
lean_closure_set(v___f_779_, 0, v_a_778_);
lean_closure_set(v___f_779_, 1, v_toPure_774_);
v___x_780_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_780_, 0, lean_box(0));
lean_closure_set(v___x_780_, 1, lean_box(0));
lean_closure_set(v___x_780_, 2, v_ref_775_);
v___x_781_ = lean_apply_2(v_inst_776_, lean_box(0), v___x_780_);
v___x_782_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_781_, v___f_779_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__3(lean_object* v_toPure_783_, lean_object* v_inst_784_, lean_object* v_toBind_785_, lean_object* v_x_786_, lean_object* v_ref_787_){
_start:
{
lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_inc(v_toBind_785_);
lean_inc(v_ref_787_);
v___f_788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__2), 5, 4);
lean_closure_set(v___f_788_, 0, v_toPure_783_);
lean_closure_set(v___f_788_, 1, v_ref_787_);
lean_closure_set(v___f_788_, 2, v_inst_784_);
lean_closure_set(v___f_788_, 3, v_toBind_785_);
v___x_789_ = lean_apply_1(v_x_786_, v_ref_787_);
v___x_790_ = lean_apply_4(v_toBind_785_, lean_box(0), lean_box(0), v___x_789_, v___f_788_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__0(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = lean_box(0);
v___x_792_ = lean_unsigned_to_nat(16u);
v___x_793_ = lean_mk_array(v___x_792_, v___x_791_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__1(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__0);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_794_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__1);
v___x_798_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_798_, 0, lean_box(0));
lean_closure_set(v___x_798_, 1, lean_box(0));
lean_closure_set(v___x_798_, 2, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg(lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_toApplicative_802_; lean_object* v_toBind_803_; lean_object* v_toPure_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_toApplicative_802_ = lean_ctor_get(v_inst_799_, 0);
lean_inc_ref(v_toApplicative_802_);
v_toBind_803_ = lean_ctor_get(v_inst_799_, 1);
lean_inc_n(v_toBind_803_, 3);
lean_dec_ref(v_inst_799_);
v_toPure_804_ = lean_ctor_get(v_toApplicative_802_, 1);
lean_inc_n(v_toPure_804_, 2);
lean_dec_ref(v_toApplicative_802_);
v___x_805_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2);
lean_inc(v_inst_800_);
v___x_806_ = lean_apply_2(v_inst_800_, lean_box(0), v___x_805_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__0), 2, 1);
lean_closure_set(v___f_807_, 0, v_toPure_804_);
v___f_808_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___lam__3), 5, 4);
lean_closure_set(v___f_808_, 0, v_toPure_804_);
lean_closure_set(v___f_808_, 1, v_inst_800_);
lean_closure_set(v___f_808_, 2, v_toBind_803_);
lean_closure_set(v___f_808_, 3, v_x_801_);
v___x_809_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_806_, v___f_808_);
v___x_810_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_809_, v___f_807_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold(lean_object* v_m_811_, lean_object* v_00_u03c9_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_00_u03c3_816_, lean_object* v_x_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg(v_inst_813_, v_inst_815_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__0(lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = lean_box(0);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__0___boxed(lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__0(v_x_821_);
lean_dec_ref(v_x_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__1(lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = lean_box(0);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__1___boxed(lean_object* v_x_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Meta_Grind_Formula_foldCachedM___redArg___lam__1(v_x_825_);
lean_dec(v_x_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg(lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_atom_831_, lean_object* v_and_832_, lean_object* v_or_833_, lean_object* v_e_834_, lean_object* v_known_x3f_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; 
v___f_837_ = ((lean_object*)(l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__0));
v___f_838_ = ((lean_object*)(l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__1));
v___x_839_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg(v_inst_829_, v_inst_830_, v_atom_831_, v_and_832_, v_or_833_, v_known_x3f_835_, v___f_837_, v___f_838_, v_e_834_, v_a_836_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___redArg___boxed(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_atom_842_, lean_object* v_and_843_, lean_object* v_or_844_, lean_object* v_e_845_, lean_object* v_known_x3f_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Meta_Grind_Formula_foldCachedM___redArg(v_inst_840_, v_inst_841_, v_atom_842_, v_and_843_, v_or_844_, v_e_845_, v_known_x3f_846_, v_a_847_);
lean_dec(v_a_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM(lean_object* v_m_849_, lean_object* v_00_u03c9_850_, lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_00_u03c3_854_, lean_object* v_inst_855_, lean_object* v_atom_856_, lean_object* v_and_857_, lean_object* v_or_858_, lean_object* v_e_859_, lean_object* v_known_x3f_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_Formula_foldCachedM___redArg(v_inst_851_, v_inst_853_, v_atom_856_, v_and_857_, v_or_858_, v_e_859_, v_known_x3f_860_, v_a_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___boxed(lean_object* v_m_863_, lean_object* v_00_u03c9_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_00_u03c3_868_, lean_object* v_inst_869_, lean_object* v_atom_870_, lean_object* v_and_871_, lean_object* v_or_872_, lean_object* v_e_873_, lean_object* v_known_x3f_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_Grind_Formula_foldCachedM(v_m_863_, v_00_u03c9_864_, v_inst_865_, v_inst_866_, v_inst_867_, v_00_u03c3_868_, v_inst_869_, v_atom_870_, v_and_871_, v_or_872_, v_e_873_, v_known_x3f_874_, v_a_875_);
lean_dec(v_a_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldM___redArg(lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_atom_880_, lean_object* v_and_881_, lean_object* v_or_882_, lean_object* v_e_883_){
_start:
{
lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___f_884_ = ((lean_object*)(l_Lean_Meta_Grind_Formula_foldCachedM___redArg___closed__0));
lean_inc(v_inst_879_);
lean_inc_ref(v_inst_877_);
v___x_885_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldCachedM___boxed), 13, 12);
lean_closure_set(v___x_885_, 0, lean_box(0));
lean_closure_set(v___x_885_, 1, lean_box(0));
lean_closure_set(v___x_885_, 2, v_inst_877_);
lean_closure_set(v___x_885_, 3, v_inst_878_);
lean_closure_set(v___x_885_, 4, v_inst_879_);
lean_closure_set(v___x_885_, 5, lean_box(0));
lean_closure_set(v___x_885_, 6, lean_box(0));
lean_closure_set(v___x_885_, 7, v_atom_880_);
lean_closure_set(v___x_885_, 8, v_and_881_);
lean_closure_set(v___x_885_, 9, v_or_882_);
lean_closure_set(v___x_885_, 10, v_e_883_);
lean_closure_set(v___x_885_, 11, v___f_884_);
v___x_886_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg(v_inst_877_, v_inst_879_, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldM(lean_object* v_m_887_, lean_object* v_00_u03c9_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_00_u03c3_892_, lean_object* v_inst_893_, lean_object* v_atom_894_, lean_object* v_and_895_, lean_object* v_or_896_, lean_object* v_e_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Meta_Grind_Formula_foldM___redArg(v_inst_889_, v_inst_890_, v_inst_891_, v_atom_894_, v_and_895_, v_or_896_, v_e_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__0(lean_object* v_isEmpty_899_, lean_object* v_empty_900_, lean_object* v_x_901_){
_start:
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_apply_1(v_isEmpty_899_, v_x_901_);
v___x_903_ = lean_unbox(v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec(v_empty_900_);
v___x_904_ = lean_box(0);
return v___x_904_;
}
else
{
lean_object* v___x_905_; 
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v_empty_900_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__1(lean_object* v___x_906_, lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v_snd_909_, lean_object* v_empty_910_, lean_object* v_c_911_){
_start:
{
lean_object* v___x_912_; uint8_t v_supported_913_; 
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v___x_906_, v___x_907_, v___x_908_, v_snd_909_, v_c_911_);
v_supported_913_ = lean_ctor_get_uint8(v___x_912_, 0);
lean_dec(v___x_912_);
if (v_supported_913_ == 0)
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_empty_910_);
return v___x_914_;
}
else
{
lean_object* v___x_915_; 
lean_dec(v_empty_910_);
v___x_915_ = lean_box(0);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__1___boxed(lean_object* v___x_916_, lean_object* v___x_917_, lean_object* v___x_918_, lean_object* v_snd_919_, lean_object* v_empty_920_, lean_object* v_c_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__1(v___x_916_, v___x_917_, v___x_918_, v_snd_919_, v_empty_920_, v_c_921_);
lean_dec_ref(v_snd_919_);
lean_dec_ref(v___x_918_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__2(lean_object* v___x_923_, lean_object* v___x_924_, lean_object* v___x_925_, lean_object* v_snd_926_, lean_object* v_empty_927_, lean_object* v_c_928_){
_start:
{
lean_object* v___x_929_; uint8_t v_conjunct_930_; uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v___x_923_, v___x_924_, v___x_925_, v_snd_926_, v_c_928_);
v_conjunct_930_ = lean_ctor_get_uint8(v___x_929_, 1);
lean_dec(v___x_929_);
v___x_931_ = 0;
v___x_932_ = l_Lean_instBEqLBool_beq(v_conjunct_930_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec(v_empty_927_);
v___x_933_ = lean_box(0);
return v___x_933_;
}
else
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v_empty_927_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__2___boxed(lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v_snd_938_, lean_object* v_empty_939_, lean_object* v_c_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__2(v___x_935_, v___x_936_, v___x_937_, v_snd_938_, v_empty_939_, v_c_940_);
lean_dec_ref(v_snd_938_);
lean_dec_ref(v___x_937_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__3(lean_object* v___x_942_, lean_object* v___x_943_, lean_object* v___x_944_, lean_object* v___x_945_, lean_object* v_e_946_, lean_object* v_empty_947_, lean_object* v_toPure_948_, lean_object* v___x_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_atom_953_, lean_object* v_and_954_, lean_object* v_or_955_, lean_object* v_finishOr_x3f_956_, lean_object* v_____x_957_){
_start:
{
lean_object* v_fst_958_; uint8_t v_supported_959_; 
v_fst_958_ = lean_ctor_get(v_____x_957_, 0);
v_supported_959_ = lean_ctor_get_uint8(v_fst_958_, 0);
if (v_supported_959_ == 0)
{
lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_971_; 
lean_dec_ref(v_finishOr_x3f_956_);
lean_dec(v_or_955_);
lean_dec(v_and_954_);
lean_dec(v_atom_953_);
lean_dec(v_inst_952_);
lean_dec_ref(v_inst_950_);
lean_dec_ref(v___x_949_);
v_isSharedCheck_971_ = !lean_is_exclusive(v_____x_957_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_972_ = lean_ctor_get(v_____x_957_, 1);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_____x_957_, 0);
lean_dec(v_unused_973_);
v___x_961_ = v_____x_957_;
v_isShared_962_ = v_isSharedCheck_971_;
goto v_resetjp_960_;
}
else
{
lean_dec(v_____x_957_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_971_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_963_ = lean_box(0);
v___x_964_ = lean_mk_array(v___x_942_, v___x_963_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_964_);
lean_ctor_set(v___x_961_, 0, v___x_943_);
v___x_966_ = v___x_961_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_inc(v_empty_947_);
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_944_, v___x_945_, v___x_966_, v_e_946_, v_empty_947_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_empty_947_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_apply_2(v_toPure_948_, lean_box(0), v___x_968_);
return v___x_969_;
}
}
}
else
{
lean_object* v_snd_974_; lean_object* v_skip_x3f_975_; lean_object* v_skipConjunct_x3f_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v_toPure_948_);
lean_dec(v___x_943_);
lean_dec(v___x_942_);
v_snd_974_ = lean_ctor_get(v_____x_957_, 1);
lean_inc_n(v_snd_974_, 2);
lean_dec_ref(v_____x_957_);
lean_inc(v_empty_947_);
lean_inc_ref(v___x_949_);
lean_inc_ref(v___x_945_);
lean_inc_ref(v___x_944_);
v_skip_x3f_975_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v_skip_x3f_975_, 0, v___x_944_);
lean_closure_set(v_skip_x3f_975_, 1, v___x_945_);
lean_closure_set(v_skip_x3f_975_, 2, v___x_949_);
lean_closure_set(v_skip_x3f_975_, 3, v_snd_974_);
lean_closure_set(v_skip_x3f_975_, 4, v_empty_947_);
v_skipConjunct_x3f_976_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v_skipConjunct_x3f_976_, 0, v___x_944_);
lean_closure_set(v_skipConjunct_x3f_976_, 1, v___x_945_);
lean_closure_set(v_skipConjunct_x3f_976_, 2, v___x_949_);
lean_closure_set(v_skipConjunct_x3f_976_, 3, v_snd_974_);
lean_closure_set(v_skipConjunct_x3f_976_, 4, v_empty_947_);
lean_inc(v_inst_952_);
lean_inc_ref(v_inst_950_);
v___x_977_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___boxed), 15, 14);
lean_closure_set(v___x_977_, 0, lean_box(0));
lean_closure_set(v___x_977_, 1, lean_box(0));
lean_closure_set(v___x_977_, 2, v_inst_950_);
lean_closure_set(v___x_977_, 3, v_inst_951_);
lean_closure_set(v___x_977_, 4, v_inst_952_);
lean_closure_set(v___x_977_, 5, lean_box(0));
lean_closure_set(v___x_977_, 6, lean_box(0));
lean_closure_set(v___x_977_, 7, v_atom_953_);
lean_closure_set(v___x_977_, 8, v_and_954_);
lean_closure_set(v___x_977_, 9, v_or_955_);
lean_closure_set(v___x_977_, 10, v_skip_x3f_975_);
lean_closure_set(v___x_977_, 11, v_skipConjunct_x3f_976_);
lean_closure_set(v___x_977_, 12, v_finishOr_x3f_956_);
lean_closure_set(v___x_977_, 13, v_e_946_);
v___x_978_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg(v_inst_950_, v_inst_952_, v___x_977_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__4(lean_object* v_a_979_, lean_object* v_toPure_980_, lean_object* v_s_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_a_979_);
lean_ctor_set(v___x_982_, 1, v_s_981_);
v___x_983_ = lean_apply_2(v_toPure_980_, lean_box(0), v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__5(lean_object* v_toPure_984_, lean_object* v_ref_985_, lean_object* v_inst_986_, lean_object* v_toBind_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_989_, 0, v_a_988_);
lean_closure_set(v___f_989_, 1, v_toPure_984_);
v___x_990_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_990_, 0, lean_box(0));
lean_closure_set(v___x_990_, 1, lean_box(0));
lean_closure_set(v___x_990_, 2, v_ref_985_);
v___x_991_ = lean_apply_2(v_inst_986_, lean_box(0), v___x_990_);
v___x_992_ = lean_apply_4(v_toBind_987_, lean_box(0), lean_box(0), v___x_991_, v___f_989_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__6(lean_object* v_toPure_993_, lean_object* v_inst_994_, lean_object* v_toBind_995_, lean_object* v_inst_996_, lean_object* v_canContribute_997_, lean_object* v_admitConjunct_998_, lean_object* v_e_999_, lean_object* v_ref_1000_){
_start:
{
lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_inc(v_toBind_995_);
lean_inc(v_inst_994_);
lean_inc(v_ref_1000_);
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1001_, 0, v_toPure_993_);
lean_closure_set(v___f_1001_, 1, v_ref_1000_);
lean_closure_set(v___f_1001_, 2, v_inst_994_);
lean_closure_set(v___f_1001_, 3, v_toBind_995_);
v___x_1002_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg(v_inst_996_, v_inst_994_, v_canContribute_997_, v_admitConjunct_998_, v_e_999_, v_ref_1000_);
lean_dec(v_ref_1000_);
v___x_1003_ = lean_apply_4(v_toBind_995_, lean_box(0), lean_box(0), v___x_1002_, v___f_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___redArg(lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_canContribute_1007_, lean_object* v_empty_1008_, lean_object* v_isEmpty_1009_, lean_object* v_atom_1010_, lean_object* v_and_1011_, lean_object* v_or_1012_, lean_object* v_e_1013_, lean_object* v_admitConjunct_1014_){
_start:
{
lean_object* v_toApplicative_1015_; lean_object* v_toBind_1016_; lean_object* v_toPure_1017_; lean_object* v_finishOr_x3f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_toApplicative_1015_ = lean_ctor_get(v_inst_1004_, 0);
v_toBind_1016_ = lean_ctor_get(v_inst_1004_, 1);
lean_inc_n(v_toBind_1016_, 3);
v_toPure_1017_ = lean_ctor_get(v_toApplicative_1015_, 1);
lean_inc_n(v_toPure_1017_, 2);
lean_inc(v_empty_1008_);
v_finishOr_x3f_1018_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__0), 3, 2);
lean_closure_set(v_finishOr_x3f_1018_, 0, v_isEmpty_1009_);
lean_closure_set(v_finishOr_x3f_1018_, 1, v_empty_1008_);
v___x_1019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__0));
v___x_1020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__1));
v___x_1021_ = ((lean_object*)(l_Lean_Meta_Grind_Formula_instInhabitedAdmission_default));
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_unsigned_to_nat(16u);
v___x_1024_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2);
lean_inc_n(v_inst_1006_, 2);
v___x_1025_ = lean_apply_2(v_inst_1006_, lean_box(0), v___x_1024_);
lean_inc_ref(v_inst_1004_);
lean_inc_ref(v_e_1013_);
v___f_1026_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1026_, 0, v___x_1023_);
lean_closure_set(v___f_1026_, 1, v___x_1022_);
lean_closure_set(v___f_1026_, 2, v___x_1019_);
lean_closure_set(v___f_1026_, 3, v___x_1020_);
lean_closure_set(v___f_1026_, 4, v_e_1013_);
lean_closure_set(v___f_1026_, 5, v_empty_1008_);
lean_closure_set(v___f_1026_, 6, v_toPure_1017_);
lean_closure_set(v___f_1026_, 7, v___x_1021_);
lean_closure_set(v___f_1026_, 8, v_inst_1004_);
lean_closure_set(v___f_1026_, 9, v_inst_1005_);
lean_closure_set(v___f_1026_, 10, v_inst_1006_);
lean_closure_set(v___f_1026_, 11, v_atom_1010_);
lean_closure_set(v___f_1026_, 12, v_and_1011_);
lean_closure_set(v___f_1026_, 13, v_or_1012_);
lean_closure_set(v___f_1026_, 14, v_finishOr_x3f_1018_);
v___f_1027_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___redArg___lam__6), 8, 7);
lean_closure_set(v___f_1027_, 0, v_toPure_1017_);
lean_closure_set(v___f_1027_, 1, v_inst_1006_);
lean_closure_set(v___f_1027_, 2, v_toBind_1016_);
lean_closure_set(v___f_1027_, 3, v_inst_1004_);
lean_closure_set(v___f_1027_, 4, v_canContribute_1007_);
lean_closure_set(v___f_1027_, 5, v_admitConjunct_1014_);
lean_closure_set(v___f_1027_, 6, v_e_1013_);
v___x_1028_ = lean_apply_4(v_toBind_1016_, lean_box(0), lean_box(0), v___x_1025_, v___f_1027_);
v___x_1029_ = lean_apply_4(v_toBind_1016_, lean_box(0), lean_box(0), v___x_1028_, v___f_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM(lean_object* v_m_1030_, lean_object* v_00_u03c9_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_00_u03c3_1035_, lean_object* v_canContribute_1036_, lean_object* v_empty_1037_, lean_object* v_isEmpty_1038_, lean_object* v_atom_1039_, lean_object* v_and_1040_, lean_object* v_or_1041_, lean_object* v_e_1042_, lean_object* v_admitConjunct_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_Grind_Formula_foldRelevantM___redArg(v_inst_1032_, v_inst_1033_, v_inst_1034_, v_canContribute_1036_, v_empty_1037_, v_isEmpty_1038_, v_atom_1039_, v_and_1040_, v_or_1041_, v_e_1042_, v_admitConjunct_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__0(lean_object* v_toApplicative_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_toPure_1048_; lean_object* v___x_1049_; 
v_toPure_1048_ = lean_ctor_get(v_toApplicative_1045_, 1);
lean_inc(v_toPure_1048_);
lean_dec_ref(v_toApplicative_1045_);
v___x_1049_ = lean_apply_2(v_toPure_1048_, lean_box(0), v_a_1046_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__1(lean_object* v___x_1050_, lean_object* v___x_1051_, lean_object* v_e_1052_, lean_object* v_a_1053_, lean_object* v_s_1054_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1050_, v___x_1051_, v_s_1054_, v_e_1052_, v_a_1053_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__2(lean_object* v_toApplicative_1058_, lean_object* v___x_1059_, lean_object* v___x_1060_, lean_object* v_e_1061_, lean_object* v_a_1062_, lean_object* v_inst_1063_, lean_object* v_toBind_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_inc_ref(v_a_1065_);
v___f_1066_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1066_, 0, v_toApplicative_1058_);
lean_closure_set(v___f_1066_, 1, v_a_1065_);
v___f_1067_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1067_, 0, v___x_1059_);
lean_closure_set(v___f_1067_, 1, v___x_1060_);
lean_closure_set(v___f_1067_, 2, v_e_1061_);
lean_closure_set(v___f_1067_, 3, v_a_1065_);
lean_inc(v_a_1062_);
v___x_1068_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1068_, 0, lean_box(0));
lean_closure_set(v___x_1068_, 1, lean_box(0));
lean_closure_set(v___x_1068_, 2, lean_box(0));
lean_closure_set(v___x_1068_, 3, v_a_1062_);
lean_closure_set(v___x_1068_, 4, v___f_1067_);
v___x_1069_ = lean_apply_2(v_inst_1063_, lean_box(0), v___x_1068_);
v___x_1070_ = lean_apply_4(v_toBind_1064_, lean_box(0), lean_box(0), v___x_1069_, v___f_1066_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__2___boxed(lean_object* v_toApplicative_1071_, lean_object* v___x_1072_, lean_object* v___x_1073_, lean_object* v_e_1074_, lean_object* v_a_1075_, lean_object* v_inst_1076_, lean_object* v_toBind_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__2(v_toApplicative_1071_, v___x_1072_, v___x_1073_, v_e_1074_, v_a_1075_, v_inst_1076_, v_toBind_1077_, v_a_1078_);
lean_dec(v_a_1075_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__4(lean_object* v_h_1080_, lean_object* v_inst_1081_, lean_object* v_____do__lift_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; uint8_t v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_mk_empty_array_with_capacity(v___x_1083_);
v___x_1085_ = lean_array_push(v___x_1084_, v_h_1080_);
v___x_1086_ = 0;
v___x_1087_ = 1;
v___x_1088_ = 1;
v___x_1089_ = lean_box(v___x_1086_);
v___x_1090_ = lean_box(v___x_1087_);
v___x_1091_ = lean_box(v___x_1086_);
v___x_1092_ = lean_box(v___x_1087_);
v___x_1093_ = lean_box(v___x_1088_);
v___x_1094_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1094_, 0, v___x_1085_);
lean_closure_set(v___x_1094_, 1, v_____do__lift_1082_);
lean_closure_set(v___x_1094_, 2, v___x_1089_);
lean_closure_set(v___x_1094_, 3, v___x_1090_);
lean_closure_set(v___x_1094_, 4, v___x_1091_);
lean_closure_set(v___x_1094_, 5, v___x_1092_);
lean_closure_set(v___x_1094_, 6, v___x_1093_);
v___x_1095_ = lean_apply_2(v_inst_1081_, lean_box(0), v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__3(lean_object* v_inst_1096_, lean_object* v_proveAtom_1097_, lean_object* v_val_1098_, lean_object* v_e_1099_, lean_object* v_toBind_1100_, lean_object* v_h_1101_){
_start:
{
lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_inc_ref(v_h_1101_);
v___f_1102_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1102_, 0, v_h_1101_);
lean_closure_set(v___f_1102_, 1, v_inst_1096_);
v___x_1103_ = lean_apply_3(v_proveAtom_1097_, v_val_1098_, v_e_1099_, v_h_1101_);
v___x_1104_ = lean_apply_4(v_toBind_1100_, lean_box(0), lean_box(0), v___x_1103_, v___f_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__2));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5(lean_object* v_support_1111_, lean_object* v_e_1112_, lean_object* v_inst_1113_, lean_object* v_proveAtom_1114_, lean_object* v_toBind_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_x_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1121_; 
lean_inc_ref(v_e_1112_);
v___x_1121_ = lean_apply_1(v_support_1111_, v_e_1112_);
if (lean_obj_tag(v___x_1121_) == 1)
{
lean_object* v_val_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec_ref(v_inst_1118_);
v_val_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_val_1122_);
lean_dec_ref_known(v___x_1121_, 1);
lean_inc_ref(v_e_1112_);
v___f_1123_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1123_, 0, v_inst_1113_);
lean_closure_set(v___f_1123_, 1, v_proveAtom_1114_);
lean_closure_set(v___f_1123_, 2, v_val_1122_);
lean_closure_set(v___f_1123_, 3, v_e_1112_);
lean_closure_set(v___f_1123_, 4, v_toBind_1115_);
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__1));
v___x_1125_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_1116_, v_inst_1117_, v___x_1124_, v_e_1112_, v___f_1123_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec(v___x_1121_);
lean_dec_ref(v_inst_1116_);
lean_dec(v_toBind_1115_);
lean_dec(v_proveAtom_1114_);
lean_dec(v_inst_1113_);
v___x_1126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__3, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___closed__3);
v___x_1127_ = l_Lean_indentExpr(v_e_1112_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_throwError___redArg(v_inst_1117_, v_inst_1118_, v___x_1128_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___boxed(lean_object* v_support_1130_, lean_object* v_e_1131_, lean_object* v_inst_1132_, lean_object* v_proveAtom_1133_, lean_object* v_toBind_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_x_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5(v_support_1130_, v_e_1131_, v_inst_1132_, v_proveAtom_1133_, v_toBind_1134_, v_inst_1135_, v_inst_1136_, v_inst_1137_, v_x_1138_, v___y_1139_);
lean_dec(v___y_1139_);
return v_res_1140_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__4(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_box(0);
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__3));
v___x_1150_ = l_Lean_mkConst(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6(lean_object* v_toApplicative_1151_, lean_object* v_arg_1152_, lean_object* v_arg_1153_, lean_object* v_motive_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_toPure_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_toPure_1156_ = lean_ctor_get(v_toApplicative_1151_, 1);
lean_inc(v_toPure_1156_);
lean_dec_ref(v_toApplicative_1151_);
v___x_1157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__4, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6___closed__4);
v___x_1158_ = l_Lean_mkApp4(v___x_1157_, v_arg_1152_, v_arg_1153_, v_motive_1154_, v_a_1155_);
v___x_1159_ = lean_apply_2(v_toPure_1156_, lean_box(0), v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__2(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__1));
v___x_1167_ = l_Lean_mkConst(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7(lean_object* v_toApplicative_1168_, lean_object* v_arg_1169_, lean_object* v_arg_1170_, lean_object* v_motive_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_toPure_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_toPure_1173_ = lean_ctor_get(v_toApplicative_1168_, 1);
lean_inc(v_toPure_1173_);
lean_dec_ref(v_toApplicative_1168_);
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__2, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7___closed__2);
v___x_1175_ = l_Lean_mkApp4(v___x_1174_, v_arg_1169_, v_arg_1170_, v_motive_1171_, v_a_1172_);
v___x_1176_ = lean_apply_2(v_toPure_1173_, lean_box(0), v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__1));
v___x_1184_ = l_Lean_mkConst(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8(lean_object* v_toApplicative_1185_, lean_object* v_arg_1186_, lean_object* v_arg_1187_, lean_object* v_motive_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_toPure_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_toPure_1191_ = lean_ctor_get(v_toApplicative_1185_, 1);
lean_inc(v_toPure_1191_);
lean_dec_ref(v_toApplicative_1185_);
v___x_1192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__2, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8___closed__2);
v___x_1193_ = l_Lean_mkApp5(v___x_1192_, v_arg_1186_, v_arg_1187_, v_motive_1188_, v_a_1189_, v_a_1190_);
v___x_1194_ = lean_apply_2(v_toPure_1191_, lean_box(0), v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__9___boxed(lean_object* v_toApplicative_1195_, lean_object* v_arg_1196_, lean_object* v_arg_1197_, lean_object* v_motive_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_support_1204_, lean_object* v_proveAtom_1205_, lean_object* v_a_1206_, lean_object* v_toBind_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__9(v_toApplicative_1195_, v_arg_1196_, v_arg_1197_, v_motive_1198_, v_inst_1199_, v_inst_1200_, v_inst_1201_, v_inst_1202_, v_inst_1203_, v_support_1204_, v_proveAtom_1205_, v_a_1206_, v_toBind_1207_, v_a_1208_);
lean_dec(v_a_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__10(lean_object* v_e_1210_, lean_object* v___f_1211_, lean_object* v_a_1212_, lean_object* v_toBind_1213_, lean_object* v___f_1214_, lean_object* v_support_1215_, lean_object* v_toApplicative_1216_, lean_object* v_motive_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_proveAtom_1223_, lean_object* v_a_1224_){
_start:
{
if (lean_obj_tag(v_a_1224_) == 0)
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = l_Lean_Expr_cleanupAnnotations(v_e_1210_);
v___x_1226_ = l_Lean_Expr_isApp(v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v___x_1225_);
lean_dec(v_proveAtom_1223_);
lean_dec(v_inst_1222_);
lean_dec_ref(v_inst_1221_);
lean_dec_ref(v_inst_1220_);
lean_dec(v_inst_1219_);
lean_dec_ref(v_inst_1218_);
lean_dec_ref(v_motive_1217_);
lean_dec_ref(v_toApplicative_1216_);
lean_dec_ref(v_support_1215_);
v___x_1227_ = lean_box(0);
lean_inc(v_a_1212_);
v___x_1228_ = lean_apply_2(v___f_1211_, v___x_1227_, v_a_1212_);
v___x_1229_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1228_, v___f_1214_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1225_);
v___x_1231_ = l_Lean_Expr_isApp(v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v___x_1230_);
lean_dec_ref(v___x_1225_);
lean_dec(v_proveAtom_1223_);
lean_dec(v_inst_1222_);
lean_dec_ref(v_inst_1221_);
lean_dec_ref(v_inst_1220_);
lean_dec(v_inst_1219_);
lean_dec_ref(v_inst_1218_);
lean_dec_ref(v_motive_1217_);
lean_dec_ref(v_toApplicative_1216_);
lean_dec_ref(v_support_1215_);
v___x_1232_ = lean_box(0);
lean_inc(v_a_1212_);
v___x_1233_ = lean_apply_2(v___f_1211_, v___x_1232_, v_a_1212_);
v___x_1234_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1233_, v___f_1214_);
return v___x_1234_;
}
else
{
lean_object* v_arg_1235_; lean_object* v_arg_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_arg_1235_ = lean_ctor_get(v___x_1225_, 1);
lean_inc_ref(v_arg_1235_);
lean_dec_ref(v___x_1225_);
v_arg_1236_ = lean_ctor_get(v___x_1230_, 1);
lean_inc_ref(v_arg_1236_);
v___x_1237_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1230_);
lean_dec_ref(v___x_1230_);
v___x_1238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__1));
v___x_1239_ = l_Lean_Expr_isConstOf(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___lam__16___closed__3));
v___x_1241_ = l_Lean_Expr_isConstOf(v___x_1237_, v___x_1240_);
lean_dec_ref(v___x_1237_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v_arg_1236_);
lean_dec_ref(v_arg_1235_);
lean_dec(v_proveAtom_1223_);
lean_dec(v_inst_1222_);
lean_dec_ref(v_inst_1221_);
lean_dec_ref(v_inst_1220_);
lean_dec(v_inst_1219_);
lean_dec_ref(v_inst_1218_);
lean_dec_ref(v_motive_1217_);
lean_dec_ref(v_toApplicative_1216_);
lean_dec_ref(v_support_1215_);
v___x_1242_ = lean_box(0);
lean_inc(v_a_1212_);
v___x_1243_ = lean_apply_2(v___f_1211_, v___x_1242_, v_a_1212_);
v___x_1244_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1243_, v___f_1214_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; 
lean_dec(v___f_1211_);
lean_inc_ref(v_support_1215_);
lean_inc_ref(v_arg_1236_);
v___x_1245_ = lean_apply_1(v_support_1215_, v_arg_1236_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_inc_ref(v_motive_1217_);
lean_inc_ref(v_arg_1235_);
v___f_1246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__6), 5, 4);
lean_closure_set(v___f_1246_, 0, v_toApplicative_1216_);
lean_closure_set(v___f_1246_, 1, v_arg_1236_);
lean_closure_set(v___f_1246_, 2, v_arg_1235_);
lean_closure_set(v___f_1246_, 3, v_motive_1217_);
v___x_1247_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(v_inst_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_inst_1222_, v_motive_1217_, v_support_1215_, v_proveAtom_1223_, v_arg_1235_, v_a_1212_);
lean_inc(v_toBind_1213_);
v___x_1248_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1247_, v___f_1246_);
v___x_1249_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1248_, v___f_1214_);
return v___x_1249_;
}
else
{
lean_object* v___f_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref_known(v___x_1245_, 1);
lean_inc_ref(v_motive_1217_);
lean_inc_ref(v_arg_1236_);
v___f_1250_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1250_, 0, v_toApplicative_1216_);
lean_closure_set(v___f_1250_, 1, v_arg_1236_);
lean_closure_set(v___f_1250_, 2, v_arg_1235_);
lean_closure_set(v___f_1250_, 3, v_motive_1217_);
v___x_1251_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(v_inst_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_inst_1222_, v_motive_1217_, v_support_1215_, v_proveAtom_1223_, v_arg_1236_, v_a_1212_);
lean_inc(v_toBind_1213_);
v___x_1252_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1251_, v___f_1250_);
v___x_1253_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1252_, v___f_1214_);
return v___x_1253_;
}
}
}
else
{
lean_object* v___f_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v___x_1237_);
lean_dec(v___f_1211_);
lean_inc_n(v_toBind_1213_, 2);
lean_inc(v_a_1212_);
lean_inc(v_proveAtom_1223_);
lean_inc_ref(v_support_1215_);
lean_inc(v_inst_1222_);
lean_inc_ref(v_inst_1221_);
lean_inc_ref(v_inst_1220_);
lean_inc(v_inst_1219_);
lean_inc_ref(v_inst_1218_);
lean_inc_ref(v_motive_1217_);
lean_inc_ref(v_arg_1236_);
v___f_1254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_1254_, 0, v_toApplicative_1216_);
lean_closure_set(v___f_1254_, 1, v_arg_1236_);
lean_closure_set(v___f_1254_, 2, v_arg_1235_);
lean_closure_set(v___f_1254_, 3, v_motive_1217_);
lean_closure_set(v___f_1254_, 4, v_inst_1218_);
lean_closure_set(v___f_1254_, 5, v_inst_1219_);
lean_closure_set(v___f_1254_, 6, v_inst_1220_);
lean_closure_set(v___f_1254_, 7, v_inst_1221_);
lean_closure_set(v___f_1254_, 8, v_inst_1222_);
lean_closure_set(v___f_1254_, 9, v_support_1215_);
lean_closure_set(v___f_1254_, 10, v_proveAtom_1223_);
lean_closure_set(v___f_1254_, 11, v_a_1212_);
lean_closure_set(v___f_1254_, 12, v_toBind_1213_);
v___x_1255_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(v_inst_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_inst_1222_, v_motive_1217_, v_support_1215_, v_proveAtom_1223_, v_arg_1236_, v_a_1212_);
v___x_1256_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1255_, v___f_1254_);
v___x_1257_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1256_, v___f_1214_);
return v___x_1257_;
}
}
}
}
else
{
lean_object* v_val_1258_; lean_object* v_toPure_1259_; lean_object* v___x_1260_; 
lean_dec(v_proveAtom_1223_);
lean_dec(v_inst_1222_);
lean_dec_ref(v_inst_1221_);
lean_dec_ref(v_inst_1220_);
lean_dec(v_inst_1219_);
lean_dec_ref(v_inst_1218_);
lean_dec_ref(v_motive_1217_);
lean_dec_ref(v_support_1215_);
lean_dec(v___f_1214_);
lean_dec(v_toBind_1213_);
lean_dec(v___f_1211_);
v_val_1258_ = lean_ctor_get(v_a_1224_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v_a_1224_, 1);
v_toPure_1259_ = lean_ctor_get(v_toApplicative_1216_, 1);
lean_inc(v_toPure_1259_);
lean_dec_ref(v_toApplicative_1216_);
v___x_1260_ = lean_apply_2(v_toPure_1259_, lean_box(0), v_val_1258_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__10___boxed(lean_object* v_e_1261_, lean_object* v___f_1262_, lean_object* v_a_1263_, lean_object* v_toBind_1264_, lean_object* v___f_1265_, lean_object* v_support_1266_, lean_object* v_toApplicative_1267_, lean_object* v_motive_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_proveAtom_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__10(v_e_1261_, v___f_1262_, v_a_1263_, v_toBind_1264_, v___f_1265_, v_support_1266_, v_toApplicative_1267_, v_motive_1268_, v_inst_1269_, v_inst_1270_, v_inst_1271_, v_inst_1272_, v_inst_1273_, v_proveAtom_1274_, v_a_1275_);
lean_dec(v_a_1263_);
lean_dec_ref(v_e_1261_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_motive_1282_, lean_object* v_support_1283_, lean_object* v_proveAtom_1284_, lean_object* v_e_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_toApplicative_1287_; lean_object* v_toBind_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; lean_object* v___f_1293_; lean_object* v___f_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_toApplicative_1287_ = lean_ctor_get(v_inst_1277_, 0);
lean_inc_ref_n(v_toApplicative_1287_, 3);
v_toBind_1288_ = lean_ctor_get(v_inst_1277_, 1);
lean_inc_n(v_toBind_1288_, 5);
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__0));
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___redArg___closed__1));
lean_inc_n(v_inst_1278_, 2);
lean_inc_n(v_a_1286_, 3);
lean_inc_ref_n(v_e_1285_, 3);
v___f_1291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1291_, 0, v_toApplicative_1287_);
lean_closure_set(v___f_1291_, 1, v___x_1289_);
lean_closure_set(v___f_1291_, 2, v___x_1290_);
lean_closure_set(v___f_1291_, 3, v_e_1285_);
lean_closure_set(v___f_1291_, 4, v_a_1286_);
lean_closure_set(v___f_1291_, 5, v_inst_1278_);
lean_closure_set(v___f_1291_, 6, v_toBind_1288_);
v___f_1292_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_1292_, 0, v_toApplicative_1287_);
lean_closure_set(v___f_1292_, 1, v___x_1289_);
lean_closure_set(v___f_1292_, 2, v___x_1290_);
lean_closure_set(v___f_1292_, 3, v_e_1285_);
lean_inc_ref(v_inst_1279_);
lean_inc_ref(v_inst_1277_);
lean_inc_ref(v_inst_1280_);
lean_inc(v_proveAtom_1284_);
lean_inc(v_inst_1281_);
lean_inc_ref(v_support_1283_);
v___f_1293_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_1293_, 0, v_support_1283_);
lean_closure_set(v___f_1293_, 1, v_e_1285_);
lean_closure_set(v___f_1293_, 2, v_inst_1281_);
lean_closure_set(v___f_1293_, 3, v_proveAtom_1284_);
lean_closure_set(v___f_1293_, 4, v_toBind_1288_);
lean_closure_set(v___f_1293_, 5, v_inst_1280_);
lean_closure_set(v___f_1293_, 6, v_inst_1277_);
lean_closure_set(v___f_1293_, 7, v_inst_1279_);
v___f_1294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__10___boxed), 15, 14);
lean_closure_set(v___f_1294_, 0, v_e_1285_);
lean_closure_set(v___f_1294_, 1, v___f_1293_);
lean_closure_set(v___f_1294_, 2, v_a_1286_);
lean_closure_set(v___f_1294_, 3, v_toBind_1288_);
lean_closure_set(v___f_1294_, 4, v___f_1291_);
lean_closure_set(v___f_1294_, 5, v_support_1283_);
lean_closure_set(v___f_1294_, 6, v_toApplicative_1287_);
lean_closure_set(v___f_1294_, 7, v_motive_1282_);
lean_closure_set(v___f_1294_, 8, v_inst_1277_);
lean_closure_set(v___f_1294_, 9, v_inst_1278_);
lean_closure_set(v___f_1294_, 10, v_inst_1279_);
lean_closure_set(v___f_1294_, 11, v_inst_1280_);
lean_closure_set(v___f_1294_, 12, v_inst_1281_);
lean_closure_set(v___f_1294_, 13, v_proveAtom_1284_);
v___x_1295_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1295_, 0, lean_box(0));
lean_closure_set(v___x_1295_, 1, lean_box(0));
lean_closure_set(v___x_1295_, 2, v_a_1286_);
v___x_1296_ = lean_apply_2(v_inst_1278_, lean_box(0), v___x_1295_);
v___x_1297_ = lean_apply_4(v_toBind_1288_, lean_box(0), lean_box(0), v___x_1296_, v___f_1292_);
v___x_1298_ = lean_apply_4(v_toBind_1288_, lean_box(0), lean_box(0), v___x_1297_, v___f_1294_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__9(lean_object* v_toApplicative_1299_, lean_object* v_arg_1300_, lean_object* v_arg_1301_, lean_object* v_motive_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_support_1308_, lean_object* v_proveAtom_1309_, lean_object* v_a_1310_, lean_object* v_toBind_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_inc_ref(v_motive_1302_);
lean_inc_ref(v_arg_1301_);
v___f_1313_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___lam__8), 6, 5);
lean_closure_set(v___f_1313_, 0, v_toApplicative_1299_);
lean_closure_set(v___f_1313_, 1, v_arg_1300_);
lean_closure_set(v___f_1313_, 2, v_arg_1301_);
lean_closure_set(v___f_1313_, 3, v_motive_1302_);
lean_closure_set(v___f_1313_, 4, v_a_1312_);
v___x_1314_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(v_inst_1303_, v_inst_1304_, v_inst_1305_, v_inst_1306_, v_inst_1307_, v_motive_1302_, v_support_1308_, v_proveAtom_1309_, v_arg_1301_, v_a_1310_);
v___x_1315_ = lean_apply_4(v_toBind_1311_, lean_box(0), lean_box(0), v___x_1314_, v___f_1313_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg___boxed(lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_motive_1321_, lean_object* v_support_1322_, lean_object* v_proveAtom_1323_, lean_object* v_e_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(v_inst_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_inst_1320_, v_motive_1321_, v_support_1322_, v_proveAtom_1323_, v_e_1324_, v_a_1325_);
lean_dec(v_a_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go(lean_object* v_m_1327_, lean_object* v_00_u03c9_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_00_u03b1_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_motive_1336_, lean_object* v_support_1337_, lean_object* v_proveAtom_1338_, lean_object* v_e_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(v_inst_1329_, v_inst_1331_, v_inst_1333_, v_inst_1334_, v_inst_1335_, v_motive_1336_, v_support_1337_, v_proveAtom_1338_, v_e_1339_, v_a_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___boxed(lean_object* v_m_1342_, lean_object* v_00_u03c9_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_00_u03b1_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_motive_1351_, lean_object* v_support_1352_, lean_object* v_proveAtom_1353_, lean_object* v_e_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go(v_m_1342_, v_00_u03c9_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_00_u03b1_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_motive_1351_, v_support_1352_, v_proveAtom_1353_, v_e_1354_, v_a_1355_);
lean_dec(v_a_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__0(lean_object* v_h_1357_, lean_object* v_toPure_1358_, lean_object* v_____do__lift_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = l_Lean_Expr_app___override(v_____do__lift_1359_, v_h_1357_);
v___x_1361_ = lean_apply_2(v_toPure_1358_, lean_box(0), v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__1(lean_object* v_a_1362_, lean_object* v_toPure_1363_, lean_object* v_s_1364_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_a_1362_);
lean_ctor_set(v___x_1365_, 1, v_s_1364_);
v___x_1366_ = lean_apply_2(v_toPure_1363_, lean_box(0), v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__2(lean_object* v_toPure_1367_, lean_object* v_ref_1368_, lean_object* v_inst_1369_, lean_object* v_toBind_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___f_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_prove___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1372_, 0, v_a_1371_);
lean_closure_set(v___f_1372_, 1, v_toPure_1367_);
v___x_1373_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1373_, 0, lean_box(0));
lean_closure_set(v___x_1373_, 1, lean_box(0));
lean_closure_set(v___x_1373_, 2, v_ref_1368_);
v___x_1374_ = lean_apply_2(v_inst_1369_, lean_box(0), v___x_1373_);
v___x_1375_ = lean_apply_4(v_toBind_1370_, lean_box(0), lean_box(0), v___x_1374_, v___f_1372_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__3(lean_object* v_toPure_1376_, lean_object* v_inst_1377_, lean_object* v_toBind_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_motive_1383_, lean_object* v_support_1384_, lean_object* v_proveAtom_1385_, lean_object* v_source_1386_, lean_object* v_ref_1387_){
_start:
{
lean_object* v___f_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_inc(v_toBind_1378_);
lean_inc(v_inst_1377_);
lean_inc(v_ref_1387_);
v___f_1388_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_prove___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1388_, 0, v_toPure_1376_);
lean_closure_set(v___f_1388_, 1, v_ref_1387_);
lean_closure_set(v___f_1388_, 2, v_inst_1377_);
lean_closure_set(v___f_1388_, 3, v_toBind_1378_);
v___x_1389_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_prove_go___redArg(v_inst_1379_, v_inst_1377_, v_inst_1380_, v_inst_1381_, v_inst_1382_, v_motive_1383_, v_support_1384_, v_proveAtom_1385_, v_source_1386_, v_ref_1387_);
lean_dec(v_ref_1387_);
v___x_1390_ = lean_apply_4(v_toBind_1378_, lean_box(0), lean_box(0), v___x_1389_, v___f_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg___lam__4(lean_object* v_toPure_1391_, lean_object* v_____x_1392_){
_start:
{
lean_object* v_fst_1393_; lean_object* v___x_1394_; 
v_fst_1393_ = lean_ctor_get(v_____x_1392_, 0);
lean_inc(v_fst_1393_);
lean_dec_ref(v_____x_1392_);
v___x_1394_ = lean_apply_2(v_toPure_1391_, lean_box(0), v_fst_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove___redArg(lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_source_1400_, lean_object* v_motive_1401_, lean_object* v_h_1402_, lean_object* v_support_1403_, lean_object* v_proveAtom_1404_){
_start:
{
lean_object* v_toApplicative_1405_; lean_object* v_toBind_1406_; lean_object* v_toPure_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v___f_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_toApplicative_1405_ = lean_ctor_get(v_inst_1395_, 0);
v_toBind_1406_ = lean_ctor_get(v_inst_1395_, 1);
lean_inc_n(v_toBind_1406_, 4);
v_toPure_1407_ = lean_ctor_get(v_toApplicative_1405_, 1);
lean_inc_n(v_toPure_1407_, 3);
v___x_1408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___redArg___closed__2);
lean_inc(v_inst_1396_);
v___x_1409_ = lean_apply_2(v_inst_1396_, lean_box(0), v___x_1408_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_prove___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1410_, 0, v_h_1402_);
lean_closure_set(v___f_1410_, 1, v_toPure_1407_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_prove___redArg___lam__3), 12, 11);
lean_closure_set(v___f_1411_, 0, v_toPure_1407_);
lean_closure_set(v___f_1411_, 1, v_inst_1396_);
lean_closure_set(v___f_1411_, 2, v_toBind_1406_);
lean_closure_set(v___f_1411_, 3, v_inst_1395_);
lean_closure_set(v___f_1411_, 4, v_inst_1397_);
lean_closure_set(v___f_1411_, 5, v_inst_1398_);
lean_closure_set(v___f_1411_, 6, v_inst_1399_);
lean_closure_set(v___f_1411_, 7, v_motive_1401_);
lean_closure_set(v___f_1411_, 8, v_support_1403_);
lean_closure_set(v___f_1411_, 9, v_proveAtom_1404_);
lean_closure_set(v___f_1411_, 10, v_source_1400_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_prove___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1412_, 0, v_toPure_1407_);
v___x_1413_ = lean_apply_4(v_toBind_1406_, lean_box(0), lean_box(0), v___x_1409_, v___f_1411_);
v___x_1414_ = lean_apply_4(v_toBind_1406_, lean_box(0), lean_box(0), v___x_1413_, v___f_1412_);
v___x_1415_ = lean_apply_4(v_toBind_1406_, lean_box(0), lean_box(0), v___x_1414_, v___f_1410_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_prove(lean_object* v_m_1416_, lean_object* v_00_u03c9_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_00_u03b1_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_source_1425_, lean_object* v_motive_1426_, lean_object* v_h_1427_, lean_object* v_support_1428_, lean_object* v_proveAtom_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Meta_Grind_Formula_prove___redArg(v_inst_1418_, v_inst_1420_, v_inst_1422_, v_inst_1423_, v_inst_1424_, v_source_1425_, v_motive_1426_, v_h_1427_, v_support_1428_, v_proveAtom_1429_);
return v___x_1430_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Formula(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Formula(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Formula(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Formula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Formula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Formula(builtin);
}
#ifdef __cplusplus
}
#endif
