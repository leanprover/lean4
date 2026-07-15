// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Reify
// Imports: public import Lean.Meta.Sym.Arith.Functions public import Lean.Meta.Sym.Arith.MonadVar public import Lean.Meta.Sym.LitValues
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isMulInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isMulInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isSubInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isSubInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isPowInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isPowInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isIntCastInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNatCastInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "ring term with unexpected instance"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__5_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__8_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__9_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__11_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__12_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__15_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__17_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__18_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__20_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__21_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__23_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__24_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "semiring term with unexpected instance"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_toPure_2_, lean_object* v_____do__lift_3_){
_start:
{
lean_object* v___x_4_; size_t v___x_5_; size_t v___x_6_; uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = l_Lean_Expr_appArg_x21(v_____do__lift_3_);
v___x_5_ = lean_ptr_addr(v___x_4_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_ptr_addr(v_inst_1_);
v___x_7_ = lean_usize_dec_eq(v___x_5_, v___x_6_);
v___x_8_ = lean_box(v___x_7_);
v___x_9_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed(lean_object* v_inst_10_, lean_object* v_toPure_11_, lean_object* v_____do__lift_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0(v_inst_10_, v_toPure_11_, v_____do__lift_12_);
lean_dec_ref(v_____do__lift_12_);
lean_dec_ref(v_inst_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v_toApplicative_20_; lean_object* v_toBind_21_; lean_object* v_toPure_22_; lean_object* v___x_23_; lean_object* v___f_24_; lean_object* v___x_25_; 
v_toApplicative_20_ = lean_ctor_get(v_inst_16_, 0);
v_toBind_21_ = lean_ctor_get(v_inst_16_, 1);
lean_inc(v_toBind_21_);
v_toPure_22_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_inc(v_toPure_22_);
v___x_23_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_14_, v_inst_15_, v_inst_16_, v_inst_17_, v_inst_18_);
v___f_24_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_24_, 0, v_inst_19_);
lean_closure_set(v___f_24_, 1, v_toPure_22_);
v___x_25_ = lean_apply_4(v_toBind_21_, lean_box(0), lean_box(0), v___x_23_, v___f_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst(lean_object* v_m_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_27_, v_inst_28_, v_inst_29_, v_inst_30_, v_inst_31_, v_inst_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isMulInst___redArg(lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v_toApplicative_40_; lean_object* v_toBind_41_; lean_object* v_toPure_42_; lean_object* v___x_43_; lean_object* v___f_44_; lean_object* v___x_45_; 
v_toApplicative_40_ = lean_ctor_get(v_inst_36_, 0);
v_toBind_41_ = lean_ctor_get(v_inst_36_, 1);
lean_inc(v_toBind_41_);
v_toPure_42_ = lean_ctor_get(v_toApplicative_40_, 1);
lean_inc(v_toPure_42_);
v___x_43_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_34_, v_inst_35_, v_inst_36_, v_inst_37_, v_inst_38_);
v___f_44_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_44_, 0, v_inst_39_);
lean_closure_set(v___f_44_, 1, v_toPure_42_);
v___x_45_ = lean_apply_4(v_toBind_41_, lean_box(0), lean_box(0), v___x_43_, v___f_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isMulInst(lean_object* v_m_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_47_, v_inst_48_, v_inst_49_, v_inst_50_, v_inst_51_, v_inst_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isSubInst___redArg(lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v_toApplicative_60_; lean_object* v_toBind_61_; lean_object* v_toPure_62_; lean_object* v___x_63_; lean_object* v___f_64_; lean_object* v___x_65_; 
v_toApplicative_60_ = lean_ctor_get(v_inst_56_, 0);
v_toBind_61_ = lean_ctor_get(v_inst_56_, 1);
lean_inc(v_toBind_61_);
v_toPure_62_ = lean_ctor_get(v_toApplicative_60_, 1);
lean_inc(v_toPure_62_);
v___x_63_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_54_, v_inst_55_, v_inst_56_, v_inst_57_, v_inst_58_);
v___f_64_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_64_, 0, v_inst_59_);
lean_closure_set(v___f_64_, 1, v_toPure_62_);
v___x_65_ = lean_apply_4(v_toBind_61_, lean_box(0), lean_box(0), v___x_63_, v___f_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isSubInst(lean_object* v_m_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_67_, v_inst_68_, v_inst_69_, v_inst_70_, v_inst_71_, v_inst_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___redArg(lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v_toApplicative_80_; lean_object* v_toBind_81_; lean_object* v_toPure_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___x_85_; 
v_toApplicative_80_ = lean_ctor_get(v_inst_76_, 0);
v_toBind_81_ = lean_ctor_get(v_inst_76_, 1);
lean_inc(v_toBind_81_);
v_toPure_82_ = lean_ctor_get(v_toApplicative_80_, 1);
lean_inc(v_toPure_82_);
v___x_83_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_74_, v_inst_75_, v_inst_76_, v_inst_77_, v_inst_78_);
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_84_, 0, v_inst_79_);
lean_closure_set(v___f_84_, 1, v_toPure_82_);
v___x_85_ = lean_apply_4(v_toBind_81_, lean_box(0), lean_box(0), v___x_83_, v___f_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst(lean_object* v_m_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_87_, v_inst_88_, v_inst_89_, v_inst_90_, v_inst_91_, v_inst_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isPowInst___redArg(lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_){
_start:
{
lean_object* v_toApplicative_100_; lean_object* v_toBind_101_; lean_object* v_toPure_102_; lean_object* v___x_103_; lean_object* v___f_104_; lean_object* v___x_105_; 
v_toApplicative_100_ = lean_ctor_get(v_inst_96_, 0);
v_toBind_101_ = lean_ctor_get(v_inst_96_, 1);
lean_inc(v_toBind_101_);
v_toPure_102_ = lean_ctor_get(v_toApplicative_100_, 1);
lean_inc(v_toPure_102_);
v___x_103_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_94_, v_inst_95_, v_inst_96_, v_inst_97_, v_inst_98_);
v___f_104_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_104_, 0, v_inst_99_);
lean_closure_set(v___f_104_, 1, v_toPure_102_);
v___x_105_ = lean_apply_4(v_toBind_101_, lean_box(0), lean_box(0), v___x_103_, v___f_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isPowInst(lean_object* v_m_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_){
_start:
{
lean_object* v_toApplicative_119_; lean_object* v_toBind_120_; lean_object* v_toPure_121_; lean_object* v___x_122_; lean_object* v___f_123_; lean_object* v___x_124_; 
v_toApplicative_119_ = lean_ctor_get(v_inst_115_, 0);
v_toBind_120_ = lean_ctor_get(v_inst_115_, 1);
lean_inc(v_toBind_120_);
v_toPure_121_ = lean_ctor_get(v_toApplicative_119_, 1);
lean_inc(v_toPure_121_);
v___x_122_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_114_, v_inst_115_, v_inst_116_, v_inst_117_);
v___f_123_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_123_, 0, v_inst_118_);
lean_closure_set(v___f_123_, 1, v_toPure_121_);
v___x_124_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_122_, v___f_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isIntCastInst(lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_, v_inst_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_){
_start:
{
lean_object* v_toApplicative_137_; lean_object* v_toBind_138_; lean_object* v_toPure_139_; lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___x_142_; 
v_toApplicative_137_ = lean_ctor_get(v_inst_133_, 0);
v_toBind_138_ = lean_ctor_get(v_inst_133_, 1);
lean_inc(v_toBind_138_);
v_toPure_139_ = lean_ctor_get(v_toApplicative_137_, 1);
lean_inc(v_toPure_139_);
v___x_140_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_132_, v_inst_133_, v_inst_134_, v_inst_135_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_141_, 0, v_inst_136_);
lean_closure_set(v___f_141_, 1, v_toPure_139_);
v___x_142_ = lean_apply_4(v_toBind_138_, lean_box(0), lean_box(0), v___x_140_, v___f_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNatCastInst(lean_object* v_m_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_144_, v_inst_145_, v_inst_146_, v_inst_147_, v_inst_148_);
return v___x_149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0));
v___x_152_ = l_Lean_stringToMessageData(v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(lean_object* v_inst_153_, lean_object* v_e_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_155_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1, &l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1);
v___x_156_ = l_Lean_indentExpr(v_e_154_);
v___x_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_reportIssueIfVerbose___boxed), 8, 1);
lean_closure_set(v___x_158_, 0, v___x_157_);
v___x_159_ = lean_apply_2(v_inst_153_, lean_box(0), v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue(lean_object* v_m_160_, lean_object* v_inst_161_, lean_object* v_e_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_161_, v_e_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0(lean_object* v_toPure_164_, lean_object* v_____do__lift_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_166_, 0, v_____do__lift_165_);
v___x_167_ = lean_apply_2(v_toPure_164_, lean_box(0), v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1(lean_object* v_____do__lift_168_, lean_object* v_toPure_169_, lean_object* v_____do__lift_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_171_, 0, v_____do__lift_168_);
lean_ctor_set(v___x_171_, 1, v_____do__lift_170_);
v___x_172_ = lean_apply_2(v_toPure_169_, lean_box(0), v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(lean_object* v_asVar_173_, lean_object* v_e_174_, lean_object* v_arg_175_, lean_object* v_toPure_176_, lean_object* v_toVar_177_, uint8_t v_____do__lift_178_){
_start:
{
if (v_____do__lift_178_ == 0)
{
lean_object* v___x_179_; 
lean_dec(v_toVar_177_);
lean_dec(v_toPure_176_);
lean_dec_ref(v_arg_175_);
v___x_179_ = lean_apply_1(v_asVar_173_, v_e_174_);
return v___x_179_;
}
else
{
lean_object* v___x_180_; 
lean_dec(v_asVar_173_);
v___x_180_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_175_);
if (lean_obj_tag(v___x_180_) == 1)
{
lean_object* v_val_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_189_; 
lean_dec(v_toVar_177_);
lean_dec_ref(v_e_174_);
v_val_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_189_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_val_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set_tag(v___x_183_, 2);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_val_181_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; 
v___x_187_ = lean_apply_2(v_toPure_176_, lean_box(0), v___x_186_);
return v___x_187_;
}
}
}
else
{
lean_object* v___x_190_; 
lean_dec(v___x_180_);
lean_dec(v_toPure_176_);
v___x_190_ = lean_apply_1(v_toVar_177_, v_e_174_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed(lean_object* v_asVar_191_, lean_object* v_e_192_, lean_object* v_arg_193_, lean_object* v_toPure_194_, lean_object* v_toVar_195_, lean_object* v_____do__lift_196_){
_start:
{
uint8_t v_____do__lift_4904__boxed_197_; lean_object* v_res_198_; 
v_____do__lift_4904__boxed_197_ = lean_unbox(v_____do__lift_196_);
v_res_198_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(v_asVar_191_, v_e_192_, v_arg_193_, v_toPure_194_, v_toVar_195_, v_____do__lift_4904__boxed_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7(lean_object* v_____do__lift_199_, lean_object* v_toPure_200_, lean_object* v_____do__lift_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_202_, 0, v_____do__lift_199_);
lean_ctor_set(v___x_202_, 1, v_____do__lift_201_);
v___x_203_ = lean_apply_2(v_toPure_200_, lean_box(0), v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4(lean_object* v_____do__lift_204_, lean_object* v_toPure_205_, lean_object* v_____do__lift_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_207_, 0, v_____do__lift_204_);
lean_ctor_set(v___x_207_, 1, v_____do__lift_206_);
v___x_208_ = lean_apply_2(v_toPure_205_, lean_box(0), v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9(lean_object* v_val_209_, lean_object* v_toPure_210_, lean_object* v_____do__lift_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_212_, 0, v_____do__lift_211_);
lean_ctor_set(v___x_212_, 1, v_val_209_);
v___x_213_ = lean_apply_2(v_toPure_210_, lean_box(0), v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(lean_object* v_asVar_214_, lean_object* v_e_215_, lean_object* v_arg_216_, lean_object* v_toPure_217_, lean_object* v_toVar_218_, uint8_t v_____do__lift_219_){
_start:
{
if (v_____do__lift_219_ == 0)
{
lean_object* v___x_220_; 
lean_dec(v_toVar_218_);
lean_dec(v_toPure_217_);
lean_dec_ref(v_arg_216_);
v___x_220_ = lean_apply_1(v_asVar_214_, v_e_215_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
lean_dec(v_asVar_214_);
v___x_221_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_216_);
if (lean_obj_tag(v___x_221_) == 1)
{
lean_object* v_val_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
lean_dec(v_toVar_218_);
lean_dec_ref(v_e_215_);
v_val_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_val_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_val_222_);
v___x_227_ = v_reuseFailAlloc_229_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; 
v___x_228_ = lean_apply_2(v_toPure_217_, lean_box(0), v___x_227_);
return v___x_228_;
}
}
}
else
{
lean_object* v___x_231_; 
lean_dec(v___x_221_);
lean_dec(v_toPure_217_);
v___x_231_ = lean_apply_1(v_toVar_218_, v_e_215_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed(lean_object* v_asVar_232_, lean_object* v_e_233_, lean_object* v_arg_234_, lean_object* v_toPure_235_, lean_object* v_toVar_236_, lean_object* v_____do__lift_237_){
_start:
{
uint8_t v_____do__lift_4958__boxed_238_; lean_object* v_res_239_; 
v_____do__lift_4958__boxed_238_ = lean_unbox(v_____do__lift_237_);
v_res_239_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(v_asVar_232_, v_e_233_, v_arg_234_, v_toPure_235_, v_toVar_236_, v_____do__lift_4958__boxed_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(lean_object* v_asVar_284_, lean_object* v_e_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_toVar_291_, lean_object* v_arg_292_, lean_object* v_toBind_293_, lean_object* v___f_294_, uint8_t v_____do__lift_295_){
_start:
{
if (v_____do__lift_295_ == 0)
{
lean_object* v___x_296_; 
lean_dec(v___f_294_);
lean_dec(v_toBind_293_);
lean_dec_ref(v_arg_292_);
lean_dec(v_toVar_291_);
lean_dec_ref(v_inst_290_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
lean_dec_ref(v_inst_287_);
lean_dec(v_inst_286_);
v___x_296_ = lean_apply_1(v_asVar_284_, v_e_285_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v_e_285_);
v___x_297_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_286_, v_inst_287_, v_inst_288_, v_inst_289_, v_inst_290_, v_toVar_291_, v_asVar_284_, v_arg_292_);
v___x_298_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v___x_297_, v___f_294_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed(lean_object* v_asVar_299_, lean_object* v_e_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_toVar_306_, lean_object* v_arg_307_, lean_object* v_toBind_308_, lean_object* v___f_309_, lean_object* v_____do__lift_310_){
_start:
{
uint8_t v_____do__lift_5068__boxed_311_; lean_object* v_res_312_; 
v_____do__lift_5068__boxed_311_ = lean_unbox(v_____do__lift_310_);
v_res_312_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(v_asVar_299_, v_e_300_, v_inst_301_, v_inst_302_, v_inst_303_, v_inst_304_, v_inst_305_, v_toVar_306_, v_arg_307_, v_toBind_308_, v___f_309_, v_____do__lift_5068__boxed_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5(lean_object* v_toPure_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_toVar_319_, lean_object* v_asVar_320_, lean_object* v_arg_321_, lean_object* v_toBind_322_, lean_object* v_____do__lift_323_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___f_324_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_324_, 0, v_____do__lift_323_);
lean_closure_set(v___f_324_, 1, v_toPure_313_);
v___x_325_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_314_, v_inst_315_, v_inst_316_, v_inst_317_, v_inst_318_, v_toVar_319_, v_asVar_320_, v_arg_321_);
v___x_326_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_325_, v___f_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6(lean_object* v_toPure_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_toVar_333_, lean_object* v_asVar_334_, lean_object* v_arg_335_, lean_object* v_toBind_336_, lean_object* v_____do__lift_337_){
_start:
{
lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___f_338_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7), 3, 2);
lean_closure_set(v___f_338_, 0, v_____do__lift_337_);
lean_closure_set(v___f_338_, 1, v_toPure_327_);
v___x_339_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_328_, v_inst_329_, v_inst_330_, v_inst_331_, v_inst_332_, v_toVar_333_, v_asVar_334_, v_arg_335_);
v___x_340_ = lean_apply_4(v_toBind_336_, lean_box(0), lean_box(0), v___x_339_, v___f_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10(lean_object* v_toVar_341_, lean_object* v_e_342_, lean_object* v_toPure_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_asVar_349_, lean_object* v_toBind_350_, lean_object* v___f_351_, lean_object* v_____x_352_){
_start:
{
lean_object* v_n_354_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = l_Lean_Expr_cleanupAnnotations(v_____x_352_);
v___x_369_ = l_Lean_Expr_isApp(v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec_ref(v___x_368_);
lean_dec(v___f_351_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_370_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_370_;
}
else
{
lean_object* v_arg_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_arg_371_ = lean_ctor_get(v___x_368_, 1);
lean_inc_ref(v_arg_371_);
v___x_372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_368_);
v___x_373_ = l_Lean_Expr_isApp(v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec_ref(v___x_372_);
lean_dec_ref(v_arg_371_);
lean_dec(v___f_351_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_374_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_374_;
}
else
{
lean_object* v_arg_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_arg_375_ = lean_ctor_get(v___x_372_, 1);
lean_inc_ref(v_arg_375_);
v___x_376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_372_);
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2));
v___x_378_ = l_Lean_Expr_isConstOf(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
uint8_t v___x_379_; 
v___x_379_ = l_Lean_Expr_isApp(v___x_376_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
lean_dec_ref(v___x_376_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_arg_371_);
lean_dec(v___f_351_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_380_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_380_;
}
else
{
lean_object* v_arg_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_arg_381_ = lean_ctor_get(v___x_376_, 1);
lean_inc_ref(v_arg_381_);
v___x_382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_376_);
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_384_ = l_Lean_Expr_isConstOf(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_386_ = l_Lean_Expr_isConstOf(v___x_382_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10));
v___x_388_ = l_Lean_Expr_isConstOf(v___x_382_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13));
v___x_390_ = l_Lean_Expr_isConstOf(v___x_382_, v___x_389_);
if (v___x_390_ == 0)
{
uint8_t v___x_391_; 
lean_dec(v___f_351_);
v___x_391_ = l_Lean_Expr_isApp(v___x_382_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_arg_371_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_392_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = l_Lean_Expr_appFnCleanup___redArg(v___x_382_);
v___x_394_ = l_Lean_Expr_isApp(v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_dec_ref(v___x_393_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_arg_371_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_395_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_393_);
v___x_397_ = l_Lean_Expr_isApp(v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v___x_396_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_arg_371_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_398_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_396_);
v___x_400_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_401_ = l_Lean_Expr_isConstOf(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19));
v___x_403_ = l_Lean_Expr_isConstOf(v___x_399_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_405_ = l_Lean_Expr_isConstOf(v___x_399_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_407_ = l_Lean_Expr_isConstOf(v___x_399_, v___x_406_);
lean_dec_ref(v___x_399_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_arg_371_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_408_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_408_;
}
else
{
lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_inc_n(v_toBind_350_, 2);
lean_inc(v_asVar_349_);
lean_inc(v_toVar_341_);
lean_inc_ref_n(v_inst_348_, 2);
lean_inc_ref_n(v_inst_347_, 2);
lean_inc_ref_n(v_inst_346_, 2);
lean_inc_ref_n(v_inst_345_, 2);
lean_inc_n(v_inst_344_, 2);
v___f_409_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2), 11, 10);
lean_closure_set(v___f_409_, 0, v_toPure_343_);
lean_closure_set(v___f_409_, 1, v_inst_344_);
lean_closure_set(v___f_409_, 2, v_inst_345_);
lean_closure_set(v___f_409_, 3, v_inst_346_);
lean_closure_set(v___f_409_, 4, v_inst_347_);
lean_closure_set(v___f_409_, 5, v_inst_348_);
lean_closure_set(v___f_409_, 6, v_toVar_341_);
lean_closure_set(v___f_409_, 7, v_asVar_349_);
lean_closure_set(v___f_409_, 8, v_arg_371_);
lean_closure_set(v___f_409_, 9, v_toBind_350_);
v___f_410_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_410_, 0, v_asVar_349_);
lean_closure_set(v___f_410_, 1, v_e_342_);
lean_closure_set(v___f_410_, 2, v_inst_344_);
lean_closure_set(v___f_410_, 3, v_inst_345_);
lean_closure_set(v___f_410_, 4, v_inst_346_);
lean_closure_set(v___f_410_, 5, v_inst_347_);
lean_closure_set(v___f_410_, 6, v_inst_348_);
lean_closure_set(v___f_410_, 7, v_toVar_341_);
lean_closure_set(v___f_410_, 8, v_arg_375_);
lean_closure_set(v___f_410_, 9, v_toBind_350_);
lean_closure_set(v___f_410_, 10, v___f_409_);
v___x_411_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_381_);
v___x_412_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_411_, v___f_410_);
return v___x_412_;
}
}
else
{
lean_object* v___f_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec_ref(v___x_399_);
lean_inc_n(v_toBind_350_, 2);
lean_inc(v_asVar_349_);
lean_inc(v_toVar_341_);
lean_inc_ref_n(v_inst_348_, 2);
lean_inc_ref_n(v_inst_347_, 2);
lean_inc_ref_n(v_inst_346_, 2);
lean_inc_ref_n(v_inst_345_, 2);
lean_inc_n(v_inst_344_, 2);
v___f_413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5), 11, 10);
lean_closure_set(v___f_413_, 0, v_toPure_343_);
lean_closure_set(v___f_413_, 1, v_inst_344_);
lean_closure_set(v___f_413_, 2, v_inst_345_);
lean_closure_set(v___f_413_, 3, v_inst_346_);
lean_closure_set(v___f_413_, 4, v_inst_347_);
lean_closure_set(v___f_413_, 5, v_inst_348_);
lean_closure_set(v___f_413_, 6, v_toVar_341_);
lean_closure_set(v___f_413_, 7, v_asVar_349_);
lean_closure_set(v___f_413_, 8, v_arg_371_);
lean_closure_set(v___f_413_, 9, v_toBind_350_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_414_, 0, v_asVar_349_);
lean_closure_set(v___f_414_, 1, v_e_342_);
lean_closure_set(v___f_414_, 2, v_inst_344_);
lean_closure_set(v___f_414_, 3, v_inst_345_);
lean_closure_set(v___f_414_, 4, v_inst_346_);
lean_closure_set(v___f_414_, 5, v_inst_347_);
lean_closure_set(v___f_414_, 6, v_inst_348_);
lean_closure_set(v___f_414_, 7, v_toVar_341_);
lean_closure_set(v___f_414_, 8, v_arg_375_);
lean_closure_set(v___f_414_, 9, v_toBind_350_);
lean_closure_set(v___f_414_, 10, v___f_413_);
v___x_415_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_381_);
v___x_416_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_415_, v___f_414_);
return v___x_416_;
}
}
else
{
lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec_ref(v___x_399_);
lean_inc_n(v_toBind_350_, 2);
lean_inc(v_asVar_349_);
lean_inc(v_toVar_341_);
lean_inc_ref_n(v_inst_348_, 2);
lean_inc_ref_n(v_inst_347_, 2);
lean_inc_ref_n(v_inst_346_, 2);
lean_inc_ref_n(v_inst_345_, 2);
lean_inc_n(v_inst_344_, 2);
v___f_417_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6), 11, 10);
lean_closure_set(v___f_417_, 0, v_toPure_343_);
lean_closure_set(v___f_417_, 1, v_inst_344_);
lean_closure_set(v___f_417_, 2, v_inst_345_);
lean_closure_set(v___f_417_, 3, v_inst_346_);
lean_closure_set(v___f_417_, 4, v_inst_347_);
lean_closure_set(v___f_417_, 5, v_inst_348_);
lean_closure_set(v___f_417_, 6, v_toVar_341_);
lean_closure_set(v___f_417_, 7, v_asVar_349_);
lean_closure_set(v___f_417_, 8, v_arg_371_);
lean_closure_set(v___f_417_, 9, v_toBind_350_);
v___f_418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_418_, 0, v_asVar_349_);
lean_closure_set(v___f_418_, 1, v_e_342_);
lean_closure_set(v___f_418_, 2, v_inst_344_);
lean_closure_set(v___f_418_, 3, v_inst_345_);
lean_closure_set(v___f_418_, 4, v_inst_346_);
lean_closure_set(v___f_418_, 5, v_inst_347_);
lean_closure_set(v___f_418_, 6, v_inst_348_);
lean_closure_set(v___f_418_, 7, v_toVar_341_);
lean_closure_set(v___f_418_, 8, v_arg_375_);
lean_closure_set(v___f_418_, 9, v_toBind_350_);
lean_closure_set(v___f_418_, 10, v___f_417_);
v___x_419_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_381_);
v___x_420_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_419_, v___f_418_);
return v___x_420_;
}
}
else
{
lean_object* v___x_421_; 
lean_dec_ref(v___x_399_);
v___x_421_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_371_);
if (lean_obj_tag(v___x_421_) == 1)
{
lean_object* v_val_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_val_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v___x_421_, 1);
v___f_423_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9), 3, 2);
lean_closure_set(v___f_423_, 0, v_val_422_);
lean_closure_set(v___f_423_, 1, v_toPure_343_);
lean_inc(v_toBind_350_);
lean_inc_ref(v_inst_348_);
lean_inc_ref(v_inst_347_);
lean_inc_ref(v_inst_346_);
lean_inc_ref(v_inst_345_);
lean_inc(v_inst_344_);
v___f_424_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_424_, 0, v_asVar_349_);
lean_closure_set(v___f_424_, 1, v_e_342_);
lean_closure_set(v___f_424_, 2, v_inst_344_);
lean_closure_set(v___f_424_, 3, v_inst_345_);
lean_closure_set(v___f_424_, 4, v_inst_346_);
lean_closure_set(v___f_424_, 5, v_inst_347_);
lean_closure_set(v___f_424_, 6, v_inst_348_);
lean_closure_set(v___f_424_, 7, v_toVar_341_);
lean_closure_set(v___f_424_, 8, v_arg_375_);
lean_closure_set(v___f_424_, 9, v_toBind_350_);
lean_closure_set(v___f_424_, 10, v___f_423_);
v___x_425_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_381_);
v___x_426_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_425_, v___f_424_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
lean_dec(v___x_421_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_375_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_427_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_427_;
}
}
}
}
}
}
else
{
lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_arg_381_);
lean_dec(v_toPure_343_);
lean_inc(v_toBind_350_);
lean_inc_ref(v_inst_348_);
lean_inc_ref(v_inst_347_);
lean_inc_ref(v_inst_346_);
lean_inc_ref(v_inst_345_);
lean_inc(v_inst_344_);
v___f_428_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_428_, 0, v_asVar_349_);
lean_closure_set(v___f_428_, 1, v_e_342_);
lean_closure_set(v___f_428_, 2, v_inst_344_);
lean_closure_set(v___f_428_, 3, v_inst_345_);
lean_closure_set(v___f_428_, 4, v_inst_346_);
lean_closure_set(v___f_428_, 5, v_inst_347_);
lean_closure_set(v___f_428_, 6, v_inst_348_);
lean_closure_set(v___f_428_, 7, v_toVar_341_);
lean_closure_set(v___f_428_, 8, v_arg_371_);
lean_closure_set(v___f_428_, 9, v_toBind_350_);
lean_closure_set(v___f_428_, 10, v___f_351_);
v___x_429_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_375_);
v___x_430_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_429_, v___f_428_);
return v___x_430_;
}
}
else
{
lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_arg_381_);
lean_dec(v___f_351_);
lean_dec_ref(v_inst_345_);
v___f_431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_431_, 0, v_asVar_349_);
lean_closure_set(v___f_431_, 1, v_e_342_);
lean_closure_set(v___f_431_, 2, v_arg_371_);
lean_closure_set(v___f_431_, 3, v_toPure_343_);
lean_closure_set(v___f_431_, 4, v_toVar_341_);
v___x_432_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_344_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_375_);
v___x_433_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_432_, v___f_431_);
return v___x_433_;
}
}
else
{
lean_object* v___f_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_arg_381_);
lean_dec(v___f_351_);
lean_dec_ref(v_inst_345_);
v___f_434_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed), 6, 5);
lean_closure_set(v___f_434_, 0, v_asVar_349_);
lean_closure_set(v___f_434_, 1, v_e_342_);
lean_closure_set(v___f_434_, 2, v_arg_371_);
lean_closure_set(v___f_434_, 3, v_toPure_343_);
lean_closure_set(v___f_434_, 4, v_toVar_341_);
v___x_435_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_344_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_375_);
v___x_436_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_435_, v___f_434_);
return v___x_436_;
}
}
else
{
lean_dec_ref(v___x_382_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_371_);
lean_dec(v___f_351_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
v_n_354_ = v_arg_375_;
goto v___jp_353_;
}
}
}
else
{
lean_dec_ref(v___x_376_);
lean_dec_ref(v_arg_375_);
lean_dec(v___f_351_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
v_n_354_ = v_arg_371_;
goto v___jp_353_;
}
}
}
v___jp_353_:
{
if (lean_obj_tag(v_n_354_) == 9)
{
lean_object* v_a_355_; 
v_a_355_ = lean_ctor_get(v_n_354_, 0);
lean_inc_ref(v_a_355_);
lean_dec_ref_known(v_n_354_, 1);
if (lean_obj_tag(v_a_355_) == 0)
{
lean_object* v_val_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_e_342_);
lean_dec(v_toVar_341_);
v_val_356_ = lean_ctor_get(v_a_355_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_a_355_);
if (v_isSharedCheck_365_ == 0)
{
v___x_358_ = v_a_355_;
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_val_356_);
lean_dec(v_a_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_nat_to_int(v_val_356_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_apply_2(v_toPure_343_, lean_box(0), v___x_362_);
return v___x_363_;
}
}
}
else
{
lean_object* v___x_366_; 
lean_dec_ref(v_a_355_);
lean_dec(v_toPure_343_);
v___x_366_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_366_;
}
}
else
{
lean_object* v___x_367_; 
lean_dec_ref(v_n_354_);
lean_dec(v_toPure_343_);
v___x_367_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_toVar_442_, lean_object* v_asVar_443_, lean_object* v_e_444_){
_start:
{
lean_object* v_toApplicative_445_; lean_object* v_toBind_446_; lean_object* v_toPure_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___f_450_; lean_object* v___f_451_; lean_object* v___x_452_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_439_, 0);
v_toBind_446_ = lean_ctor_get(v_inst_439_, 1);
lean_inc_n(v_toBind_446_, 2);
v_toPure_447_ = lean_ctor_get(v_toApplicative_445_, 1);
lean_inc_n(v_toPure_447_, 2);
lean_inc_ref(v_e_444_);
v___x_448_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_448_, 0, v_e_444_);
lean_inc(v_inst_437_);
v___x_449_ = lean_apply_2(v_inst_437_, lean_box(0), v___x_448_);
v___f_450_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_450_, 0, v_toPure_447_);
v___f_451_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10), 12, 11);
lean_closure_set(v___f_451_, 0, v_toVar_442_);
lean_closure_set(v___f_451_, 1, v_e_444_);
lean_closure_set(v___f_451_, 2, v_toPure_447_);
lean_closure_set(v___f_451_, 3, v_inst_437_);
lean_closure_set(v___f_451_, 4, v_inst_438_);
lean_closure_set(v___f_451_, 5, v_inst_439_);
lean_closure_set(v___f_451_, 6, v_inst_440_);
lean_closure_set(v___f_451_, 7, v_inst_441_);
lean_closure_set(v___f_451_, 8, v_asVar_443_);
lean_closure_set(v___f_451_, 9, v_toBind_446_);
lean_closure_set(v___f_451_, 10, v___f_450_);
v___x_452_ = lean_apply_4(v_toBind_446_, lean_box(0), lean_box(0), v___x_449_, v___f_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2(lean_object* v_toPure_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_toVar_459_, lean_object* v_asVar_460_, lean_object* v_arg_461_, lean_object* v_toBind_462_, lean_object* v_____do__lift_463_){
_start:
{
lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___f_464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_464_, 0, v_____do__lift_463_);
lean_closure_set(v___f_464_, 1, v_toPure_453_);
v___x_465_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_454_, v_inst_455_, v_inst_456_, v_inst_457_, v_inst_458_, v_toVar_459_, v_asVar_460_, v_arg_461_);
v___x_466_ = lean_apply_4(v_toBind_462_, lean_box(0), lean_box(0), v___x_465_, v___f_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go(lean_object* v_m_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_toVar_473_, lean_object* v_asVar_474_, lean_object* v_e_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_468_, v_inst_469_, v_inst_470_, v_inst_471_, v_inst_472_, v_toVar_473_, v_asVar_474_, v_e_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0(lean_object* v_toPure_477_, lean_object* v_____do__lift_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_479_, 0, v_____do__lift_478_);
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___x_481_ = lean_apply_2(v_toPure_477_, lean_box(0), v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1(lean_object* v_toPure_482_, lean_object* v_____do__lift_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_____do__lift_483_);
v___x_485_ = lean_apply_2(v_toPure_482_, lean_box(0), v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2(lean_object* v_toPure_486_, lean_object* v_____do__lift_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v_____do__lift_487_);
v___x_489_ = lean_apply_2(v_toPure_486_, lean_box(0), v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3(lean_object* v_inst_490_, lean_object* v_e_491_, lean_object* v_toBind_492_, lean_object* v___f_493_, lean_object* v_____r_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_apply_1(v_inst_490_, v_e_491_);
v___x_496_ = lean_apply_4(v_toBind_492_, lean_box(0), lean_box(0), v___x_495_, v___f_493_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4(lean_object* v_inst_497_, lean_object* v_toBind_498_, lean_object* v___f_499_, lean_object* v_inst_500_, lean_object* v_e_501_){
_start:
{
lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc(v_toBind_498_);
lean_inc_ref(v_e_501_);
v___f_502_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_502_, 0, v_inst_497_);
lean_closure_set(v___f_502_, 1, v_e_501_);
lean_closure_set(v___f_502_, 2, v_toBind_498_);
lean_closure_set(v___f_502_, 3, v___f_499_);
v___x_503_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_500_, v_e_501_);
v___x_504_ = lean_apply_4(v_toBind_498_, lean_box(0), lean_box(0), v___x_503_, v___f_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6(lean_object* v_inst_505_, lean_object* v_toBind_506_, lean_object* v___f_507_, lean_object* v_e_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_apply_1(v_inst_505_, v_e_508_);
v___x_510_ = lean_apply_4(v_toBind_506_, lean_box(0), lean_box(0), v___x_509_, v___f_507_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(uint8_t v_skipVar_511_, lean_object* v_toVar_512_, lean_object* v_toBind_513_, lean_object* v___f_514_, lean_object* v_toPure_515_, lean_object* v_e_516_){
_start:
{
if (v_skipVar_511_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_toPure_515_);
v___x_517_ = lean_apply_1(v_toVar_512_, v_e_516_);
v___x_518_ = lean_apply_4(v_toBind_513_, lean_box(0), lean_box(0), v___x_517_, v___f_514_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref(v_e_516_);
lean_dec(v___f_514_);
lean_dec(v_toBind_513_);
lean_dec(v_toVar_512_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_apply_2(v_toPure_515_, lean_box(0), v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed(lean_object* v_skipVar_521_, lean_object* v_toVar_522_, lean_object* v_toBind_523_, lean_object* v___f_524_, lean_object* v_toPure_525_, lean_object* v_e_526_){
_start:
{
uint8_t v_skipVar_boxed_527_; lean_object* v_res_528_; 
v_skipVar_boxed_527_ = lean_unbox(v_skipVar_521_);
v_res_528_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(v_skipVar_boxed_527_, v_toVar_522_, v_toBind_523_, v___f_524_, v_toPure_525_, v_e_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7(lean_object* v_toTopVar_529_, lean_object* v_e_530_, lean_object* v_____r_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_apply_1(v_toTopVar_529_, v_e_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8(lean_object* v_toTopVar_533_, lean_object* v_inst_534_, lean_object* v_toBind_535_, lean_object* v_e_536_){
_start:
{
lean_object* v___f_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_inc_ref(v_e_536_);
v___f_537_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7), 3, 2);
lean_closure_set(v___f_537_, 0, v_toTopVar_533_);
lean_closure_set(v___f_537_, 1, v_e_536_);
v___x_538_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_534_, v_e_536_);
v___x_539_ = lean_apply_4(v_toBind_535_, lean_box(0), lean_box(0), v___x_538_, v___f_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9(lean_object* v_____do__lift_540_, lean_object* v_toPure_541_, lean_object* v_____do__lift_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v_____do__lift_540_);
lean_ctor_set(v___x_543_, 1, v_____do__lift_542_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_apply_2(v_toPure_541_, lean_box(0), v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10(lean_object* v_toPure_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_toVar_552_, lean_object* v_asVar_553_, lean_object* v_arg_554_, lean_object* v_toBind_555_, lean_object* v_____do__lift_556_){
_start:
{
lean_object* v___f_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___f_557_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9), 3, 2);
lean_closure_set(v___f_557_, 0, v_____do__lift_556_);
lean_closure_set(v___f_557_, 1, v_toPure_546_);
v___x_558_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_547_, v_inst_548_, v_inst_549_, v_inst_550_, v_inst_551_, v_toVar_552_, v_asVar_553_, v_arg_554_);
v___x_559_ = lean_apply_4(v_toBind_555_, lean_box(0), lean_box(0), v___x_558_, v___f_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(lean_object* v_asTopVar_560_, lean_object* v_e_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_toVar_567_, lean_object* v_asVar_568_, lean_object* v_arg_569_, lean_object* v_toBind_570_, lean_object* v___f_571_, uint8_t v_____do__lift_572_){
_start:
{
if (v_____do__lift_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v___f_571_);
lean_dec(v_toBind_570_);
lean_dec_ref(v_arg_569_);
lean_dec(v_asVar_568_);
lean_dec(v_toVar_567_);
lean_dec_ref(v_inst_566_);
lean_dec_ref(v_inst_565_);
lean_dec_ref(v_inst_564_);
lean_dec_ref(v_inst_563_);
lean_dec(v_inst_562_);
v___x_573_ = lean_apply_1(v_asTopVar_560_, v_e_561_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v_e_561_);
lean_dec(v_asTopVar_560_);
v___x_574_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_562_, v_inst_563_, v_inst_564_, v_inst_565_, v_inst_566_, v_toVar_567_, v_asVar_568_, v_arg_569_);
v___x_575_ = lean_apply_4(v_toBind_570_, lean_box(0), lean_box(0), v___x_574_, v___f_571_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed(lean_object* v_asTopVar_576_, lean_object* v_e_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_toVar_583_, lean_object* v_asVar_584_, lean_object* v_arg_585_, lean_object* v_toBind_586_, lean_object* v___f_587_, lean_object* v_____do__lift_588_){
_start:
{
uint8_t v_____do__lift_4902__boxed_589_; lean_object* v_res_590_; 
v_____do__lift_4902__boxed_589_ = lean_unbox(v_____do__lift_588_);
v_res_590_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(v_asTopVar_576_, v_e_577_, v_inst_578_, v_inst_579_, v_inst_580_, v_inst_581_, v_inst_582_, v_toVar_583_, v_asVar_584_, v_arg_585_, v_toBind_586_, v___f_587_, v_____do__lift_4902__boxed_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12(lean_object* v_____do__lift_591_, lean_object* v_toPure_592_, lean_object* v_____do__lift_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v_____do__lift_591_);
lean_ctor_set(v___x_594_, 1, v_____do__lift_593_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
v___x_596_ = lean_apply_2(v_toPure_592_, lean_box(0), v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13(lean_object* v_toPure_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_toVar_603_, lean_object* v_asVar_604_, lean_object* v_arg_605_, lean_object* v_toBind_606_, lean_object* v_____do__lift_607_){
_start:
{
lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___f_608_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12), 3, 2);
lean_closure_set(v___f_608_, 0, v_____do__lift_607_);
lean_closure_set(v___f_608_, 1, v_toPure_597_);
v___x_609_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_598_, v_inst_599_, v_inst_600_, v_inst_601_, v_inst_602_, v_toVar_603_, v_asVar_604_, v_arg_605_);
v___x_610_ = lean_apply_4(v_toBind_606_, lean_box(0), lean_box(0), v___x_609_, v___f_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15(lean_object* v_____do__lift_611_, lean_object* v_toPure_612_, lean_object* v_____do__lift_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_614_, 0, v_____do__lift_611_);
lean_ctor_set(v___x_614_, 1, v_____do__lift_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = lean_apply_2(v_toPure_612_, lean_box(0), v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14(lean_object* v_toPure_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_toVar_623_, lean_object* v_asVar_624_, lean_object* v_arg_625_, lean_object* v_toBind_626_, lean_object* v_____do__lift_627_){
_start:
{
lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15), 3, 2);
lean_closure_set(v___f_628_, 0, v_____do__lift_627_);
lean_closure_set(v___f_628_, 1, v_toPure_617_);
v___x_629_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_618_, v_inst_619_, v_inst_620_, v_inst_621_, v_inst_622_, v_toVar_623_, v_asVar_624_, v_arg_625_);
v___x_630_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_629_, v___f_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17(lean_object* v_val_631_, lean_object* v_toPure_632_, lean_object* v_____do__lift_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_634_, 0, v_____do__lift_633_);
lean_ctor_set(v___x_634_, 1, v_val_631_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = lean_apply_2(v_toPure_632_, lean_box(0), v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(lean_object* v_asTopVar_637_, lean_object* v_e_638_, lean_object* v_arg_639_, lean_object* v_toPure_640_, lean_object* v_toTopVar_641_, uint8_t v_____do__lift_642_){
_start:
{
if (v_____do__lift_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v_toTopVar_641_);
lean_dec(v_toPure_640_);
lean_dec_ref(v_arg_639_);
v___x_643_ = lean_apply_1(v_asTopVar_637_, v_e_638_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; 
lean_dec(v_asTopVar_637_);
v___x_644_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_639_);
if (lean_obj_tag(v___x_644_) == 1)
{
lean_object* v_val_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_toTopVar_641_);
lean_dec_ref(v_e_638_);
v_val_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_654_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_val_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_649_, 0, v_val_645_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; 
v___x_652_ = lean_apply_2(v_toPure_640_, lean_box(0), v___x_651_);
return v___x_652_;
}
}
}
else
{
lean_object* v___x_655_; 
lean_dec(v___x_644_);
lean_dec(v_toPure_640_);
v___x_655_ = lean_apply_1(v_toTopVar_641_, v_e_638_);
return v___x_655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed(lean_object* v_asTopVar_656_, lean_object* v_e_657_, lean_object* v_arg_658_, lean_object* v_toPure_659_, lean_object* v_toTopVar_660_, lean_object* v_____do__lift_661_){
_start:
{
uint8_t v_____do__lift_4996__boxed_662_; lean_object* v_res_663_; 
v_____do__lift_4996__boxed_662_ = lean_unbox(v_____do__lift_661_);
v_res_663_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(v_asTopVar_656_, v_e_657_, v_arg_658_, v_toPure_659_, v_toTopVar_660_, v_____do__lift_4996__boxed_662_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(lean_object* v_asTopVar_664_, lean_object* v_e_665_, lean_object* v_arg_666_, lean_object* v_toPure_667_, lean_object* v_toTopVar_668_, uint8_t v_____do__lift_669_){
_start:
{
if (v_____do__lift_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v_toTopVar_668_);
lean_dec(v_toPure_667_);
lean_dec_ref(v_arg_666_);
v___x_670_ = lean_apply_1(v_asTopVar_664_, v_e_665_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; 
lean_dec(v_asTopVar_664_);
v___x_671_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_666_);
if (lean_obj_tag(v___x_671_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_toTopVar_668_);
lean_dec_ref(v_e_665_);
v_val_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_val_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v_val_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_680_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; 
v___x_679_ = lean_apply_2(v_toPure_667_, lean_box(0), v___x_678_);
return v___x_679_;
}
}
}
else
{
lean_object* v___x_682_; 
lean_dec(v___x_671_);
lean_dec(v_toPure_667_);
v___x_682_ = lean_apply_1(v_toTopVar_668_, v_e_665_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed(lean_object* v_asTopVar_683_, lean_object* v_e_684_, lean_object* v_arg_685_, lean_object* v_toPure_686_, lean_object* v_toTopVar_687_, lean_object* v_____do__lift_688_){
_start:
{
uint8_t v_____do__lift_5028__boxed_689_; lean_object* v_res_690_; 
v_____do__lift_5028__boxed_689_ = lean_unbox(v_____do__lift_688_);
v_res_690_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(v_asTopVar_683_, v_e_684_, v_arg_685_, v_toPure_686_, v_toTopVar_687_, v_____do__lift_5028__boxed_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18(lean_object* v_toTopVar_691_, lean_object* v_e_692_, lean_object* v_toPure_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_toVar_699_, lean_object* v_asVar_700_, lean_object* v_toBind_701_, lean_object* v_asTopVar_702_, lean_object* v___f_703_, lean_object* v_____x_704_){
_start:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = l_Lean_Expr_cleanupAnnotations(v_____x_704_);
v___x_706_ = l_Lean_Expr_isApp(v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec_ref(v___x_705_);
lean_dec(v___f_703_);
lean_dec(v_asTopVar_702_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toPure_693_);
v___x_707_ = lean_apply_1(v_toTopVar_691_, v_e_692_);
return v___x_707_;
}
else
{
lean_object* v_arg_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_arg_708_ = lean_ctor_get(v___x_705_, 1);
lean_inc_ref(v_arg_708_);
v___x_709_ = l_Lean_Expr_appFnCleanup___redArg(v___x_705_);
v___x_710_ = l_Lean_Expr_isApp(v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
lean_dec_ref(v___x_709_);
lean_dec_ref(v_arg_708_);
lean_dec(v___f_703_);
lean_dec(v_asTopVar_702_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toPure_693_);
v___x_711_ = lean_apply_1(v_toTopVar_691_, v_e_692_);
return v___x_711_;
}
else
{
lean_object* v_arg_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_arg_712_ = lean_ctor_get(v___x_709_, 1);
lean_inc_ref(v_arg_712_);
v___x_713_ = l_Lean_Expr_appFnCleanup___redArg(v___x_709_);
v___x_714_ = l_Lean_Expr_isApp(v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec_ref(v___x_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_708_);
lean_dec(v___f_703_);
lean_dec(v_asTopVar_702_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toPure_693_);
v___x_715_ = lean_apply_1(v_toTopVar_691_, v_e_692_);
return v___x_715_;
}
else
{
lean_object* v_arg_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_arg_716_ = lean_ctor_get(v___x_713_, 1);
lean_inc_ref(v_arg_716_);
v___x_717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_713_);
v___x_718_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_719_ = l_Lean_Expr_isConstOf(v___x_717_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_721_ = l_Lean_Expr_isConstOf(v___x_717_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10));
v___x_723_ = l_Lean_Expr_isConstOf(v___x_717_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13));
v___x_725_ = l_Lean_Expr_isConstOf(v___x_717_, v___x_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; 
lean_dec(v___f_703_);
v___x_726_ = l_Lean_Expr_isApp(v___x_717_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_arg_716_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_708_);
lean_dec(v_asTopVar_702_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toPure_693_);
v___x_727_ = lean_apply_1(v_toTopVar_691_, v_e_692_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = l_Lean_Expr_appFnCleanup___redArg(v___x_717_);
v___x_729_ = l_Lean_Expr_isApp(v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec_ref(v___x_728_);
lean_dec_ref(v_arg_716_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_708_);
lean_dec(v_asTopVar_702_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toPure_693_);
v___x_730_ = lean_apply_1(v_toTopVar_691_, v_e_692_);
return v___x_730_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = l_Lean_Expr_appFnCleanup___redArg(v___x_728_);
v___x_732_ = l_Lean_Expr_isApp(v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec_ref(v___x_731_);
lean_dec_ref(v_arg_716_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_708_);
lean_dec(v_asTopVar_702_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toPure_693_);
v___x_733_ = lean_apply_1(v_toTopVar_691_, v_e_692_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = l_Lean_Expr_appFnCleanup___redArg(v___x_731_);
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_736_ = l_Lean_Expr_isConstOf(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19));
v___x_738_ = l_Lean_Expr_isConstOf(v___x_734_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_740_ = l_Lean_Expr_isConstOf(v___x_734_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_742_ = l_Lean_Expr_isConstOf(v___x_734_, v___x_741_);
lean_dec_ref(v___x_734_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec_ref(v_arg_716_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_708_);
lean_dec(v_asTopVar_702_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toPure_693_);
v___x_743_ = lean_apply_1(v_toTopVar_691_, v_e_692_);
return v___x_743_;
}
else
{
lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_toTopVar_691_);
lean_inc_n(v_toBind_701_, 2);
lean_inc(v_asVar_700_);
lean_inc(v_toVar_699_);
lean_inc_ref_n(v_inst_698_, 2);
lean_inc_ref_n(v_inst_697_, 2);
lean_inc_ref_n(v_inst_696_, 2);
lean_inc_ref_n(v_inst_695_, 2);
lean_inc_n(v_inst_694_, 2);
v___f_744_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10), 11, 10);
lean_closure_set(v___f_744_, 0, v_toPure_693_);
lean_closure_set(v___f_744_, 1, v_inst_694_);
lean_closure_set(v___f_744_, 2, v_inst_695_);
lean_closure_set(v___f_744_, 3, v_inst_696_);
lean_closure_set(v___f_744_, 4, v_inst_697_);
lean_closure_set(v___f_744_, 5, v_inst_698_);
lean_closure_set(v___f_744_, 6, v_toVar_699_);
lean_closure_set(v___f_744_, 7, v_asVar_700_);
lean_closure_set(v___f_744_, 8, v_arg_708_);
lean_closure_set(v___f_744_, 9, v_toBind_701_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_745_, 0, v_asTopVar_702_);
lean_closure_set(v___f_745_, 1, v_e_692_);
lean_closure_set(v___f_745_, 2, v_inst_694_);
lean_closure_set(v___f_745_, 3, v_inst_695_);
lean_closure_set(v___f_745_, 4, v_inst_696_);
lean_closure_set(v___f_745_, 5, v_inst_697_);
lean_closure_set(v___f_745_, 6, v_inst_698_);
lean_closure_set(v___f_745_, 7, v_toVar_699_);
lean_closure_set(v___f_745_, 8, v_asVar_700_);
lean_closure_set(v___f_745_, 9, v_arg_712_);
lean_closure_set(v___f_745_, 10, v_toBind_701_);
lean_closure_set(v___f_745_, 11, v___f_744_);
v___x_746_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v_arg_716_);
v___x_747_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v___x_746_, v___f_745_);
return v___x_747_;
}
}
else
{
lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref(v___x_734_);
lean_dec(v_toTopVar_691_);
lean_inc_n(v_toBind_701_, 2);
lean_inc(v_asVar_700_);
lean_inc(v_toVar_699_);
lean_inc_ref_n(v_inst_698_, 2);
lean_inc_ref_n(v_inst_697_, 2);
lean_inc_ref_n(v_inst_696_, 2);
lean_inc_ref_n(v_inst_695_, 2);
lean_inc_n(v_inst_694_, 2);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13), 11, 10);
lean_closure_set(v___f_748_, 0, v_toPure_693_);
lean_closure_set(v___f_748_, 1, v_inst_694_);
lean_closure_set(v___f_748_, 2, v_inst_695_);
lean_closure_set(v___f_748_, 3, v_inst_696_);
lean_closure_set(v___f_748_, 4, v_inst_697_);
lean_closure_set(v___f_748_, 5, v_inst_698_);
lean_closure_set(v___f_748_, 6, v_toVar_699_);
lean_closure_set(v___f_748_, 7, v_asVar_700_);
lean_closure_set(v___f_748_, 8, v_arg_708_);
lean_closure_set(v___f_748_, 9, v_toBind_701_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_749_, 0, v_asTopVar_702_);
lean_closure_set(v___f_749_, 1, v_e_692_);
lean_closure_set(v___f_749_, 2, v_inst_694_);
lean_closure_set(v___f_749_, 3, v_inst_695_);
lean_closure_set(v___f_749_, 4, v_inst_696_);
lean_closure_set(v___f_749_, 5, v_inst_697_);
lean_closure_set(v___f_749_, 6, v_inst_698_);
lean_closure_set(v___f_749_, 7, v_toVar_699_);
lean_closure_set(v___f_749_, 8, v_asVar_700_);
lean_closure_set(v___f_749_, 9, v_arg_712_);
lean_closure_set(v___f_749_, 10, v_toBind_701_);
lean_closure_set(v___f_749_, 11, v___f_748_);
v___x_750_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v_arg_716_);
v___x_751_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v___x_750_, v___f_749_);
return v___x_751_;
}
}
else
{
lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref(v___x_734_);
lean_dec(v_toTopVar_691_);
lean_inc_n(v_toBind_701_, 2);
lean_inc(v_asVar_700_);
lean_inc(v_toVar_699_);
lean_inc_ref_n(v_inst_698_, 2);
lean_inc_ref_n(v_inst_697_, 2);
lean_inc_ref_n(v_inst_696_, 2);
lean_inc_ref_n(v_inst_695_, 2);
lean_inc_n(v_inst_694_, 2);
v___f_752_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14), 11, 10);
lean_closure_set(v___f_752_, 0, v_toPure_693_);
lean_closure_set(v___f_752_, 1, v_inst_694_);
lean_closure_set(v___f_752_, 2, v_inst_695_);
lean_closure_set(v___f_752_, 3, v_inst_696_);
lean_closure_set(v___f_752_, 4, v_inst_697_);
lean_closure_set(v___f_752_, 5, v_inst_698_);
lean_closure_set(v___f_752_, 6, v_toVar_699_);
lean_closure_set(v___f_752_, 7, v_asVar_700_);
lean_closure_set(v___f_752_, 8, v_arg_708_);
lean_closure_set(v___f_752_, 9, v_toBind_701_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_753_, 0, v_asTopVar_702_);
lean_closure_set(v___f_753_, 1, v_e_692_);
lean_closure_set(v___f_753_, 2, v_inst_694_);
lean_closure_set(v___f_753_, 3, v_inst_695_);
lean_closure_set(v___f_753_, 4, v_inst_696_);
lean_closure_set(v___f_753_, 5, v_inst_697_);
lean_closure_set(v___f_753_, 6, v_inst_698_);
lean_closure_set(v___f_753_, 7, v_toVar_699_);
lean_closure_set(v___f_753_, 8, v_asVar_700_);
lean_closure_set(v___f_753_, 9, v_arg_712_);
lean_closure_set(v___f_753_, 10, v_toBind_701_);
lean_closure_set(v___f_753_, 11, v___f_752_);
v___x_754_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v_arg_716_);
v___x_755_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v___x_754_, v___f_753_);
return v___x_755_;
}
}
else
{
lean_object* v___x_756_; 
lean_dec_ref(v___x_734_);
lean_dec(v_toTopVar_691_);
v___x_756_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_708_);
if (lean_obj_tag(v___x_756_) == 1)
{
lean_object* v_val_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_val_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v___x_756_, 1);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17), 3, 2);
lean_closure_set(v___f_758_, 0, v_val_757_);
lean_closure_set(v___f_758_, 1, v_toPure_693_);
lean_inc(v_toBind_701_);
lean_inc_ref(v_inst_698_);
lean_inc_ref(v_inst_697_);
lean_inc_ref(v_inst_696_);
lean_inc_ref(v_inst_695_);
lean_inc(v_inst_694_);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_759_, 0, v_asTopVar_702_);
lean_closure_set(v___f_759_, 1, v_e_692_);
lean_closure_set(v___f_759_, 2, v_inst_694_);
lean_closure_set(v___f_759_, 3, v_inst_695_);
lean_closure_set(v___f_759_, 4, v_inst_696_);
lean_closure_set(v___f_759_, 5, v_inst_697_);
lean_closure_set(v___f_759_, 6, v_inst_698_);
lean_closure_set(v___f_759_, 7, v_toVar_699_);
lean_closure_set(v___f_759_, 8, v_asVar_700_);
lean_closure_set(v___f_759_, 9, v_arg_712_);
lean_closure_set(v___f_759_, 10, v_toBind_701_);
lean_closure_set(v___f_759_, 11, v___f_758_);
v___x_760_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v_arg_716_);
v___x_761_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v___x_760_, v___f_759_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; 
lean_dec(v___x_756_);
lean_dec_ref(v_arg_716_);
lean_dec_ref(v_arg_712_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toPure_693_);
v___x_762_ = lean_apply_1(v_asTopVar_702_, v_e_692_);
return v___x_762_;
}
}
}
}
}
}
else
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_arg_716_);
lean_dec(v_toPure_693_);
lean_dec(v_toTopVar_691_);
lean_inc(v_toBind_701_);
lean_inc_ref(v_inst_698_);
lean_inc_ref(v_inst_697_);
lean_inc_ref(v_inst_696_);
lean_inc_ref(v_inst_695_);
lean_inc(v_inst_694_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_763_, 0, v_asTopVar_702_);
lean_closure_set(v___f_763_, 1, v_e_692_);
lean_closure_set(v___f_763_, 2, v_inst_694_);
lean_closure_set(v___f_763_, 3, v_inst_695_);
lean_closure_set(v___f_763_, 4, v_inst_696_);
lean_closure_set(v___f_763_, 5, v_inst_697_);
lean_closure_set(v___f_763_, 6, v_inst_698_);
lean_closure_set(v___f_763_, 7, v_toVar_699_);
lean_closure_set(v___f_763_, 8, v_asVar_700_);
lean_closure_set(v___f_763_, 9, v_arg_708_);
lean_closure_set(v___f_763_, 10, v_toBind_701_);
lean_closure_set(v___f_763_, 11, v___f_703_);
v___x_764_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v_arg_712_);
v___x_765_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v___x_764_, v___f_763_);
return v___x_765_;
}
}
else
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_arg_716_);
lean_dec(v___f_703_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_695_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed), 6, 5);
lean_closure_set(v___f_766_, 0, v_asTopVar_702_);
lean_closure_set(v___f_766_, 1, v_e_692_);
lean_closure_set(v___f_766_, 2, v_arg_708_);
lean_closure_set(v___f_766_, 3, v_toPure_693_);
lean_closure_set(v___f_766_, 4, v_toTopVar_691_);
v___x_767_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_694_, v_inst_696_, v_inst_697_, v_inst_698_, v_arg_712_);
v___x_768_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v___x_767_, v___f_766_);
return v___x_768_;
}
}
else
{
lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_arg_716_);
lean_dec(v___f_703_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_695_);
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed), 6, 5);
lean_closure_set(v___f_769_, 0, v_asTopVar_702_);
lean_closure_set(v___f_769_, 1, v_e_692_);
lean_closure_set(v___f_769_, 2, v_arg_708_);
lean_closure_set(v___f_769_, 3, v_toPure_693_);
lean_closure_set(v___f_769_, 4, v_toTopVar_691_);
v___x_770_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_694_, v_inst_696_, v_inst_697_, v_inst_698_, v_arg_712_);
v___x_771_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v___x_770_, v___f_769_);
return v___x_771_;
}
}
else
{
lean_dec_ref(v___x_717_);
lean_dec_ref(v_arg_716_);
lean_dec_ref(v_arg_708_);
lean_dec(v___f_703_);
lean_dec(v_toBind_701_);
lean_dec(v_asVar_700_);
lean_dec(v_toVar_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec(v_toTopVar_691_);
if (lean_obj_tag(v_arg_712_) == 9)
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v_arg_712_, 0);
lean_inc_ref(v_a_772_);
lean_dec_ref_known(v_arg_712_, 1);
if (lean_obj_tag(v_a_772_) == 0)
{
lean_object* v_val_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_asTopVar_702_);
lean_dec_ref(v_e_692_);
v_val_773_ = lean_ctor_get(v_a_772_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_783_ == 0)
{
v___x_775_ = v_a_772_;
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_val_773_);
lean_dec(v_a_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_nat_to_int(v_val_773_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_782_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___x_781_ = lean_apply_2(v_toPure_693_, lean_box(0), v___x_780_);
return v___x_781_;
}
}
}
else
{
lean_object* v___x_784_; 
lean_dec_ref(v_a_772_);
lean_dec(v_toPure_693_);
v___x_784_ = lean_apply_1(v_asTopVar_702_, v_e_692_);
return v___x_784_;
}
}
else
{
lean_object* v___x_785_; 
lean_dec_ref(v_arg_712_);
lean_dec(v_toPure_693_);
v___x_785_ = lean_apply_1(v_asTopVar_702_, v_e_692_);
return v___x_785_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_e_793_, uint8_t v_skipVar_794_){
_start:
{
lean_object* v_toApplicative_795_; lean_object* v_toBind_796_; lean_object* v_toPure_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v_asVar_801_; lean_object* v_toVar_802_; lean_object* v___x_803_; lean_object* v_toTopVar_804_; lean_object* v_asTopVar_805_; lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_toApplicative_795_ = lean_ctor_get(v_inst_789_, 0);
v_toBind_796_ = lean_ctor_get(v_inst_789_, 1);
lean_inc_n(v_toBind_796_, 6);
v_toPure_797_ = lean_ctor_get(v_toApplicative_795_, 1);
lean_inc_n(v_toPure_797_, 5);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_798_, 0, v_toPure_797_);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_799_, 0, v_toPure_797_);
v___f_800_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_800_, 0, v_toPure_797_);
lean_inc(v_inst_786_);
lean_inc_ref(v___f_800_);
lean_inc(v_inst_792_);
v_asVar_801_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4), 5, 4);
lean_closure_set(v_asVar_801_, 0, v_inst_792_);
lean_closure_set(v_asVar_801_, 1, v_toBind_796_);
lean_closure_set(v_asVar_801_, 2, v___f_800_);
lean_closure_set(v_asVar_801_, 3, v_inst_786_);
v_toVar_802_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6), 4, 3);
lean_closure_set(v_toVar_802_, 0, v_inst_792_);
lean_closure_set(v_toVar_802_, 1, v_toBind_796_);
lean_closure_set(v_toVar_802_, 2, v___f_800_);
v___x_803_ = lean_box(v_skipVar_794_);
lean_inc_ref(v_toVar_802_);
v_toTopVar_804_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v_toTopVar_804_, 0, v___x_803_);
lean_closure_set(v_toTopVar_804_, 1, v_toVar_802_);
lean_closure_set(v_toTopVar_804_, 2, v_toBind_796_);
lean_closure_set(v_toTopVar_804_, 3, v___f_799_);
lean_closure_set(v_toTopVar_804_, 4, v_toPure_797_);
lean_inc_ref(v_toTopVar_804_);
v_asTopVar_805_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8), 4, 3);
lean_closure_set(v_asTopVar_805_, 0, v_toTopVar_804_);
lean_closure_set(v_asTopVar_805_, 1, v_inst_786_);
lean_closure_set(v_asTopVar_805_, 2, v_toBind_796_);
lean_inc(v_inst_787_);
lean_inc_ref(v_e_793_);
v___f_806_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18), 14, 13);
lean_closure_set(v___f_806_, 0, v_toTopVar_804_);
lean_closure_set(v___f_806_, 1, v_e_793_);
lean_closure_set(v___f_806_, 2, v_toPure_797_);
lean_closure_set(v___f_806_, 3, v_inst_787_);
lean_closure_set(v___f_806_, 4, v_inst_788_);
lean_closure_set(v___f_806_, 5, v_inst_789_);
lean_closure_set(v___f_806_, 6, v_inst_790_);
lean_closure_set(v___f_806_, 7, v_inst_791_);
lean_closure_set(v___f_806_, 8, v_toVar_802_);
lean_closure_set(v___f_806_, 9, v_asVar_801_);
lean_closure_set(v___f_806_, 10, v_toBind_796_);
lean_closure_set(v___f_806_, 11, v_asTopVar_805_);
lean_closure_set(v___f_806_, 12, v___f_798_);
v___x_807_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_807_, 0, v_e_793_);
v___x_808_ = lean_apply_2(v_inst_787_, lean_box(0), v___x_807_);
v___x_809_ = lean_apply_4(v_toBind_796_, lean_box(0), lean_box(0), v___x_808_, v___f_806_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___boxed(lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_e_817_, lean_object* v_skipVar_818_){
_start:
{
uint8_t v_skipVar_boxed_819_; lean_object* v_res_820_; 
v_skipVar_boxed_819_ = lean_unbox(v_skipVar_818_);
v_res_820_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_810_, v_inst_811_, v_inst_812_, v_inst_813_, v_inst_814_, v_inst_815_, v_inst_816_, v_e_817_, v_skipVar_boxed_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f(lean_object* v_m_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_e_829_, uint8_t v_skipVar_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_822_, v_inst_823_, v_inst_824_, v_inst_825_, v_inst_826_, v_inst_827_, v_inst_828_, v_e_829_, v_skipVar_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___boxed(lean_object* v_m_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_e_840_, lean_object* v_skipVar_841_){
_start:
{
uint8_t v_skipVar_boxed_842_; lean_object* v_res_843_; 
v_skipVar_boxed_842_ = lean_unbox(v_skipVar_841_);
v_res_843_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f(v_m_832_, v_inst_833_, v_inst_834_, v_inst_835_, v_inst_836_, v_inst_837_, v_inst_838_, v_inst_839_, v_e_840_, v_skipVar_boxed_842_);
return v_res_843_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(lean_object* v_inst_847_, lean_object* v_e_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_849_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1, &l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1);
v___x_850_ = l_Lean_indentExpr(v_e_848_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_reportIssueIfVerbose___boxed), 8, 1);
lean_closure_set(v___x_852_, 0, v___x_851_);
v___x_853_ = lean_apply_2(v_inst_847_, lean_box(0), v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue(lean_object* v_m_854_, lean_object* v_inst_855_, lean_object* v_e_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_855_, v_e_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(lean_object* v_arg_858_, lean_object* v_asVar_859_, lean_object* v_e_860_, lean_object* v_arg_861_, lean_object* v_toPure_862_, lean_object* v_toVar_863_, lean_object* v_____do__lift_864_){
_start:
{
lean_object* v___x_865_; size_t v___x_866_; size_t v___x_867_; uint8_t v___x_868_; 
v___x_865_ = l_Lean_Expr_appArg_x21(v_____do__lift_864_);
v___x_866_ = lean_ptr_addr(v___x_865_);
lean_dec_ref(v___x_865_);
v___x_867_ = lean_ptr_addr(v_arg_858_);
v___x_868_ = lean_usize_dec_eq(v___x_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_toVar_863_);
lean_dec(v_toPure_862_);
lean_dec_ref(v_arg_861_);
v___x_869_ = lean_apply_1(v_asVar_859_, v_e_860_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; 
lean_dec(v_asVar_859_);
v___x_870_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_861_);
if (lean_obj_tag(v___x_870_) == 1)
{
lean_object* v_val_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_toVar_863_);
lean_dec_ref(v_e_860_);
v_val_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_880_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_val_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = lean_nat_to_int(v_val_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 0);
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_879_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; 
v___x_878_ = lean_apply_2(v_toPure_862_, lean_box(0), v___x_877_);
return v___x_878_;
}
}
}
else
{
lean_object* v___x_881_; 
lean_dec(v___x_870_);
lean_dec(v_toPure_862_);
v___x_881_ = lean_apply_1(v_toVar_863_, v_e_860_);
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed(lean_object* v_arg_882_, lean_object* v_asVar_883_, lean_object* v_e_884_, lean_object* v_arg_885_, lean_object* v_toPure_886_, lean_object* v_toVar_887_, lean_object* v_____do__lift_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(v_arg_882_, v_asVar_883_, v_e_884_, v_arg_885_, v_toPure_886_, v_toVar_887_, v_____do__lift_888_);
lean_dec_ref(v_____do__lift_888_);
lean_dec_ref(v_arg_882_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(lean_object* v_arg_890_, lean_object* v_asVar_891_, lean_object* v_e_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_toVar_898_, lean_object* v_arg_899_, lean_object* v_toBind_900_, lean_object* v___f_901_, lean_object* v_____do__lift_902_){
_start:
{
lean_object* v___x_903_; size_t v___x_904_; size_t v___x_905_; uint8_t v___x_906_; 
v___x_903_ = l_Lean_Expr_appArg_x21(v_____do__lift_902_);
v___x_904_ = lean_ptr_addr(v___x_903_);
lean_dec_ref(v___x_903_);
v___x_905_ = lean_ptr_addr(v_arg_890_);
v___x_906_ = lean_usize_dec_eq(v___x_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v___f_901_);
lean_dec(v_toBind_900_);
lean_dec_ref(v_arg_899_);
lean_dec(v_toVar_898_);
lean_dec_ref(v_inst_897_);
lean_dec_ref(v_inst_896_);
lean_dec_ref(v_inst_895_);
lean_dec_ref(v_inst_894_);
lean_dec(v_inst_893_);
v___x_907_ = lean_apply_1(v_asVar_891_, v_e_892_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec_ref(v_e_892_);
v___x_908_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_893_, v_inst_894_, v_inst_895_, v_inst_896_, v_inst_897_, v_toVar_898_, v_asVar_891_, v_arg_899_);
v___x_909_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_908_, v___f_901_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed(lean_object* v_arg_910_, lean_object* v_asVar_911_, lean_object* v_e_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_toVar_918_, lean_object* v_arg_919_, lean_object* v_toBind_920_, lean_object* v___f_921_, lean_object* v_____do__lift_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(v_arg_910_, v_asVar_911_, v_e_912_, v_inst_913_, v_inst_914_, v_inst_915_, v_inst_916_, v_inst_917_, v_toVar_918_, v_arg_919_, v_toBind_920_, v___f_921_, v_____do__lift_922_);
lean_dec_ref(v_____do__lift_922_);
lean_dec_ref(v_arg_910_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3(lean_object* v_toPure_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_toVar_930_, lean_object* v_asVar_931_, lean_object* v_arg_932_, lean_object* v_toBind_933_, lean_object* v_____do__lift_934_){
_start:
{
lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___f_935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_935_, 0, v_____do__lift_934_);
lean_closure_set(v___f_935_, 1, v_toPure_924_);
v___x_936_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_925_, v_inst_926_, v_inst_927_, v_inst_928_, v_inst_929_, v_toVar_930_, v_asVar_931_, v_arg_932_);
v___x_937_ = lean_apply_4(v_toBind_933_, lean_box(0), lean_box(0), v___x_936_, v___f_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2(lean_object* v_toVar_938_, lean_object* v_e_939_, lean_object* v_toPure_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_asVar_946_, lean_object* v_toBind_947_, lean_object* v_____x_948_){
_start:
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = l_Lean_Expr_cleanupAnnotations(v_____x_948_);
v___x_950_ = l_Lean_Expr_isApp(v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v___x_949_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
lean_dec(v_toPure_940_);
v___x_951_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_951_;
}
else
{
lean_object* v_arg_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v_arg_952_ = lean_ctor_get(v___x_949_, 1);
lean_inc_ref(v_arg_952_);
v___x_953_ = l_Lean_Expr_appFnCleanup___redArg(v___x_949_);
v___x_954_ = l_Lean_Expr_isApp(v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v___x_953_);
lean_dec_ref(v_arg_952_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
lean_dec(v_toPure_940_);
v___x_955_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_955_;
}
else
{
lean_object* v_arg_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_arg_956_ = lean_ctor_get(v___x_953_, 1);
lean_inc_ref(v_arg_956_);
v___x_957_ = l_Lean_Expr_appFnCleanup___redArg(v___x_953_);
v___x_958_ = l_Lean_Expr_isApp(v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v___x_957_);
lean_dec_ref(v_arg_956_);
lean_dec_ref(v_arg_952_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
lean_dec(v_toPure_940_);
v___x_959_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_959_;
}
else
{
lean_object* v_arg_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_arg_960_ = lean_ctor_get(v___x_957_, 1);
lean_inc_ref(v_arg_960_);
v___x_961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_957_);
v___x_962_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_963_ = l_Lean_Expr_isConstOf(v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_965_ = l_Lean_Expr_isConstOf(v___x_961_, v___x_964_);
if (v___x_965_ == 0)
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_Expr_isApp(v___x_961_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec_ref(v___x_961_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_956_);
lean_dec_ref(v_arg_952_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
lean_dec(v_toPure_940_);
v___x_967_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_961_);
v___x_969_ = l_Lean_Expr_isApp(v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
lean_dec_ref(v___x_968_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_956_);
lean_dec_ref(v_arg_952_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
lean_dec(v_toPure_940_);
v___x_970_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_968_);
v___x_972_ = l_Lean_Expr_isApp(v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
lean_dec_ref(v___x_971_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_956_);
lean_dec_ref(v_arg_952_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
lean_dec(v_toPure_940_);
v___x_973_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_971_);
v___x_975_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_976_ = l_Lean_Expr_isConstOf(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_978_ = l_Lean_Expr_isConstOf(v___x_974_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_980_ = l_Lean_Expr_isConstOf(v___x_974_, v___x_979_);
lean_dec_ref(v___x_974_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_956_);
lean_dec_ref(v_arg_952_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
lean_dec(v_toPure_940_);
v___x_981_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_981_;
}
else
{
lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_inc_n(v_toBind_947_, 2);
lean_inc(v_asVar_946_);
lean_inc(v_toVar_938_);
lean_inc_ref_n(v_inst_945_, 2);
lean_inc_ref_n(v_inst_944_, 2);
lean_inc_ref_n(v_inst_943_, 2);
lean_inc_ref_n(v_inst_942_, 2);
lean_inc_n(v_inst_941_, 2);
v___f_982_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_982_, 0, v_toPure_940_);
lean_closure_set(v___f_982_, 1, v_inst_941_);
lean_closure_set(v___f_982_, 2, v_inst_942_);
lean_closure_set(v___f_982_, 3, v_inst_943_);
lean_closure_set(v___f_982_, 4, v_inst_944_);
lean_closure_set(v___f_982_, 5, v_inst_945_);
lean_closure_set(v___f_982_, 6, v_toVar_938_);
lean_closure_set(v___f_982_, 7, v_asVar_946_);
lean_closure_set(v___f_982_, 8, v_arg_952_);
lean_closure_set(v___f_982_, 9, v_toBind_947_);
v___f_983_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_983_, 0, v_arg_960_);
lean_closure_set(v___f_983_, 1, v_asVar_946_);
lean_closure_set(v___f_983_, 2, v_e_939_);
lean_closure_set(v___f_983_, 3, v_inst_941_);
lean_closure_set(v___f_983_, 4, v_inst_942_);
lean_closure_set(v___f_983_, 5, v_inst_943_);
lean_closure_set(v___f_983_, 6, v_inst_944_);
lean_closure_set(v___f_983_, 7, v_inst_945_);
lean_closure_set(v___f_983_, 8, v_toVar_938_);
lean_closure_set(v___f_983_, 9, v_arg_956_);
lean_closure_set(v___f_983_, 10, v_toBind_947_);
lean_closure_set(v___f_983_, 11, v___f_982_);
v___x_984_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_941_, v_inst_942_, v_inst_943_, v_inst_944_, v_inst_945_);
v___x_985_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_984_, v___f_983_);
return v___x_985_;
}
}
else
{
lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref(v___x_974_);
lean_inc_n(v_toBind_947_, 2);
lean_inc(v_asVar_946_);
lean_inc(v_toVar_938_);
lean_inc_ref_n(v_inst_945_, 2);
lean_inc_ref_n(v_inst_944_, 2);
lean_inc_ref_n(v_inst_943_, 2);
lean_inc_ref_n(v_inst_942_, 2);
lean_inc_n(v_inst_941_, 2);
v___f_986_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3), 11, 10);
lean_closure_set(v___f_986_, 0, v_toPure_940_);
lean_closure_set(v___f_986_, 1, v_inst_941_);
lean_closure_set(v___f_986_, 2, v_inst_942_);
lean_closure_set(v___f_986_, 3, v_inst_943_);
lean_closure_set(v___f_986_, 4, v_inst_944_);
lean_closure_set(v___f_986_, 5, v_inst_945_);
lean_closure_set(v___f_986_, 6, v_toVar_938_);
lean_closure_set(v___f_986_, 7, v_asVar_946_);
lean_closure_set(v___f_986_, 8, v_arg_952_);
lean_closure_set(v___f_986_, 9, v_toBind_947_);
v___f_987_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_987_, 0, v_arg_960_);
lean_closure_set(v___f_987_, 1, v_asVar_946_);
lean_closure_set(v___f_987_, 2, v_e_939_);
lean_closure_set(v___f_987_, 3, v_inst_941_);
lean_closure_set(v___f_987_, 4, v_inst_942_);
lean_closure_set(v___f_987_, 5, v_inst_943_);
lean_closure_set(v___f_987_, 6, v_inst_944_);
lean_closure_set(v___f_987_, 7, v_inst_945_);
lean_closure_set(v___f_987_, 8, v_toVar_938_);
lean_closure_set(v___f_987_, 9, v_arg_956_);
lean_closure_set(v___f_987_, 10, v_toBind_947_);
lean_closure_set(v___f_987_, 11, v___f_986_);
v___x_988_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_941_, v_inst_942_, v_inst_943_, v_inst_944_, v_inst_945_);
v___x_989_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_988_, v___f_987_);
return v___x_989_;
}
}
else
{
lean_object* v___x_990_; 
lean_dec_ref(v___x_974_);
v___x_990_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_952_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_val_991_; lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_990_, 1);
v___f_992_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9), 3, 2);
lean_closure_set(v___f_992_, 0, v_val_991_);
lean_closure_set(v___f_992_, 1, v_toPure_940_);
lean_inc(v_toBind_947_);
lean_inc_ref(v_inst_945_);
lean_inc_ref(v_inst_944_);
lean_inc_ref(v_inst_943_);
lean_inc_ref(v_inst_942_);
lean_inc(v_inst_941_);
v___f_993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_993_, 0, v_arg_960_);
lean_closure_set(v___f_993_, 1, v_asVar_946_);
lean_closure_set(v___f_993_, 2, v_e_939_);
lean_closure_set(v___f_993_, 3, v_inst_941_);
lean_closure_set(v___f_993_, 4, v_inst_942_);
lean_closure_set(v___f_993_, 5, v_inst_943_);
lean_closure_set(v___f_993_, 6, v_inst_944_);
lean_closure_set(v___f_993_, 7, v_inst_945_);
lean_closure_set(v___f_993_, 8, v_toVar_938_);
lean_closure_set(v___f_993_, 9, v_arg_956_);
lean_closure_set(v___f_993_, 10, v_toBind_947_);
lean_closure_set(v___f_993_, 11, v___f_992_);
v___x_994_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_941_, v_inst_942_, v_inst_943_, v_inst_944_, v_inst_945_);
v___x_995_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_994_, v___f_993_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; 
lean_dec(v___x_990_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_956_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
lean_dec(v_toPure_940_);
v___x_996_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_996_;
}
}
}
}
}
}
else
{
lean_object* v___f_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref(v___x_961_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_inst_942_);
v___f_997_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_997_, 0, v_arg_956_);
lean_closure_set(v___f_997_, 1, v_asVar_946_);
lean_closure_set(v___f_997_, 2, v_e_939_);
lean_closure_set(v___f_997_, 3, v_arg_952_);
lean_closure_set(v___f_997_, 4, v_toPure_940_);
lean_closure_set(v___f_997_, 5, v_toVar_938_);
v___x_998_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_941_, v_inst_943_, v_inst_944_, v_inst_945_);
v___x_999_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_998_, v___f_997_);
return v___x_999_;
}
}
else
{
lean_dec_ref(v___x_961_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_952_);
lean_dec(v_toBind_947_);
lean_dec(v_asVar_946_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
lean_dec(v_inst_941_);
if (lean_obj_tag(v_arg_956_) == 9)
{
lean_object* v_a_1000_; 
v_a_1000_ = lean_ctor_get(v_arg_956_, 0);
lean_inc_ref(v_a_1000_);
lean_dec_ref_known(v_arg_956_, 1);
if (lean_obj_tag(v_a_1000_) == 0)
{
lean_object* v_val_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_e_939_);
lean_dec(v_toVar_938_);
v_val_1001_ = lean_ctor_get(v_a_1000_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_a_1000_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1003_ = v_a_1000_;
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_val_1001_);
lean_dec(v_a_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_nat_to_int(v_val_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_apply_2(v_toPure_940_, lean_box(0), v___x_1007_);
return v___x_1008_;
}
}
}
else
{
lean_object* v___x_1011_; 
lean_dec_ref(v_a_1000_);
lean_dec(v_toPure_940_);
v___x_1011_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_1011_;
}
}
else
{
lean_object* v___x_1012_; 
lean_dec_ref(v_arg_956_);
lean_dec(v_toPure_940_);
v___x_1012_ = lean_apply_1(v_toVar_938_, v_e_939_);
return v___x_1012_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(lean_object* v_inst_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_toVar_1018_, lean_object* v_asVar_1019_, lean_object* v_e_1020_){
_start:
{
lean_object* v_toApplicative_1021_; lean_object* v_toBind_1022_; lean_object* v_toPure_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; 
v_toApplicative_1021_ = lean_ctor_get(v_inst_1015_, 0);
v_toBind_1022_ = lean_ctor_get(v_inst_1015_, 1);
lean_inc_n(v_toBind_1022_, 2);
v_toPure_1023_ = lean_ctor_get(v_toApplicative_1021_, 1);
lean_inc(v_toPure_1023_);
lean_inc_ref(v_e_1020_);
v___x_1024_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_1024_, 0, v_e_1020_);
lean_inc(v_inst_1013_);
v___x_1025_ = lean_apply_2(v_inst_1013_, lean_box(0), v___x_1024_);
v___f_1026_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1026_, 0, v_toVar_1018_);
lean_closure_set(v___f_1026_, 1, v_e_1020_);
lean_closure_set(v___f_1026_, 2, v_toPure_1023_);
lean_closure_set(v___f_1026_, 3, v_inst_1013_);
lean_closure_set(v___f_1026_, 4, v_inst_1014_);
lean_closure_set(v___f_1026_, 5, v_inst_1015_);
lean_closure_set(v___f_1026_, 6, v_inst_1016_);
lean_closure_set(v___f_1026_, 7, v_inst_1017_);
lean_closure_set(v___f_1026_, 8, v_asVar_1019_);
lean_closure_set(v___f_1026_, 9, v_toBind_1022_);
v___x_1027_ = lean_apply_4(v_toBind_1022_, lean_box(0), lean_box(0), v___x_1025_, v___f_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1(lean_object* v_toPure_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_toVar_1034_, lean_object* v_asVar_1035_, lean_object* v_arg_1036_, lean_object* v_toBind_1037_, lean_object* v_____do__lift_1038_){
_start:
{
lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___f_1039_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1039_, 0, v_____do__lift_1038_);
lean_closure_set(v___f_1039_, 1, v_toPure_1028_);
v___x_1040_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1029_, v_inst_1030_, v_inst_1031_, v_inst_1032_, v_inst_1033_, v_toVar_1034_, v_asVar_1035_, v_arg_1036_);
v___x_1041_ = lean_apply_4(v_toBind_1037_, lean_box(0), lean_box(0), v___x_1040_, v___f_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go(lean_object* v_m_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_toVar_1048_, lean_object* v_asVar_1049_, lean_object* v_e_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1043_, v_inst_1044_, v_inst_1045_, v_inst_1046_, v_inst_1047_, v_toVar_1048_, v_asVar_1049_, v_e_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3(lean_object* v_inst_1052_, lean_object* v_toBind_1053_, lean_object* v___f_1054_, lean_object* v_inst_1055_, lean_object* v_e_1056_){
_start:
{
lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_inc(v_toBind_1053_);
lean_inc_ref(v_e_1056_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1057_, 0, v_inst_1052_);
lean_closure_set(v___f_1057_, 1, v_e_1056_);
lean_closure_set(v___f_1057_, 2, v_toBind_1053_);
lean_closure_set(v___f_1057_, 3, v___f_1054_);
v___x_1058_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_1055_, v_e_1056_);
v___x_1059_ = lean_apply_4(v_toBind_1053_, lean_box(0), lean_box(0), v___x_1058_, v___f_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2(lean_object* v_toVar_1060_, lean_object* v_toBind_1061_, lean_object* v___f_1062_, lean_object* v_e_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_apply_1(v_toVar_1060_, v_e_1063_);
v___x_1065_ = lean_apply_4(v_toBind_1061_, lean_box(0), lean_box(0), v___x_1064_, v___f_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1(lean_object* v_toTopVar_1066_, lean_object* v_inst_1067_, lean_object* v_toBind_1068_, lean_object* v_e_1069_){
_start:
{
lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_inc_ref(v_e_1069_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1070_, 0, v_toTopVar_1066_);
lean_closure_set(v___f_1070_, 1, v_e_1069_);
v___x_1071_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_1067_, v_e_1069_);
v___x_1072_ = lean_apply_4(v_toBind_1068_, lean_box(0), lean_box(0), v___x_1071_, v___f_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4(lean_object* v_toPure_1073_, lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_toVar_1079_, lean_object* v_asVar_1080_, lean_object* v_arg_1081_, lean_object* v_toBind_1082_, lean_object* v_____do__lift_1083_){
_start:
{
lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9), 3, 2);
lean_closure_set(v___f_1084_, 0, v_____do__lift_1083_);
lean_closure_set(v___f_1084_, 1, v_toPure_1073_);
v___x_1085_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1074_, v_inst_1075_, v_inst_1076_, v_inst_1077_, v_inst_1078_, v_toVar_1079_, v_asVar_1080_, v_arg_1081_);
v___x_1086_ = lean_apply_4(v_toBind_1082_, lean_box(0), lean_box(0), v___x_1085_, v___f_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(lean_object* v_arg_1087_, lean_object* v_asTopVar_1088_, lean_object* v_e_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_toVar_1095_, lean_object* v_asVar_1096_, lean_object* v_arg_1097_, lean_object* v_toBind_1098_, lean_object* v___f_1099_, lean_object* v_____do__lift_1100_){
_start:
{
lean_object* v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; uint8_t v___x_1104_; 
v___x_1101_ = l_Lean_Expr_appArg_x21(v_____do__lift_1100_);
v___x_1102_ = lean_ptr_addr(v___x_1101_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = lean_ptr_addr(v_arg_1087_);
v___x_1104_ = lean_usize_dec_eq(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
lean_dec(v___f_1099_);
lean_dec(v_toBind_1098_);
lean_dec_ref(v_arg_1097_);
lean_dec(v_asVar_1096_);
lean_dec(v_toVar_1095_);
lean_dec_ref(v_inst_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_inst_1092_);
lean_dec_ref(v_inst_1091_);
lean_dec(v_inst_1090_);
v___x_1105_ = lean_apply_1(v_asTopVar_1088_, v_e_1089_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref(v_e_1089_);
lean_dec(v_asTopVar_1088_);
v___x_1106_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1090_, v_inst_1091_, v_inst_1092_, v_inst_1093_, v_inst_1094_, v_toVar_1095_, v_asVar_1096_, v_arg_1097_);
v___x_1107_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v___x_1106_, v___f_1099_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed(lean_object* v_arg_1108_, lean_object* v_asTopVar_1109_, lean_object* v_e_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_toVar_1116_, lean_object* v_asVar_1117_, lean_object* v_arg_1118_, lean_object* v_toBind_1119_, lean_object* v___f_1120_, lean_object* v_____do__lift_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(v_arg_1108_, v_asTopVar_1109_, v_e_1110_, v_inst_1111_, v_inst_1112_, v_inst_1113_, v_inst_1114_, v_inst_1115_, v_toVar_1116_, v_asVar_1117_, v_arg_1118_, v_toBind_1119_, v___f_1120_, v_____do__lift_1121_);
lean_dec_ref(v_____do__lift_1121_);
lean_dec_ref(v_arg_1108_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6(lean_object* v_toPure_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_toVar_1129_, lean_object* v_asVar_1130_, lean_object* v_arg_1131_, lean_object* v_toBind_1132_, lean_object* v_____do__lift_1133_){
_start:
{
lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12), 3, 2);
lean_closure_set(v___f_1134_, 0, v_____do__lift_1133_);
lean_closure_set(v___f_1134_, 1, v_toPure_1123_);
v___x_1135_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1124_, v_inst_1125_, v_inst_1126_, v_inst_1127_, v_inst_1128_, v_toVar_1129_, v_asVar_1130_, v_arg_1131_);
v___x_1136_ = lean_apply_4(v_toBind_1132_, lean_box(0), lean_box(0), v___x_1135_, v___f_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(lean_object* v_arg_1137_, lean_object* v_asTopVar_1138_, lean_object* v_e_1139_, lean_object* v_arg_1140_, lean_object* v_toPure_1141_, lean_object* v_toTopVar_1142_, lean_object* v_____do__lift_1143_){
_start:
{
lean_object* v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1144_ = l_Lean_Expr_appArg_x21(v_____do__lift_1143_);
v___x_1145_ = lean_ptr_addr(v___x_1144_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = lean_ptr_addr(v_arg_1137_);
v___x_1147_ = lean_usize_dec_eq(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec(v_toTopVar_1142_);
lean_dec(v_toPure_1141_);
lean_dec_ref(v_arg_1140_);
v___x_1148_ = lean_apply_1(v_asTopVar_1138_, v_e_1139_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; 
lean_dec(v_asTopVar_1138_);
v___x_1149_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1140_);
if (lean_obj_tag(v___x_1149_) == 1)
{
lean_object* v_val_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_toTopVar_1142_);
lean_dec_ref(v_e_1139_);
v_val_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_val_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = lean_nat_to_int(v_val_1150_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_apply_2(v_toPure_1141_, lean_box(0), v___x_1157_);
return v___x_1158_;
}
}
}
else
{
lean_object* v___x_1161_; 
lean_dec(v___x_1149_);
lean_dec(v_toPure_1141_);
v___x_1161_ = lean_apply_1(v_toTopVar_1142_, v_e_1139_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed(lean_object* v_arg_1162_, lean_object* v_asTopVar_1163_, lean_object* v_e_1164_, lean_object* v_arg_1165_, lean_object* v_toPure_1166_, lean_object* v_toTopVar_1167_, lean_object* v_____do__lift_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(v_arg_1162_, v_asTopVar_1163_, v_e_1164_, v_arg_1165_, v_toPure_1166_, v_toTopVar_1167_, v_____do__lift_1168_);
lean_dec_ref(v_____do__lift_1168_);
lean_dec_ref(v_arg_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5(lean_object* v_toTopVar_1170_, lean_object* v_e_1171_, lean_object* v_toPure_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_toVar_1178_, lean_object* v_asVar_1179_, lean_object* v_toBind_1180_, lean_object* v_asTopVar_1181_, lean_object* v_____x_1182_){
_start:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = l_Lean_Expr_cleanupAnnotations(v_____x_1182_);
v___x_1184_ = l_Lean_Expr_isApp(v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
lean_dec_ref(v___x_1183_);
lean_dec(v_asTopVar_1181_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec(v_toPure_1172_);
v___x_1185_ = lean_apply_1(v_toTopVar_1170_, v_e_1171_);
return v___x_1185_;
}
else
{
lean_object* v_arg_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_arg_1186_ = lean_ctor_get(v___x_1183_, 1);
lean_inc_ref(v_arg_1186_);
v___x_1187_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1183_);
v___x_1188_ = l_Lean_Expr_isApp(v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_arg_1186_);
lean_dec(v_asTopVar_1181_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec(v_toPure_1172_);
v___x_1189_ = lean_apply_1(v_toTopVar_1170_, v_e_1171_);
return v___x_1189_;
}
else
{
lean_object* v_arg_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_arg_1190_ = lean_ctor_get(v___x_1187_, 1);
lean_inc_ref(v_arg_1190_);
v___x_1191_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1187_);
v___x_1192_ = l_Lean_Expr_isApp(v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
lean_dec_ref(v___x_1191_);
lean_dec_ref(v_arg_1190_);
lean_dec_ref(v_arg_1186_);
lean_dec(v_asTopVar_1181_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec(v_toPure_1172_);
v___x_1193_ = lean_apply_1(v_toTopVar_1170_, v_e_1171_);
return v___x_1193_;
}
else
{
lean_object* v_arg_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_arg_1194_ = lean_ctor_get(v___x_1191_, 1);
lean_inc_ref(v_arg_1194_);
v___x_1195_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1191_);
v___x_1196_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_1197_ = l_Lean_Expr_isConstOf(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_1199_ = l_Lean_Expr_isConstOf(v___x_1195_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_Expr_isApp(v___x_1195_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec_ref(v___x_1195_);
lean_dec_ref(v_arg_1194_);
lean_dec_ref(v_arg_1190_);
lean_dec_ref(v_arg_1186_);
lean_dec(v_asTopVar_1181_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec(v_toPure_1172_);
v___x_1201_ = lean_apply_1(v_toTopVar_1170_, v_e_1171_);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1195_);
v___x_1203_ = l_Lean_Expr_isApp(v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
lean_dec_ref(v___x_1202_);
lean_dec_ref(v_arg_1194_);
lean_dec_ref(v_arg_1190_);
lean_dec_ref(v_arg_1186_);
lean_dec(v_asTopVar_1181_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec(v_toPure_1172_);
v___x_1204_ = lean_apply_1(v_toTopVar_1170_, v_e_1171_);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1202_);
v___x_1206_ = l_Lean_Expr_isApp(v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_arg_1194_);
lean_dec_ref(v_arg_1190_);
lean_dec_ref(v_arg_1186_);
lean_dec(v_asTopVar_1181_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec(v_toPure_1172_);
v___x_1207_ = lean_apply_1(v_toTopVar_1170_, v_e_1171_);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1205_);
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_1210_ = l_Lean_Expr_isConstOf(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_1212_ = l_Lean_Expr_isConstOf(v___x_1208_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_1214_ = l_Lean_Expr_isConstOf(v___x_1208_, v___x_1213_);
lean_dec_ref(v___x_1208_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_dec_ref(v_arg_1194_);
lean_dec_ref(v_arg_1190_);
lean_dec_ref(v_arg_1186_);
lean_dec(v_asTopVar_1181_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec(v_toPure_1172_);
v___x_1215_ = lean_apply_1(v_toTopVar_1170_, v_e_1171_);
return v___x_1215_;
}
else
{
lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v_toTopVar_1170_);
lean_inc_n(v_toBind_1180_, 2);
lean_inc(v_asVar_1179_);
lean_inc(v_toVar_1178_);
lean_inc_ref_n(v_inst_1177_, 2);
lean_inc_ref_n(v_inst_1176_, 2);
lean_inc_ref_n(v_inst_1175_, 2);
lean_inc_ref_n(v_inst_1174_, 2);
lean_inc_n(v_inst_1173_, 2);
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4), 11, 10);
lean_closure_set(v___f_1216_, 0, v_toPure_1172_);
lean_closure_set(v___f_1216_, 1, v_inst_1173_);
lean_closure_set(v___f_1216_, 2, v_inst_1174_);
lean_closure_set(v___f_1216_, 3, v_inst_1175_);
lean_closure_set(v___f_1216_, 4, v_inst_1176_);
lean_closure_set(v___f_1216_, 5, v_inst_1177_);
lean_closure_set(v___f_1216_, 6, v_toVar_1178_);
lean_closure_set(v___f_1216_, 7, v_asVar_1179_);
lean_closure_set(v___f_1216_, 8, v_arg_1186_);
lean_closure_set(v___f_1216_, 9, v_toBind_1180_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1217_, 0, v_arg_1194_);
lean_closure_set(v___f_1217_, 1, v_asTopVar_1181_);
lean_closure_set(v___f_1217_, 2, v_e_1171_);
lean_closure_set(v___f_1217_, 3, v_inst_1173_);
lean_closure_set(v___f_1217_, 4, v_inst_1174_);
lean_closure_set(v___f_1217_, 5, v_inst_1175_);
lean_closure_set(v___f_1217_, 6, v_inst_1176_);
lean_closure_set(v___f_1217_, 7, v_inst_1177_);
lean_closure_set(v___f_1217_, 8, v_toVar_1178_);
lean_closure_set(v___f_1217_, 9, v_asVar_1179_);
lean_closure_set(v___f_1217_, 10, v_arg_1190_);
lean_closure_set(v___f_1217_, 11, v_toBind_1180_);
lean_closure_set(v___f_1217_, 12, v___f_1216_);
v___x_1218_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1173_, v_inst_1174_, v_inst_1175_, v_inst_1176_, v_inst_1177_);
v___x_1219_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v___x_1218_, v___f_1217_);
return v___x_1219_;
}
}
else
{
lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec_ref(v___x_1208_);
lean_dec(v_toTopVar_1170_);
lean_inc_n(v_toBind_1180_, 2);
lean_inc(v_asVar_1179_);
lean_inc(v_toVar_1178_);
lean_inc_ref_n(v_inst_1177_, 2);
lean_inc_ref_n(v_inst_1176_, 2);
lean_inc_ref_n(v_inst_1175_, 2);
lean_inc_ref_n(v_inst_1174_, 2);
lean_inc_n(v_inst_1173_, 2);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6), 11, 10);
lean_closure_set(v___f_1220_, 0, v_toPure_1172_);
lean_closure_set(v___f_1220_, 1, v_inst_1173_);
lean_closure_set(v___f_1220_, 2, v_inst_1174_);
lean_closure_set(v___f_1220_, 3, v_inst_1175_);
lean_closure_set(v___f_1220_, 4, v_inst_1176_);
lean_closure_set(v___f_1220_, 5, v_inst_1177_);
lean_closure_set(v___f_1220_, 6, v_toVar_1178_);
lean_closure_set(v___f_1220_, 7, v_asVar_1179_);
lean_closure_set(v___f_1220_, 8, v_arg_1186_);
lean_closure_set(v___f_1220_, 9, v_toBind_1180_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1221_, 0, v_arg_1194_);
lean_closure_set(v___f_1221_, 1, v_asTopVar_1181_);
lean_closure_set(v___f_1221_, 2, v_e_1171_);
lean_closure_set(v___f_1221_, 3, v_inst_1173_);
lean_closure_set(v___f_1221_, 4, v_inst_1174_);
lean_closure_set(v___f_1221_, 5, v_inst_1175_);
lean_closure_set(v___f_1221_, 6, v_inst_1176_);
lean_closure_set(v___f_1221_, 7, v_inst_1177_);
lean_closure_set(v___f_1221_, 8, v_toVar_1178_);
lean_closure_set(v___f_1221_, 9, v_asVar_1179_);
lean_closure_set(v___f_1221_, 10, v_arg_1190_);
lean_closure_set(v___f_1221_, 11, v_toBind_1180_);
lean_closure_set(v___f_1221_, 12, v___f_1220_);
v___x_1222_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1173_, v_inst_1174_, v_inst_1175_, v_inst_1176_, v_inst_1177_);
v___x_1223_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v___x_1222_, v___f_1221_);
return v___x_1223_;
}
}
else
{
lean_object* v___x_1224_; 
lean_dec_ref(v___x_1208_);
lean_dec(v_toTopVar_1170_);
v___x_1224_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1186_);
if (lean_obj_tag(v___x_1224_) == 1)
{
lean_object* v_val_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17), 3, 2);
lean_closure_set(v___f_1226_, 0, v_val_1225_);
lean_closure_set(v___f_1226_, 1, v_toPure_1172_);
lean_inc(v_toBind_1180_);
lean_inc_ref(v_inst_1177_);
lean_inc_ref(v_inst_1176_);
lean_inc_ref(v_inst_1175_);
lean_inc_ref(v_inst_1174_);
lean_inc(v_inst_1173_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1227_, 0, v_arg_1194_);
lean_closure_set(v___f_1227_, 1, v_asTopVar_1181_);
lean_closure_set(v___f_1227_, 2, v_e_1171_);
lean_closure_set(v___f_1227_, 3, v_inst_1173_);
lean_closure_set(v___f_1227_, 4, v_inst_1174_);
lean_closure_set(v___f_1227_, 5, v_inst_1175_);
lean_closure_set(v___f_1227_, 6, v_inst_1176_);
lean_closure_set(v___f_1227_, 7, v_inst_1177_);
lean_closure_set(v___f_1227_, 8, v_toVar_1178_);
lean_closure_set(v___f_1227_, 9, v_asVar_1179_);
lean_closure_set(v___f_1227_, 10, v_arg_1190_);
lean_closure_set(v___f_1227_, 11, v_toBind_1180_);
lean_closure_set(v___f_1227_, 12, v___f_1226_);
v___x_1228_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1173_, v_inst_1174_, v_inst_1175_, v_inst_1176_, v_inst_1177_);
v___x_1229_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v___x_1228_, v___f_1227_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v___x_1224_);
lean_dec_ref(v_arg_1194_);
lean_dec_ref(v_arg_1190_);
lean_dec(v_asTopVar_1181_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec_ref(v_e_1171_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_apply_2(v_toPure_1172_, lean_box(0), v___x_1230_);
return v___x_1231_;
}
}
}
}
}
}
else
{
lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v___x_1195_);
lean_dec_ref(v_arg_1194_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1174_);
v___f_1232_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_1232_, 0, v_arg_1190_);
lean_closure_set(v___f_1232_, 1, v_asTopVar_1181_);
lean_closure_set(v___f_1232_, 2, v_e_1171_);
lean_closure_set(v___f_1232_, 3, v_arg_1186_);
lean_closure_set(v___f_1232_, 4, v_toPure_1172_);
lean_closure_set(v___f_1232_, 5, v_toTopVar_1170_);
v___x_1233_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1173_, v_inst_1175_, v_inst_1176_, v_inst_1177_);
v___x_1234_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v___x_1233_, v___f_1232_);
return v___x_1234_;
}
}
else
{
lean_dec_ref(v___x_1195_);
lean_dec_ref(v_arg_1194_);
lean_dec_ref(v_arg_1186_);
lean_dec(v_toBind_1180_);
lean_dec(v_asVar_1179_);
lean_dec(v_toVar_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec(v_inst_1173_);
lean_dec(v_toTopVar_1170_);
if (lean_obj_tag(v_arg_1190_) == 9)
{
lean_object* v_a_1235_; 
v_a_1235_ = lean_ctor_get(v_arg_1190_, 0);
lean_inc_ref(v_a_1235_);
lean_dec_ref_known(v_arg_1190_, 1);
if (lean_obj_tag(v_a_1235_) == 0)
{
lean_object* v_val_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v_asTopVar_1181_);
lean_dec_ref(v_e_1171_);
v_val_1236_ = lean_ctor_get(v_a_1235_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_a_1235_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1238_ = v_a_1235_;
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_val_1236_);
lean_dec(v_a_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_nat_to_int(v_val_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
v___x_1244_ = lean_apply_2(v_toPure_1172_, lean_box(0), v___x_1243_);
return v___x_1244_;
}
}
}
else
{
lean_object* v___x_1247_; 
lean_dec_ref(v_a_1235_);
lean_dec(v_toPure_1172_);
v___x_1247_ = lean_apply_1(v_asTopVar_1181_, v_e_1171_);
return v___x_1247_;
}
}
else
{
lean_object* v___x_1248_; 
lean_dec_ref(v_arg_1190_);
lean_dec(v_toPure_1172_);
v___x_1248_ = lean_apply_1(v_asTopVar_1181_, v_e_1171_);
return v___x_1248_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_e_1256_){
_start:
{
lean_object* v_toApplicative_1257_; lean_object* v_toBind_1258_; lean_object* v_toPure_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v_asVar_1262_; lean_object* v_toVar_1263_; lean_object* v_toTopVar_1264_; lean_object* v_asTopVar_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_toApplicative_1257_ = lean_ctor_get(v_inst_1252_, 0);
v_toBind_1258_ = lean_ctor_get(v_inst_1252_, 1);
lean_inc_n(v_toBind_1258_, 6);
v_toPure_1259_ = lean_ctor_get(v_toApplicative_1257_, 1);
lean_inc_n(v_toPure_1259_, 3);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1260_, 0, v_toPure_1259_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1261_, 0, v_toPure_1259_);
lean_inc(v_inst_1249_);
lean_inc_ref(v___f_1261_);
lean_inc(v_inst_1255_);
v_asVar_1262_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v_asVar_1262_, 0, v_inst_1255_);
lean_closure_set(v_asVar_1262_, 1, v_toBind_1258_);
lean_closure_set(v_asVar_1262_, 2, v___f_1261_);
lean_closure_set(v_asVar_1262_, 3, v_inst_1249_);
v_toVar_1263_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6), 4, 3);
lean_closure_set(v_toVar_1263_, 0, v_inst_1255_);
lean_closure_set(v_toVar_1263_, 1, v_toBind_1258_);
lean_closure_set(v_toVar_1263_, 2, v___f_1261_);
lean_inc_ref(v_toVar_1263_);
v_toTopVar_1264_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v_toTopVar_1264_, 0, v_toVar_1263_);
lean_closure_set(v_toTopVar_1264_, 1, v_toBind_1258_);
lean_closure_set(v_toTopVar_1264_, 2, v___f_1260_);
lean_inc_ref(v_toTopVar_1264_);
v_asTopVar_1265_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v_asTopVar_1265_, 0, v_toTopVar_1264_);
lean_closure_set(v_asTopVar_1265_, 1, v_inst_1249_);
lean_closure_set(v_asTopVar_1265_, 2, v_toBind_1258_);
lean_inc(v_inst_1250_);
lean_inc_ref(v_e_1256_);
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5), 13, 12);
lean_closure_set(v___f_1266_, 0, v_toTopVar_1264_);
lean_closure_set(v___f_1266_, 1, v_e_1256_);
lean_closure_set(v___f_1266_, 2, v_toPure_1259_);
lean_closure_set(v___f_1266_, 3, v_inst_1250_);
lean_closure_set(v___f_1266_, 4, v_inst_1251_);
lean_closure_set(v___f_1266_, 5, v_inst_1252_);
lean_closure_set(v___f_1266_, 6, v_inst_1253_);
lean_closure_set(v___f_1266_, 7, v_inst_1254_);
lean_closure_set(v___f_1266_, 8, v_toVar_1263_);
lean_closure_set(v___f_1266_, 9, v_asVar_1262_);
lean_closure_set(v___f_1266_, 10, v_toBind_1258_);
lean_closure_set(v___f_1266_, 11, v_asTopVar_1265_);
v___x_1267_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_1267_, 0, v_e_1256_);
v___x_1268_ = lean_apply_2(v_inst_1250_, lean_box(0), v___x_1267_);
v___x_1269_ = lean_apply_4(v_toBind_1258_, lean_box(0), lean_box(0), v___x_1268_, v___f_1266_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f(lean_object* v_m_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_e_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(v_inst_1271_, v_inst_1272_, v_inst_1273_, v_inst_1274_, v_inst_1275_, v_inst_1276_, v_inst_1277_, v_e_1278_);
return v___x_1279_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Reify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Reify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Reify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Reify(builtin);
}
#ifdef __cplusplus
}
#endif
