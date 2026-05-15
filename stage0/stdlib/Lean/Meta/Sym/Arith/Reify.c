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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
lean_object* v___x_4_; uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = l_Lean_Expr_appArg_x21(v_____do__lift_3_);
v___x_5_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_4_, v_inst_1_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_box(v___x_5_);
v___x_7_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed(lean_object* v_inst_8_, lean_object* v_toPure_9_, lean_object* v_____do__lift_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0(v_inst_8_, v_toPure_9_, v_____do__lift_10_);
lean_dec_ref(v_____do__lift_10_);
lean_dec_ref(v_inst_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst___redArg(lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v_toApplicative_18_; lean_object* v_toBind_19_; lean_object* v_toPure_20_; lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___x_23_; 
v_toApplicative_18_ = lean_ctor_get(v_inst_14_, 0);
v_toBind_19_ = lean_ctor_get(v_inst_14_, 1);
lean_inc(v_toBind_19_);
v_toPure_20_ = lean_ctor_get(v_toApplicative_18_, 1);
lean_inc(v_toPure_20_);
v___x_21_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_12_, v_inst_13_, v_inst_14_, v_inst_15_, v_inst_16_);
v___f_22_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_22_, 0, v_inst_17_);
lean_closure_set(v___f_22_, 1, v_toPure_20_);
v___x_23_ = lean_apply_4(v_toBind_19_, lean_box(0), lean_box(0), v___x_21_, v___f_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isAddInst(lean_object* v_m_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_inst_29_, v_inst_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isMulInst___redArg(lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v_toApplicative_38_; lean_object* v_toBind_39_; lean_object* v_toPure_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v_toApplicative_38_ = lean_ctor_get(v_inst_34_, 0);
v_toBind_39_ = lean_ctor_get(v_inst_34_, 1);
lean_inc(v_toBind_39_);
v_toPure_40_ = lean_ctor_get(v_toApplicative_38_, 1);
lean_inc(v_toPure_40_);
v___x_41_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_inst_36_);
v___f_42_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_42_, 0, v_inst_37_);
lean_closure_set(v___f_42_, 1, v_toPure_40_);
v___x_43_ = lean_apply_4(v_toBind_39_, lean_box(0), lean_box(0), v___x_41_, v___f_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isMulInst(lean_object* v_m_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_inst_49_, v_inst_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isSubInst___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v_toApplicative_58_; lean_object* v_toBind_59_; lean_object* v_toPure_60_; lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
v_toApplicative_58_ = lean_ctor_get(v_inst_54_, 0);
v_toBind_59_ = lean_ctor_get(v_inst_54_, 1);
lean_inc(v_toBind_59_);
v_toPure_60_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_60_);
v___x_61_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_52_, v_inst_53_, v_inst_54_, v_inst_55_, v_inst_56_);
v___f_62_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_62_, 0, v_inst_57_);
lean_closure_set(v___f_62_, 1, v_toPure_60_);
v___x_63_ = lean_apply_4(v_toBind_59_, lean_box(0), lean_box(0), v___x_61_, v___f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isSubInst(lean_object* v_m_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_65_, v_inst_66_, v_inst_67_, v_inst_68_, v_inst_69_, v_inst_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___redArg(lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_){
_start:
{
lean_object* v_toApplicative_78_; lean_object* v_toBind_79_; lean_object* v_toPure_80_; lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___x_83_; 
v_toApplicative_78_ = lean_ctor_get(v_inst_74_, 0);
v_toBind_79_ = lean_ctor_get(v_inst_74_, 1);
lean_inc(v_toBind_79_);
v_toPure_80_ = lean_ctor_get(v_toApplicative_78_, 1);
lean_inc(v_toPure_80_);
v___x_81_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_inst_76_);
v___f_82_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_82_, 0, v_inst_77_);
lean_closure_set(v___f_82_, 1, v_toPure_80_);
v___x_83_ = lean_apply_4(v_toBind_79_, lean_box(0), lean_box(0), v___x_81_, v___f_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst(lean_object* v_m_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_85_, v_inst_86_, v_inst_87_, v_inst_88_, v_inst_89_, v_inst_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isPowInst___redArg(lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_){
_start:
{
lean_object* v_toApplicative_98_; lean_object* v_toBind_99_; lean_object* v_toPure_100_; lean_object* v___x_101_; lean_object* v___f_102_; lean_object* v___x_103_; 
v_toApplicative_98_ = lean_ctor_get(v_inst_94_, 0);
v_toBind_99_ = lean_ctor_get(v_inst_94_, 1);
lean_inc(v_toBind_99_);
v_toPure_100_ = lean_ctor_get(v_toApplicative_98_, 1);
lean_inc(v_toPure_100_);
v___x_101_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_92_, v_inst_93_, v_inst_94_, v_inst_95_, v_inst_96_);
v___f_102_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_102_, 0, v_inst_97_);
lean_closure_set(v___f_102_, 1, v_toPure_100_);
v___x_103_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v___x_101_, v___f_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isPowInst(lean_object* v_m_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_inst_109_, v_inst_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_){
_start:
{
lean_object* v_toApplicative_117_; lean_object* v_toBind_118_; lean_object* v_toPure_119_; lean_object* v___x_120_; lean_object* v___f_121_; lean_object* v___x_122_; 
v_toApplicative_117_ = lean_ctor_get(v_inst_113_, 0);
v_toBind_118_ = lean_ctor_get(v_inst_113_, 1);
lean_inc(v_toBind_118_);
v_toPure_119_ = lean_ctor_get(v_toApplicative_117_, 1);
lean_inc(v_toPure_119_);
v___x_120_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_112_, v_inst_113_, v_inst_114_, v_inst_115_);
v___f_121_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_121_, 0, v_inst_116_);
lean_closure_set(v___f_121_, 1, v_toPure_119_);
v___x_122_ = lean_apply_4(v_toBind_118_, lean_box(0), lean_box(0), v___x_120_, v___f_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isIntCastInst(lean_object* v_m_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_inst_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_){
_start:
{
lean_object* v_toApplicative_135_; lean_object* v_toBind_136_; lean_object* v_toPure_137_; lean_object* v___x_138_; lean_object* v___f_139_; lean_object* v___x_140_; 
v_toApplicative_135_ = lean_ctor_get(v_inst_131_, 0);
v_toBind_136_ = lean_ctor_get(v_inst_131_, 1);
lean_inc(v_toBind_136_);
v_toPure_137_ = lean_ctor_get(v_toApplicative_135_, 1);
lean_inc(v_toPure_137_);
v___x_138_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_130_, v_inst_131_, v_inst_132_, v_inst_133_);
v___f_139_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_isAddInst___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_139_, 0, v_inst_134_);
lean_closure_set(v___f_139_, 1, v_toPure_137_);
v___x_140_ = lean_apply_4(v_toBind_136_, lean_box(0), lean_box(0), v___x_138_, v___f_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNatCastInst(lean_object* v_m_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_142_, v_inst_143_, v_inst_144_, v_inst_145_, v_inst_146_);
return v___x_147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__0));
v___x_150_ = l_Lean_stringToMessageData(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(lean_object* v_inst_151_, lean_object* v_e_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1, &l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg___closed__1);
v___x_154_ = l_Lean_indentExpr(v_e_152_);
v___x_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_reportIssueIfVerbose___boxed), 8, 1);
lean_closure_set(v___x_156_, 0, v___x_155_);
v___x_157_ = lean_apply_2(v_inst_151_, lean_box(0), v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue(lean_object* v_m_158_, lean_object* v_inst_159_, lean_object* v_e_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_159_, v_e_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0(lean_object* v_toPure_162_, lean_object* v_____do__lift_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_164_, 0, v_____do__lift_163_);
v___x_165_ = lean_apply_2(v_toPure_162_, lean_box(0), v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1(lean_object* v_____do__lift_166_, lean_object* v_toPure_167_, lean_object* v_____do__lift_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v_____do__lift_166_);
lean_ctor_set(v___x_169_, 1, v_____do__lift_168_);
v___x_170_ = lean_apply_2(v_toPure_167_, lean_box(0), v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(lean_object* v_asVar_171_, lean_object* v_e_172_, lean_object* v_arg_173_, lean_object* v_toPure_174_, lean_object* v_toVar_175_, uint8_t v_____do__lift_176_){
_start:
{
if (v_____do__lift_176_ == 0)
{
lean_object* v___x_177_; 
lean_dec(v_toVar_175_);
lean_dec(v_toPure_174_);
lean_dec_ref(v_arg_173_);
v___x_177_ = lean_apply_1(v_asVar_171_, v_e_172_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; 
lean_dec(v_asVar_171_);
v___x_178_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_173_);
if (lean_obj_tag(v___x_178_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_toVar_175_);
lean_dec_ref(v_e_172_);
v_val_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 2);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_val_179_);
v___x_184_ = v_reuseFailAlloc_186_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_apply_2(v_toPure_174_, lean_box(0), v___x_184_);
return v___x_185_;
}
}
}
else
{
lean_object* v___x_188_; 
lean_dec(v___x_178_);
lean_dec(v_toPure_174_);
v___x_188_ = lean_apply_1(v_toVar_175_, v_e_172_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed(lean_object* v_asVar_189_, lean_object* v_e_190_, lean_object* v_arg_191_, lean_object* v_toPure_192_, lean_object* v_toVar_193_, lean_object* v_____do__lift_194_){
_start:
{
uint8_t v_____do__lift_4904__boxed_195_; lean_object* v_res_196_; 
v_____do__lift_4904__boxed_195_ = lean_unbox(v_____do__lift_194_);
v_res_196_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(v_asVar_189_, v_e_190_, v_arg_191_, v_toPure_192_, v_toVar_193_, v_____do__lift_4904__boxed_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7(lean_object* v_____do__lift_197_, lean_object* v_toPure_198_, lean_object* v_____do__lift_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_200_, 0, v_____do__lift_197_);
lean_ctor_set(v___x_200_, 1, v_____do__lift_199_);
v___x_201_ = lean_apply_2(v_toPure_198_, lean_box(0), v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4(lean_object* v_____do__lift_202_, lean_object* v_toPure_203_, lean_object* v_____do__lift_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_205_, 0, v_____do__lift_202_);
lean_ctor_set(v___x_205_, 1, v_____do__lift_204_);
v___x_206_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9(lean_object* v_val_207_, lean_object* v_toPure_208_, lean_object* v_____do__lift_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_210_, 0, v_____do__lift_209_);
lean_ctor_set(v___x_210_, 1, v_val_207_);
v___x_211_ = lean_apply_2(v_toPure_208_, lean_box(0), v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(lean_object* v_asVar_212_, lean_object* v_e_213_, lean_object* v_arg_214_, lean_object* v_toPure_215_, lean_object* v_toVar_216_, uint8_t v_____do__lift_217_){
_start:
{
if (v_____do__lift_217_ == 0)
{
lean_object* v___x_218_; 
lean_dec(v_toVar_216_);
lean_dec(v_toPure_215_);
lean_dec_ref(v_arg_214_);
v___x_218_ = lean_apply_1(v_asVar_212_, v_e_213_);
return v___x_218_;
}
else
{
lean_object* v___x_219_; 
lean_dec(v_asVar_212_);
v___x_219_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_214_);
if (lean_obj_tag(v___x_219_) == 1)
{
lean_object* v_val_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
lean_dec(v_toVar_216_);
lean_dec_ref(v_e_213_);
v_val_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_val_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_val_220_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
v___x_226_ = lean_apply_2(v_toPure_215_, lean_box(0), v___x_225_);
return v___x_226_;
}
}
}
else
{
lean_object* v___x_229_; 
lean_dec(v___x_219_);
lean_dec(v_toPure_215_);
v___x_229_ = lean_apply_1(v_toVar_216_, v_e_213_);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed(lean_object* v_asVar_230_, lean_object* v_e_231_, lean_object* v_arg_232_, lean_object* v_toPure_233_, lean_object* v_toVar_234_, lean_object* v_____do__lift_235_){
_start:
{
uint8_t v_____do__lift_4958__boxed_236_; lean_object* v_res_237_; 
v_____do__lift_4958__boxed_236_ = lean_unbox(v_____do__lift_235_);
v_res_237_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(v_asVar_230_, v_e_231_, v_arg_232_, v_toPure_233_, v_toVar_234_, v_____do__lift_4958__boxed_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(lean_object* v_asVar_282_, lean_object* v_e_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_toVar_289_, lean_object* v_arg_290_, lean_object* v_toBind_291_, lean_object* v___f_292_, uint8_t v_____do__lift_293_){
_start:
{
if (v_____do__lift_293_ == 0)
{
lean_object* v___x_294_; 
lean_dec(v___f_292_);
lean_dec(v_toBind_291_);
lean_dec_ref(v_arg_290_);
lean_dec(v_toVar_289_);
lean_dec_ref(v_inst_288_);
lean_dec_ref(v_inst_287_);
lean_dec_ref(v_inst_286_);
lean_dec_ref(v_inst_285_);
lean_dec(v_inst_284_);
v___x_294_ = lean_apply_1(v_asVar_282_, v_e_283_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v_e_283_);
v___x_295_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_284_, v_inst_285_, v_inst_286_, v_inst_287_, v_inst_288_, v_toVar_289_, v_asVar_282_, v_arg_290_);
v___x_296_ = lean_apply_4(v_toBind_291_, lean_box(0), lean_box(0), v___x_295_, v___f_292_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed(lean_object* v_asVar_297_, lean_object* v_e_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_toVar_304_, lean_object* v_arg_305_, lean_object* v_toBind_306_, lean_object* v___f_307_, lean_object* v_____do__lift_308_){
_start:
{
uint8_t v_____do__lift_5068__boxed_309_; lean_object* v_res_310_; 
v_____do__lift_5068__boxed_309_ = lean_unbox(v_____do__lift_308_);
v_res_310_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(v_asVar_297_, v_e_298_, v_inst_299_, v_inst_300_, v_inst_301_, v_inst_302_, v_inst_303_, v_toVar_304_, v_arg_305_, v_toBind_306_, v___f_307_, v_____do__lift_5068__boxed_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5(lean_object* v_toPure_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_toVar_317_, lean_object* v_asVar_318_, lean_object* v_arg_319_, lean_object* v_toBind_320_, lean_object* v_____do__lift_321_){
_start:
{
lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___f_322_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_322_, 0, v_____do__lift_321_);
lean_closure_set(v___f_322_, 1, v_toPure_311_);
v___x_323_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_312_, v_inst_313_, v_inst_314_, v_inst_315_, v_inst_316_, v_toVar_317_, v_asVar_318_, v_arg_319_);
v___x_324_ = lean_apply_4(v_toBind_320_, lean_box(0), lean_box(0), v___x_323_, v___f_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6(lean_object* v_toPure_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_toVar_331_, lean_object* v_asVar_332_, lean_object* v_arg_333_, lean_object* v_toBind_334_, lean_object* v_____do__lift_335_){
_start:
{
lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___f_336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7), 3, 2);
lean_closure_set(v___f_336_, 0, v_____do__lift_335_);
lean_closure_set(v___f_336_, 1, v_toPure_325_);
v___x_337_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_326_, v_inst_327_, v_inst_328_, v_inst_329_, v_inst_330_, v_toVar_331_, v_asVar_332_, v_arg_333_);
v___x_338_ = lean_apply_4(v_toBind_334_, lean_box(0), lean_box(0), v___x_337_, v___f_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10(lean_object* v_toVar_339_, lean_object* v_e_340_, lean_object* v_toPure_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_asVar_347_, lean_object* v_toBind_348_, lean_object* v___f_349_, lean_object* v_____x_350_){
_start:
{
lean_object* v_n_352_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = l_Lean_Expr_cleanupAnnotations(v_____x_350_);
v___x_367_ = l_Lean_Expr_isApp(v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec_ref(v___x_366_);
lean_dec(v___f_349_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
lean_dec(v_toPure_341_);
v___x_368_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_368_;
}
else
{
lean_object* v_arg_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_arg_369_ = lean_ctor_get(v___x_366_, 1);
lean_inc_ref(v_arg_369_);
v___x_370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_366_);
v___x_371_ = l_Lean_Expr_isApp(v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec_ref(v___x_370_);
lean_dec_ref(v_arg_369_);
lean_dec(v___f_349_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
lean_dec(v_toPure_341_);
v___x_372_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_372_;
}
else
{
lean_object* v_arg_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_arg_373_ = lean_ctor_get(v___x_370_, 1);
lean_inc_ref(v_arg_373_);
v___x_374_ = l_Lean_Expr_appFnCleanup___redArg(v___x_370_);
v___x_375_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2));
v___x_376_ = l_Lean_Expr_isConstOf(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
uint8_t v___x_377_; 
v___x_377_ = l_Lean_Expr_isApp(v___x_374_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec_ref(v___x_374_);
lean_dec_ref(v_arg_373_);
lean_dec_ref(v_arg_369_);
lean_dec(v___f_349_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
lean_dec(v_toPure_341_);
v___x_378_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_378_;
}
else
{
lean_object* v_arg_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_arg_379_ = lean_ctor_get(v___x_374_, 1);
lean_inc_ref(v_arg_379_);
v___x_380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_374_);
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_382_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_384_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10));
v___x_386_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13));
v___x_388_ = l_Lean_Expr_isConstOf(v___x_380_, v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
lean_dec(v___f_349_);
v___x_389_ = l_Lean_Expr_isApp(v___x_380_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v___x_380_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_373_);
lean_dec_ref(v_arg_369_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
lean_dec(v_toPure_341_);
v___x_390_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = l_Lean_Expr_appFnCleanup___redArg(v___x_380_);
v___x_392_ = l_Lean_Expr_isApp(v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec_ref(v___x_391_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_373_);
lean_dec_ref(v_arg_369_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
lean_dec(v_toPure_341_);
v___x_393_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_391_);
v___x_395_ = l_Lean_Expr_isApp(v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v___x_394_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_373_);
lean_dec_ref(v_arg_369_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
lean_dec(v_toPure_341_);
v___x_396_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = l_Lean_Expr_appFnCleanup___redArg(v___x_394_);
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_399_ = l_Lean_Expr_isConstOf(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19));
v___x_401_ = l_Lean_Expr_isConstOf(v___x_397_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_403_ = l_Lean_Expr_isConstOf(v___x_397_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_405_ = l_Lean_Expr_isConstOf(v___x_397_, v___x_404_);
lean_dec_ref(v___x_397_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_373_);
lean_dec_ref(v_arg_369_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
lean_dec(v_toPure_341_);
v___x_406_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_406_;
}
else
{
lean_object* v___f_407_; lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_inc_n(v_toBind_348_, 2);
lean_inc(v_asVar_347_);
lean_inc(v_toVar_339_);
lean_inc_ref_n(v_inst_346_, 2);
lean_inc_ref_n(v_inst_345_, 2);
lean_inc_ref_n(v_inst_344_, 2);
lean_inc_ref_n(v_inst_343_, 2);
lean_inc_n(v_inst_342_, 2);
v___f_407_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2), 11, 10);
lean_closure_set(v___f_407_, 0, v_toPure_341_);
lean_closure_set(v___f_407_, 1, v_inst_342_);
lean_closure_set(v___f_407_, 2, v_inst_343_);
lean_closure_set(v___f_407_, 3, v_inst_344_);
lean_closure_set(v___f_407_, 4, v_inst_345_);
lean_closure_set(v___f_407_, 5, v_inst_346_);
lean_closure_set(v___f_407_, 6, v_toVar_339_);
lean_closure_set(v___f_407_, 7, v_asVar_347_);
lean_closure_set(v___f_407_, 8, v_arg_369_);
lean_closure_set(v___f_407_, 9, v_toBind_348_);
v___f_408_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_408_, 0, v_asVar_347_);
lean_closure_set(v___f_408_, 1, v_e_340_);
lean_closure_set(v___f_408_, 2, v_inst_342_);
lean_closure_set(v___f_408_, 3, v_inst_343_);
lean_closure_set(v___f_408_, 4, v_inst_344_);
lean_closure_set(v___f_408_, 5, v_inst_345_);
lean_closure_set(v___f_408_, 6, v_inst_346_);
lean_closure_set(v___f_408_, 7, v_toVar_339_);
lean_closure_set(v___f_408_, 8, v_arg_373_);
lean_closure_set(v___f_408_, 9, v_toBind_348_);
lean_closure_set(v___f_408_, 10, v___f_407_);
v___x_409_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_342_, v_inst_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_arg_379_);
v___x_410_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_409_, v___f_408_);
return v___x_410_;
}
}
else
{
lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref(v___x_397_);
lean_inc_n(v_toBind_348_, 2);
lean_inc(v_asVar_347_);
lean_inc(v_toVar_339_);
lean_inc_ref_n(v_inst_346_, 2);
lean_inc_ref_n(v_inst_345_, 2);
lean_inc_ref_n(v_inst_344_, 2);
lean_inc_ref_n(v_inst_343_, 2);
lean_inc_n(v_inst_342_, 2);
v___f_411_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5), 11, 10);
lean_closure_set(v___f_411_, 0, v_toPure_341_);
lean_closure_set(v___f_411_, 1, v_inst_342_);
lean_closure_set(v___f_411_, 2, v_inst_343_);
lean_closure_set(v___f_411_, 3, v_inst_344_);
lean_closure_set(v___f_411_, 4, v_inst_345_);
lean_closure_set(v___f_411_, 5, v_inst_346_);
lean_closure_set(v___f_411_, 6, v_toVar_339_);
lean_closure_set(v___f_411_, 7, v_asVar_347_);
lean_closure_set(v___f_411_, 8, v_arg_369_);
lean_closure_set(v___f_411_, 9, v_toBind_348_);
v___f_412_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_412_, 0, v_asVar_347_);
lean_closure_set(v___f_412_, 1, v_e_340_);
lean_closure_set(v___f_412_, 2, v_inst_342_);
lean_closure_set(v___f_412_, 3, v_inst_343_);
lean_closure_set(v___f_412_, 4, v_inst_344_);
lean_closure_set(v___f_412_, 5, v_inst_345_);
lean_closure_set(v___f_412_, 6, v_inst_346_);
lean_closure_set(v___f_412_, 7, v_toVar_339_);
lean_closure_set(v___f_412_, 8, v_arg_373_);
lean_closure_set(v___f_412_, 9, v_toBind_348_);
lean_closure_set(v___f_412_, 10, v___f_411_);
v___x_413_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_342_, v_inst_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_arg_379_);
v___x_414_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_413_, v___f_412_);
return v___x_414_;
}
}
else
{
lean_object* v___f_415_; lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v___x_397_);
lean_inc_n(v_toBind_348_, 2);
lean_inc(v_asVar_347_);
lean_inc(v_toVar_339_);
lean_inc_ref_n(v_inst_346_, 2);
lean_inc_ref_n(v_inst_345_, 2);
lean_inc_ref_n(v_inst_344_, 2);
lean_inc_ref_n(v_inst_343_, 2);
lean_inc_n(v_inst_342_, 2);
v___f_415_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6), 11, 10);
lean_closure_set(v___f_415_, 0, v_toPure_341_);
lean_closure_set(v___f_415_, 1, v_inst_342_);
lean_closure_set(v___f_415_, 2, v_inst_343_);
lean_closure_set(v___f_415_, 3, v_inst_344_);
lean_closure_set(v___f_415_, 4, v_inst_345_);
lean_closure_set(v___f_415_, 5, v_inst_346_);
lean_closure_set(v___f_415_, 6, v_toVar_339_);
lean_closure_set(v___f_415_, 7, v_asVar_347_);
lean_closure_set(v___f_415_, 8, v_arg_369_);
lean_closure_set(v___f_415_, 9, v_toBind_348_);
v___f_416_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_416_, 0, v_asVar_347_);
lean_closure_set(v___f_416_, 1, v_e_340_);
lean_closure_set(v___f_416_, 2, v_inst_342_);
lean_closure_set(v___f_416_, 3, v_inst_343_);
lean_closure_set(v___f_416_, 4, v_inst_344_);
lean_closure_set(v___f_416_, 5, v_inst_345_);
lean_closure_set(v___f_416_, 6, v_inst_346_);
lean_closure_set(v___f_416_, 7, v_toVar_339_);
lean_closure_set(v___f_416_, 8, v_arg_373_);
lean_closure_set(v___f_416_, 9, v_toBind_348_);
lean_closure_set(v___f_416_, 10, v___f_415_);
v___x_417_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_342_, v_inst_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_arg_379_);
v___x_418_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_417_, v___f_416_);
return v___x_418_;
}
}
else
{
lean_object* v___x_419_; 
lean_dec_ref(v___x_397_);
v___x_419_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_369_);
if (lean_obj_tag(v___x_419_) == 1)
{
lean_object* v_val_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_val_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_val_420_);
lean_dec_ref(v___x_419_);
v___f_421_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9), 3, 2);
lean_closure_set(v___f_421_, 0, v_val_420_);
lean_closure_set(v___f_421_, 1, v_toPure_341_);
lean_inc(v_toBind_348_);
lean_inc_ref(v_inst_346_);
lean_inc_ref(v_inst_345_);
lean_inc_ref(v_inst_344_);
lean_inc_ref(v_inst_343_);
lean_inc(v_inst_342_);
v___f_422_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_422_, 0, v_asVar_347_);
lean_closure_set(v___f_422_, 1, v_e_340_);
lean_closure_set(v___f_422_, 2, v_inst_342_);
lean_closure_set(v___f_422_, 3, v_inst_343_);
lean_closure_set(v___f_422_, 4, v_inst_344_);
lean_closure_set(v___f_422_, 5, v_inst_345_);
lean_closure_set(v___f_422_, 6, v_inst_346_);
lean_closure_set(v___f_422_, 7, v_toVar_339_);
lean_closure_set(v___f_422_, 8, v_arg_373_);
lean_closure_set(v___f_422_, 9, v_toBind_348_);
lean_closure_set(v___f_422_, 10, v___f_421_);
v___x_423_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_342_, v_inst_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_arg_379_);
v___x_424_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_423_, v___f_422_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; 
lean_dec(v___x_419_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_373_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
lean_dec(v_toPure_341_);
v___x_425_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_425_;
}
}
}
}
}
}
else
{
lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref(v___x_380_);
lean_dec_ref(v_arg_379_);
lean_dec(v_toPure_341_);
lean_inc(v_toBind_348_);
lean_inc_ref(v_inst_346_);
lean_inc_ref(v_inst_345_);
lean_inc_ref(v_inst_344_);
lean_inc_ref(v_inst_343_);
lean_inc(v_inst_342_);
v___f_426_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_426_, 0, v_asVar_347_);
lean_closure_set(v___f_426_, 1, v_e_340_);
lean_closure_set(v___f_426_, 2, v_inst_342_);
lean_closure_set(v___f_426_, 3, v_inst_343_);
lean_closure_set(v___f_426_, 4, v_inst_344_);
lean_closure_set(v___f_426_, 5, v_inst_345_);
lean_closure_set(v___f_426_, 6, v_inst_346_);
lean_closure_set(v___f_426_, 7, v_toVar_339_);
lean_closure_set(v___f_426_, 8, v_arg_369_);
lean_closure_set(v___f_426_, 9, v_toBind_348_);
lean_closure_set(v___f_426_, 10, v___f_349_);
v___x_427_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_342_, v_inst_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_arg_373_);
v___x_428_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_427_, v___f_426_);
return v___x_428_;
}
}
else
{
lean_object* v___f_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v___x_380_);
lean_dec_ref(v_arg_379_);
lean_dec(v___f_349_);
lean_dec_ref(v_inst_343_);
v___f_429_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_429_, 0, v_asVar_347_);
lean_closure_set(v___f_429_, 1, v_e_340_);
lean_closure_set(v___f_429_, 2, v_arg_369_);
lean_closure_set(v___f_429_, 3, v_toPure_341_);
lean_closure_set(v___f_429_, 4, v_toVar_339_);
v___x_430_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_342_, v_inst_344_, v_inst_345_, v_inst_346_, v_arg_373_);
v___x_431_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_430_, v___f_429_);
return v___x_431_;
}
}
else
{
lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec_ref(v___x_380_);
lean_dec_ref(v_arg_379_);
lean_dec(v___f_349_);
lean_dec_ref(v_inst_343_);
v___f_432_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed), 6, 5);
lean_closure_set(v___f_432_, 0, v_asVar_347_);
lean_closure_set(v___f_432_, 1, v_e_340_);
lean_closure_set(v___f_432_, 2, v_arg_369_);
lean_closure_set(v___f_432_, 3, v_toPure_341_);
lean_closure_set(v___f_432_, 4, v_toVar_339_);
v___x_433_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_342_, v_inst_344_, v_inst_345_, v_inst_346_, v_arg_373_);
v___x_434_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_433_, v___f_432_);
return v___x_434_;
}
}
else
{
lean_dec_ref(v___x_380_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_369_);
lean_dec(v___f_349_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
v_n_352_ = v_arg_373_;
goto v___jp_351_;
}
}
}
else
{
lean_dec_ref(v___x_374_);
lean_dec_ref(v_arg_373_);
lean_dec(v___f_349_);
lean_dec(v_toBind_348_);
lean_dec(v_asVar_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
v_n_352_ = v_arg_369_;
goto v___jp_351_;
}
}
}
v___jp_351_:
{
if (lean_obj_tag(v_n_352_) == 9)
{
lean_object* v_a_353_; 
v_a_353_ = lean_ctor_get(v_n_352_, 0);
lean_inc_ref(v_a_353_);
lean_dec_ref(v_n_352_);
if (lean_obj_tag(v_a_353_) == 0)
{
lean_object* v_val_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref(v_e_340_);
lean_dec(v_toVar_339_);
v_val_354_ = lean_ctor_get(v_a_353_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_353_);
if (v_isSharedCheck_363_ == 0)
{
v___x_356_ = v_a_353_;
v_isShared_357_ = v_isSharedCheck_363_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_val_354_);
lean_dec(v_a_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_363_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_358_ = lean_nat_to_int(v_val_354_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_358_);
v___x_360_ = v___x_356_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_362_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_2(v_toPure_341_, lean_box(0), v___x_360_);
return v___x_361_;
}
}
}
else
{
lean_object* v___x_364_; 
lean_dec_ref(v_a_353_);
lean_dec(v_toPure_341_);
v___x_364_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_364_;
}
}
else
{
lean_object* v___x_365_; 
lean_dec_ref(v_n_352_);
lean_dec(v_toPure_341_);
v___x_365_ = lean_apply_1(v_toVar_339_, v_e_340_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_toVar_440_, lean_object* v_asVar_441_, lean_object* v_e_442_){
_start:
{
lean_object* v_toApplicative_443_; lean_object* v_toBind_444_; lean_object* v_toPure_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___x_450_; 
v_toApplicative_443_ = lean_ctor_get(v_inst_437_, 0);
v_toBind_444_ = lean_ctor_get(v_inst_437_, 1);
lean_inc_n(v_toBind_444_, 2);
v_toPure_445_ = lean_ctor_get(v_toApplicative_443_, 1);
lean_inc_n(v_toPure_445_, 2);
lean_inc_ref(v_e_442_);
v___x_446_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_446_, 0, v_e_442_);
lean_inc(v_inst_435_);
v___x_447_ = lean_apply_2(v_inst_435_, lean_box(0), v___x_446_);
v___f_448_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_448_, 0, v_toPure_445_);
v___f_449_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10), 12, 11);
lean_closure_set(v___f_449_, 0, v_toVar_440_);
lean_closure_set(v___f_449_, 1, v_e_442_);
lean_closure_set(v___f_449_, 2, v_toPure_445_);
lean_closure_set(v___f_449_, 3, v_inst_435_);
lean_closure_set(v___f_449_, 4, v_inst_436_);
lean_closure_set(v___f_449_, 5, v_inst_437_);
lean_closure_set(v___f_449_, 6, v_inst_438_);
lean_closure_set(v___f_449_, 7, v_inst_439_);
lean_closure_set(v___f_449_, 8, v_asVar_441_);
lean_closure_set(v___f_449_, 9, v_toBind_444_);
lean_closure_set(v___f_449_, 10, v___f_448_);
v___x_450_ = lean_apply_4(v_toBind_444_, lean_box(0), lean_box(0), v___x_447_, v___f_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2(lean_object* v_toPure_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_toVar_457_, lean_object* v_asVar_458_, lean_object* v_arg_459_, lean_object* v_toBind_460_, lean_object* v_____do__lift_461_){
_start:
{
lean_object* v___f_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___f_462_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_462_, 0, v_____do__lift_461_);
lean_closure_set(v___f_462_, 1, v_toPure_451_);
v___x_463_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_452_, v_inst_453_, v_inst_454_, v_inst_455_, v_inst_456_, v_toVar_457_, v_asVar_458_, v_arg_459_);
v___x_464_ = lean_apply_4(v_toBind_460_, lean_box(0), lean_box(0), v___x_463_, v___f_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go(lean_object* v_m_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_toVar_471_, lean_object* v_asVar_472_, lean_object* v_e_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_466_, v_inst_467_, v_inst_468_, v_inst_469_, v_inst_470_, v_toVar_471_, v_asVar_472_, v_e_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0(lean_object* v_toPure_475_, lean_object* v_____do__lift_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_477_, 0, v_____do__lift_476_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
v___x_479_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1(lean_object* v_toPure_480_, lean_object* v_____do__lift_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v_____do__lift_481_);
v___x_483_ = lean_apply_2(v_toPure_480_, lean_box(0), v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2(lean_object* v_toPure_484_, lean_object* v_____do__lift_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_486_, 0, v_____do__lift_485_);
v___x_487_ = lean_apply_2(v_toPure_484_, lean_box(0), v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3(lean_object* v_inst_488_, lean_object* v_e_489_, lean_object* v_toBind_490_, lean_object* v___f_491_, lean_object* v_____r_492_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_apply_1(v_inst_488_, v_e_489_);
v___x_494_ = lean_apply_4(v_toBind_490_, lean_box(0), lean_box(0), v___x_493_, v___f_491_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4(lean_object* v_inst_495_, lean_object* v_toBind_496_, lean_object* v___f_497_, lean_object* v_inst_498_, lean_object* v_e_499_){
_start:
{
lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_inc(v_toBind_496_);
lean_inc_ref(v_e_499_);
v___f_500_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_500_, 0, v_inst_495_);
lean_closure_set(v___f_500_, 1, v_e_499_);
lean_closure_set(v___f_500_, 2, v_toBind_496_);
lean_closure_set(v___f_500_, 3, v___f_497_);
v___x_501_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_498_, v_e_499_);
v___x_502_ = lean_apply_4(v_toBind_496_, lean_box(0), lean_box(0), v___x_501_, v___f_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6(lean_object* v_inst_503_, lean_object* v_toBind_504_, lean_object* v___f_505_, lean_object* v_e_506_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_apply_1(v_inst_503_, v_e_506_);
v___x_508_ = lean_apply_4(v_toBind_504_, lean_box(0), lean_box(0), v___x_507_, v___f_505_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(uint8_t v_skipVar_509_, lean_object* v_toVar_510_, lean_object* v_toBind_511_, lean_object* v___f_512_, lean_object* v_toPure_513_, lean_object* v_e_514_){
_start:
{
if (v_skipVar_509_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_toPure_513_);
v___x_515_ = lean_apply_1(v_toVar_510_, v_e_514_);
v___x_516_ = lean_apply_4(v_toBind_511_, lean_box(0), lean_box(0), v___x_515_, v___f_512_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec_ref(v_e_514_);
lean_dec(v___f_512_);
lean_dec(v_toBind_511_);
lean_dec(v_toVar_510_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_apply_2(v_toPure_513_, lean_box(0), v___x_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed(lean_object* v_skipVar_519_, lean_object* v_toVar_520_, lean_object* v_toBind_521_, lean_object* v___f_522_, lean_object* v_toPure_523_, lean_object* v_e_524_){
_start:
{
uint8_t v_skipVar_boxed_525_; lean_object* v_res_526_; 
v_skipVar_boxed_525_ = lean_unbox(v_skipVar_519_);
v_res_526_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(v_skipVar_boxed_525_, v_toVar_520_, v_toBind_521_, v___f_522_, v_toPure_523_, v_e_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7(lean_object* v_toTopVar_527_, lean_object* v_e_528_, lean_object* v_____r_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_apply_1(v_toTopVar_527_, v_e_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8(lean_object* v_toTopVar_531_, lean_object* v_inst_532_, lean_object* v_toBind_533_, lean_object* v_e_534_){
_start:
{
lean_object* v___f_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_inc_ref(v_e_534_);
v___f_535_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7), 3, 2);
lean_closure_set(v___f_535_, 0, v_toTopVar_531_);
lean_closure_set(v___f_535_, 1, v_e_534_);
v___x_536_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_532_, v_e_534_);
v___x_537_ = lean_apply_4(v_toBind_533_, lean_box(0), lean_box(0), v___x_536_, v___f_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9(lean_object* v_____do__lift_538_, lean_object* v_toPure_539_, lean_object* v_____do__lift_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_541_, 0, v_____do__lift_538_);
lean_ctor_set(v___x_541_, 1, v_____do__lift_540_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___x_543_ = lean_apply_2(v_toPure_539_, lean_box(0), v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10(lean_object* v_toPure_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_toVar_550_, lean_object* v_asVar_551_, lean_object* v_arg_552_, lean_object* v_toBind_553_, lean_object* v_____do__lift_554_){
_start:
{
lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___f_555_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9), 3, 2);
lean_closure_set(v___f_555_, 0, v_____do__lift_554_);
lean_closure_set(v___f_555_, 1, v_toPure_544_);
v___x_556_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_545_, v_inst_546_, v_inst_547_, v_inst_548_, v_inst_549_, v_toVar_550_, v_asVar_551_, v_arg_552_);
v___x_557_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v___x_556_, v___f_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(lean_object* v_asTopVar_558_, lean_object* v_e_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_toVar_565_, lean_object* v_asVar_566_, lean_object* v_arg_567_, lean_object* v_toBind_568_, lean_object* v___f_569_, uint8_t v_____do__lift_570_){
_start:
{
if (v_____do__lift_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v___f_569_);
lean_dec(v_toBind_568_);
lean_dec_ref(v_arg_567_);
lean_dec(v_asVar_566_);
lean_dec(v_toVar_565_);
lean_dec_ref(v_inst_564_);
lean_dec_ref(v_inst_563_);
lean_dec_ref(v_inst_562_);
lean_dec_ref(v_inst_561_);
lean_dec(v_inst_560_);
v___x_571_ = lean_apply_1(v_asTopVar_558_, v_e_559_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec_ref(v_e_559_);
lean_dec(v_asTopVar_558_);
v___x_572_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_560_, v_inst_561_, v_inst_562_, v_inst_563_, v_inst_564_, v_toVar_565_, v_asVar_566_, v_arg_567_);
v___x_573_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v___x_572_, v___f_569_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed(lean_object* v_asTopVar_574_, lean_object* v_e_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_toVar_581_, lean_object* v_asVar_582_, lean_object* v_arg_583_, lean_object* v_toBind_584_, lean_object* v___f_585_, lean_object* v_____do__lift_586_){
_start:
{
uint8_t v_____do__lift_4902__boxed_587_; lean_object* v_res_588_; 
v_____do__lift_4902__boxed_587_ = lean_unbox(v_____do__lift_586_);
v_res_588_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(v_asTopVar_574_, v_e_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_inst_580_, v_toVar_581_, v_asVar_582_, v_arg_583_, v_toBind_584_, v___f_585_, v_____do__lift_4902__boxed_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12(lean_object* v_____do__lift_589_, lean_object* v_toPure_590_, lean_object* v_____do__lift_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v_____do__lift_589_);
lean_ctor_set(v___x_592_, 1, v_____do__lift_591_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_apply_2(v_toPure_590_, lean_box(0), v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13(lean_object* v_toPure_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_toVar_601_, lean_object* v_asVar_602_, lean_object* v_arg_603_, lean_object* v_toBind_604_, lean_object* v_____do__lift_605_){
_start:
{
lean_object* v___f_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___f_606_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12), 3, 2);
lean_closure_set(v___f_606_, 0, v_____do__lift_605_);
lean_closure_set(v___f_606_, 1, v_toPure_595_);
v___x_607_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_596_, v_inst_597_, v_inst_598_, v_inst_599_, v_inst_600_, v_toVar_601_, v_asVar_602_, v_arg_603_);
v___x_608_ = lean_apply_4(v_toBind_604_, lean_box(0), lean_box(0), v___x_607_, v___f_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15(lean_object* v_____do__lift_609_, lean_object* v_toPure_610_, lean_object* v_____do__lift_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_612_, 0, v_____do__lift_609_);
lean_ctor_set(v___x_612_, 1, v_____do__lift_611_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v___x_614_ = lean_apply_2(v_toPure_610_, lean_box(0), v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14(lean_object* v_toPure_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_toVar_621_, lean_object* v_asVar_622_, lean_object* v_arg_623_, lean_object* v_toBind_624_, lean_object* v_____do__lift_625_){
_start:
{
lean_object* v___f_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___f_626_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15), 3, 2);
lean_closure_set(v___f_626_, 0, v_____do__lift_625_);
lean_closure_set(v___f_626_, 1, v_toPure_615_);
v___x_627_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_616_, v_inst_617_, v_inst_618_, v_inst_619_, v_inst_620_, v_toVar_621_, v_asVar_622_, v_arg_623_);
v___x_628_ = lean_apply_4(v_toBind_624_, lean_box(0), lean_box(0), v___x_627_, v___f_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17(lean_object* v_val_629_, lean_object* v_toPure_630_, lean_object* v_____do__lift_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_632_, 0, v_____do__lift_631_);
lean_ctor_set(v___x_632_, 1, v_val_629_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_apply_2(v_toPure_630_, lean_box(0), v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(lean_object* v_asTopVar_635_, lean_object* v_e_636_, lean_object* v_arg_637_, lean_object* v_toPure_638_, lean_object* v_toTopVar_639_, uint8_t v_____do__lift_640_){
_start:
{
if (v_____do__lift_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v_toTopVar_639_);
lean_dec(v_toPure_638_);
lean_dec_ref(v_arg_637_);
v___x_641_ = lean_apply_1(v_asTopVar_635_, v_e_636_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; 
lean_dec(v_asTopVar_635_);
v___x_642_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_637_);
if (lean_obj_tag(v___x_642_) == 1)
{
lean_object* v_val_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_toTopVar_639_);
lean_dec_ref(v_e_636_);
v_val_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_652_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_val_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_647_, 0, v_val_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_651_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; 
v___x_650_ = lean_apply_2(v_toPure_638_, lean_box(0), v___x_649_);
return v___x_650_;
}
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v___x_642_);
lean_dec(v_toPure_638_);
v___x_653_ = lean_apply_1(v_toTopVar_639_, v_e_636_);
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed(lean_object* v_asTopVar_654_, lean_object* v_e_655_, lean_object* v_arg_656_, lean_object* v_toPure_657_, lean_object* v_toTopVar_658_, lean_object* v_____do__lift_659_){
_start:
{
uint8_t v_____do__lift_4996__boxed_660_; lean_object* v_res_661_; 
v_____do__lift_4996__boxed_660_ = lean_unbox(v_____do__lift_659_);
v_res_661_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(v_asTopVar_654_, v_e_655_, v_arg_656_, v_toPure_657_, v_toTopVar_658_, v_____do__lift_4996__boxed_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(lean_object* v_asTopVar_662_, lean_object* v_e_663_, lean_object* v_arg_664_, lean_object* v_toPure_665_, lean_object* v_toTopVar_666_, uint8_t v_____do__lift_667_){
_start:
{
if (v_____do__lift_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec(v_toTopVar_666_);
lean_dec(v_toPure_665_);
lean_dec_ref(v_arg_664_);
v___x_668_ = lean_apply_1(v_asTopVar_662_, v_e_663_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; 
lean_dec(v_asTopVar_662_);
v___x_669_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_664_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_679_; 
lean_dec(v_toTopVar_666_);
lean_dec_ref(v_e_663_);
v_val_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_679_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_val_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_678_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; 
v___x_677_ = lean_apply_2(v_toPure_665_, lean_box(0), v___x_676_);
return v___x_677_;
}
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v___x_669_);
lean_dec(v_toPure_665_);
v___x_680_ = lean_apply_1(v_toTopVar_666_, v_e_663_);
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed(lean_object* v_asTopVar_681_, lean_object* v_e_682_, lean_object* v_arg_683_, lean_object* v_toPure_684_, lean_object* v_toTopVar_685_, lean_object* v_____do__lift_686_){
_start:
{
uint8_t v_____do__lift_5028__boxed_687_; lean_object* v_res_688_; 
v_____do__lift_5028__boxed_687_ = lean_unbox(v_____do__lift_686_);
v_res_688_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(v_asTopVar_681_, v_e_682_, v_arg_683_, v_toPure_684_, v_toTopVar_685_, v_____do__lift_5028__boxed_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18(lean_object* v_toTopVar_689_, lean_object* v_e_690_, lean_object* v_toPure_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_toVar_697_, lean_object* v_asVar_698_, lean_object* v_toBind_699_, lean_object* v_asTopVar_700_, lean_object* v___f_701_, lean_object* v_____x_702_){
_start:
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = l_Lean_Expr_cleanupAnnotations(v_____x_702_);
v___x_704_ = l_Lean_Expr_isApp(v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
lean_dec_ref(v___x_703_);
lean_dec(v___f_701_);
lean_dec(v_asTopVar_700_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toPure_691_);
v___x_705_ = lean_apply_1(v_toTopVar_689_, v_e_690_);
return v___x_705_;
}
else
{
lean_object* v_arg_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_arg_706_ = lean_ctor_get(v___x_703_, 1);
lean_inc_ref(v_arg_706_);
v___x_707_ = l_Lean_Expr_appFnCleanup___redArg(v___x_703_);
v___x_708_ = l_Lean_Expr_isApp(v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec_ref(v___x_707_);
lean_dec_ref(v_arg_706_);
lean_dec(v___f_701_);
lean_dec(v_asTopVar_700_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toPure_691_);
v___x_709_ = lean_apply_1(v_toTopVar_689_, v_e_690_);
return v___x_709_;
}
else
{
lean_object* v_arg_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_arg_710_ = lean_ctor_get(v___x_707_, 1);
lean_inc_ref(v_arg_710_);
v___x_711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_707_);
v___x_712_ = l_Lean_Expr_isApp(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v___x_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_706_);
lean_dec(v___f_701_);
lean_dec(v_asTopVar_700_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toPure_691_);
v___x_713_ = lean_apply_1(v_toTopVar_689_, v_e_690_);
return v___x_713_;
}
else
{
lean_object* v_arg_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_arg_714_ = lean_ctor_get(v___x_711_, 1);
lean_inc_ref(v_arg_714_);
v___x_715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_711_);
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_717_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_719_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10));
v___x_721_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13));
v___x_723_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_722_);
if (v___x_723_ == 0)
{
uint8_t v___x_724_; 
lean_dec(v___f_701_);
v___x_724_ = l_Lean_Expr_isApp(v___x_715_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec_ref(v___x_715_);
lean_dec_ref(v_arg_714_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_706_);
lean_dec(v_asTopVar_700_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toPure_691_);
v___x_725_ = lean_apply_1(v_toTopVar_689_, v_e_690_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = l_Lean_Expr_appFnCleanup___redArg(v___x_715_);
v___x_727_ = l_Lean_Expr_isApp(v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec_ref(v___x_726_);
lean_dec_ref(v_arg_714_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_706_);
lean_dec(v_asTopVar_700_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toPure_691_);
v___x_728_ = lean_apply_1(v_toTopVar_689_, v_e_690_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = l_Lean_Expr_appFnCleanup___redArg(v___x_726_);
v___x_730_ = l_Lean_Expr_isApp(v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec_ref(v___x_729_);
lean_dec_ref(v_arg_714_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_706_);
lean_dec(v_asTopVar_700_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toPure_691_);
v___x_731_ = lean_apply_1(v_toTopVar_689_, v_e_690_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_729_);
v___x_733_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_734_ = l_Lean_Expr_isConstOf(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19));
v___x_736_ = l_Lean_Expr_isConstOf(v___x_732_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_738_ = l_Lean_Expr_isConstOf(v___x_732_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_740_ = l_Lean_Expr_isConstOf(v___x_732_, v___x_739_);
lean_dec_ref(v___x_732_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec_ref(v_arg_714_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_706_);
lean_dec(v_asTopVar_700_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toPure_691_);
v___x_741_ = lean_apply_1(v_toTopVar_689_, v_e_690_);
return v___x_741_;
}
else
{
lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec(v_toTopVar_689_);
lean_inc_n(v_toBind_699_, 2);
lean_inc(v_asVar_698_);
lean_inc(v_toVar_697_);
lean_inc_ref_n(v_inst_696_, 2);
lean_inc_ref_n(v_inst_695_, 2);
lean_inc_ref_n(v_inst_694_, 2);
lean_inc_ref_n(v_inst_693_, 2);
lean_inc_n(v_inst_692_, 2);
v___f_742_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10), 11, 10);
lean_closure_set(v___f_742_, 0, v_toPure_691_);
lean_closure_set(v___f_742_, 1, v_inst_692_);
lean_closure_set(v___f_742_, 2, v_inst_693_);
lean_closure_set(v___f_742_, 3, v_inst_694_);
lean_closure_set(v___f_742_, 4, v_inst_695_);
lean_closure_set(v___f_742_, 5, v_inst_696_);
lean_closure_set(v___f_742_, 6, v_toVar_697_);
lean_closure_set(v___f_742_, 7, v_asVar_698_);
lean_closure_set(v___f_742_, 8, v_arg_706_);
lean_closure_set(v___f_742_, 9, v_toBind_699_);
v___f_743_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_743_, 0, v_asTopVar_700_);
lean_closure_set(v___f_743_, 1, v_e_690_);
lean_closure_set(v___f_743_, 2, v_inst_692_);
lean_closure_set(v___f_743_, 3, v_inst_693_);
lean_closure_set(v___f_743_, 4, v_inst_694_);
lean_closure_set(v___f_743_, 5, v_inst_695_);
lean_closure_set(v___f_743_, 6, v_inst_696_);
lean_closure_set(v___f_743_, 7, v_toVar_697_);
lean_closure_set(v___f_743_, 8, v_asVar_698_);
lean_closure_set(v___f_743_, 9, v_arg_710_);
lean_closure_set(v___f_743_, 10, v_toBind_699_);
lean_closure_set(v___f_743_, 11, v___f_742_);
v___x_744_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_692_, v_inst_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_arg_714_);
v___x_745_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_744_, v___f_743_);
return v___x_745_;
}
}
else
{
lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v___x_732_);
lean_dec(v_toTopVar_689_);
lean_inc_n(v_toBind_699_, 2);
lean_inc(v_asVar_698_);
lean_inc(v_toVar_697_);
lean_inc_ref_n(v_inst_696_, 2);
lean_inc_ref_n(v_inst_695_, 2);
lean_inc_ref_n(v_inst_694_, 2);
lean_inc_ref_n(v_inst_693_, 2);
lean_inc_n(v_inst_692_, 2);
v___f_746_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13), 11, 10);
lean_closure_set(v___f_746_, 0, v_toPure_691_);
lean_closure_set(v___f_746_, 1, v_inst_692_);
lean_closure_set(v___f_746_, 2, v_inst_693_);
lean_closure_set(v___f_746_, 3, v_inst_694_);
lean_closure_set(v___f_746_, 4, v_inst_695_);
lean_closure_set(v___f_746_, 5, v_inst_696_);
lean_closure_set(v___f_746_, 6, v_toVar_697_);
lean_closure_set(v___f_746_, 7, v_asVar_698_);
lean_closure_set(v___f_746_, 8, v_arg_706_);
lean_closure_set(v___f_746_, 9, v_toBind_699_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_747_, 0, v_asTopVar_700_);
lean_closure_set(v___f_747_, 1, v_e_690_);
lean_closure_set(v___f_747_, 2, v_inst_692_);
lean_closure_set(v___f_747_, 3, v_inst_693_);
lean_closure_set(v___f_747_, 4, v_inst_694_);
lean_closure_set(v___f_747_, 5, v_inst_695_);
lean_closure_set(v___f_747_, 6, v_inst_696_);
lean_closure_set(v___f_747_, 7, v_toVar_697_);
lean_closure_set(v___f_747_, 8, v_asVar_698_);
lean_closure_set(v___f_747_, 9, v_arg_710_);
lean_closure_set(v___f_747_, 10, v_toBind_699_);
lean_closure_set(v___f_747_, 11, v___f_746_);
v___x_748_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_692_, v_inst_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_arg_714_);
v___x_749_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_748_, v___f_747_);
return v___x_749_;
}
}
else
{
lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec_ref(v___x_732_);
lean_dec(v_toTopVar_689_);
lean_inc_n(v_toBind_699_, 2);
lean_inc(v_asVar_698_);
lean_inc(v_toVar_697_);
lean_inc_ref_n(v_inst_696_, 2);
lean_inc_ref_n(v_inst_695_, 2);
lean_inc_ref_n(v_inst_694_, 2);
lean_inc_ref_n(v_inst_693_, 2);
lean_inc_n(v_inst_692_, 2);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14), 11, 10);
lean_closure_set(v___f_750_, 0, v_toPure_691_);
lean_closure_set(v___f_750_, 1, v_inst_692_);
lean_closure_set(v___f_750_, 2, v_inst_693_);
lean_closure_set(v___f_750_, 3, v_inst_694_);
lean_closure_set(v___f_750_, 4, v_inst_695_);
lean_closure_set(v___f_750_, 5, v_inst_696_);
lean_closure_set(v___f_750_, 6, v_toVar_697_);
lean_closure_set(v___f_750_, 7, v_asVar_698_);
lean_closure_set(v___f_750_, 8, v_arg_706_);
lean_closure_set(v___f_750_, 9, v_toBind_699_);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_751_, 0, v_asTopVar_700_);
lean_closure_set(v___f_751_, 1, v_e_690_);
lean_closure_set(v___f_751_, 2, v_inst_692_);
lean_closure_set(v___f_751_, 3, v_inst_693_);
lean_closure_set(v___f_751_, 4, v_inst_694_);
lean_closure_set(v___f_751_, 5, v_inst_695_);
lean_closure_set(v___f_751_, 6, v_inst_696_);
lean_closure_set(v___f_751_, 7, v_toVar_697_);
lean_closure_set(v___f_751_, 8, v_asVar_698_);
lean_closure_set(v___f_751_, 9, v_arg_710_);
lean_closure_set(v___f_751_, 10, v_toBind_699_);
lean_closure_set(v___f_751_, 11, v___f_750_);
v___x_752_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_692_, v_inst_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_arg_714_);
v___x_753_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_752_, v___f_751_);
return v___x_753_;
}
}
else
{
lean_object* v___x_754_; 
lean_dec_ref(v___x_732_);
lean_dec(v_toTopVar_689_);
v___x_754_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_706_);
if (lean_obj_tag(v___x_754_) == 1)
{
lean_object* v_val_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_val_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref(v___x_754_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17), 3, 2);
lean_closure_set(v___f_756_, 0, v_val_755_);
lean_closure_set(v___f_756_, 1, v_toPure_691_);
lean_inc(v_toBind_699_);
lean_inc_ref(v_inst_696_);
lean_inc_ref(v_inst_695_);
lean_inc_ref(v_inst_694_);
lean_inc_ref(v_inst_693_);
lean_inc(v_inst_692_);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_757_, 0, v_asTopVar_700_);
lean_closure_set(v___f_757_, 1, v_e_690_);
lean_closure_set(v___f_757_, 2, v_inst_692_);
lean_closure_set(v___f_757_, 3, v_inst_693_);
lean_closure_set(v___f_757_, 4, v_inst_694_);
lean_closure_set(v___f_757_, 5, v_inst_695_);
lean_closure_set(v___f_757_, 6, v_inst_696_);
lean_closure_set(v___f_757_, 7, v_toVar_697_);
lean_closure_set(v___f_757_, 8, v_asVar_698_);
lean_closure_set(v___f_757_, 9, v_arg_710_);
lean_closure_set(v___f_757_, 10, v_toBind_699_);
lean_closure_set(v___f_757_, 11, v___f_756_);
v___x_758_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_692_, v_inst_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_arg_714_);
v___x_759_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_758_, v___f_757_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; 
lean_dec(v___x_754_);
lean_dec_ref(v_arg_714_);
lean_dec_ref(v_arg_710_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toPure_691_);
v___x_760_ = lean_apply_1(v_asTopVar_700_, v_e_690_);
return v___x_760_;
}
}
}
}
}
}
else
{
lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec_ref(v___x_715_);
lean_dec_ref(v_arg_714_);
lean_dec(v_toPure_691_);
lean_dec(v_toTopVar_689_);
lean_inc(v_toBind_699_);
lean_inc_ref(v_inst_696_);
lean_inc_ref(v_inst_695_);
lean_inc_ref(v_inst_694_);
lean_inc_ref(v_inst_693_);
lean_inc(v_inst_692_);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_761_, 0, v_asTopVar_700_);
lean_closure_set(v___f_761_, 1, v_e_690_);
lean_closure_set(v___f_761_, 2, v_inst_692_);
lean_closure_set(v___f_761_, 3, v_inst_693_);
lean_closure_set(v___f_761_, 4, v_inst_694_);
lean_closure_set(v___f_761_, 5, v_inst_695_);
lean_closure_set(v___f_761_, 6, v_inst_696_);
lean_closure_set(v___f_761_, 7, v_toVar_697_);
lean_closure_set(v___f_761_, 8, v_asVar_698_);
lean_closure_set(v___f_761_, 9, v_arg_706_);
lean_closure_set(v___f_761_, 10, v_toBind_699_);
lean_closure_set(v___f_761_, 11, v___f_701_);
v___x_762_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_692_, v_inst_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_arg_710_);
v___x_763_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_762_, v___f_761_);
return v___x_763_;
}
}
else
{
lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec_ref(v___x_715_);
lean_dec_ref(v_arg_714_);
lean_dec(v___f_701_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_693_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed), 6, 5);
lean_closure_set(v___f_764_, 0, v_asTopVar_700_);
lean_closure_set(v___f_764_, 1, v_e_690_);
lean_closure_set(v___f_764_, 2, v_arg_706_);
lean_closure_set(v___f_764_, 3, v_toPure_691_);
lean_closure_set(v___f_764_, 4, v_toTopVar_689_);
v___x_765_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_692_, v_inst_694_, v_inst_695_, v_inst_696_, v_arg_710_);
v___x_766_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_765_, v___f_764_);
return v___x_766_;
}
}
else
{
lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec_ref(v___x_715_);
lean_dec_ref(v_arg_714_);
lean_dec(v___f_701_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_693_);
v___f_767_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed), 6, 5);
lean_closure_set(v___f_767_, 0, v_asTopVar_700_);
lean_closure_set(v___f_767_, 1, v_e_690_);
lean_closure_set(v___f_767_, 2, v_arg_706_);
lean_closure_set(v___f_767_, 3, v_toPure_691_);
lean_closure_set(v___f_767_, 4, v_toTopVar_689_);
v___x_768_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_692_, v_inst_694_, v_inst_695_, v_inst_696_, v_arg_710_);
v___x_769_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_768_, v___f_767_);
return v___x_769_;
}
}
else
{
lean_dec_ref(v___x_715_);
lean_dec_ref(v_arg_714_);
lean_dec_ref(v_arg_706_);
lean_dec(v___f_701_);
lean_dec(v_toBind_699_);
lean_dec(v_asVar_698_);
lean_dec(v_toVar_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
lean_dec(v_toTopVar_689_);
if (lean_obj_tag(v_arg_710_) == 9)
{
lean_object* v_a_770_; 
v_a_770_ = lean_ctor_get(v_arg_710_, 0);
lean_inc_ref(v_a_770_);
lean_dec_ref(v_arg_710_);
if (lean_obj_tag(v_a_770_) == 0)
{
lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_asTopVar_700_);
lean_dec_ref(v_e_690_);
v_val_771_ = lean_ctor_get(v_a_770_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_a_770_);
if (v_isSharedCheck_781_ == 0)
{
v___x_773_ = v_a_770_;
v_isShared_774_ = v_isSharedCheck_781_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_dec(v_a_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_781_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = lean_nat_to_int(v_val_771_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_780_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
v___x_779_ = lean_apply_2(v_toPure_691_, lean_box(0), v___x_778_);
return v___x_779_;
}
}
}
else
{
lean_object* v___x_782_; 
lean_dec_ref(v_a_770_);
lean_dec(v_toPure_691_);
v___x_782_ = lean_apply_1(v_asTopVar_700_, v_e_690_);
return v___x_782_;
}
}
else
{
lean_object* v___x_783_; 
lean_dec_ref(v_arg_710_);
lean_dec(v_toPure_691_);
v___x_783_ = lean_apply_1(v_asTopVar_700_, v_e_690_);
return v___x_783_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_e_791_, uint8_t v_skipVar_792_){
_start:
{
lean_object* v_toApplicative_793_; lean_object* v_toBind_794_; lean_object* v_toPure_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v_asVar_799_; lean_object* v_toVar_800_; lean_object* v___x_801_; lean_object* v_toTopVar_802_; lean_object* v_asTopVar_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_toApplicative_793_ = lean_ctor_get(v_inst_787_, 0);
v_toBind_794_ = lean_ctor_get(v_inst_787_, 1);
lean_inc_n(v_toBind_794_, 6);
v_toPure_795_ = lean_ctor_get(v_toApplicative_793_, 1);
lean_inc_n(v_toPure_795_, 5);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_796_, 0, v_toPure_795_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_797_, 0, v_toPure_795_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_798_, 0, v_toPure_795_);
lean_inc(v_inst_784_);
lean_inc_ref(v___f_798_);
lean_inc(v_inst_790_);
v_asVar_799_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4), 5, 4);
lean_closure_set(v_asVar_799_, 0, v_inst_790_);
lean_closure_set(v_asVar_799_, 1, v_toBind_794_);
lean_closure_set(v_asVar_799_, 2, v___f_798_);
lean_closure_set(v_asVar_799_, 3, v_inst_784_);
v_toVar_800_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6), 4, 3);
lean_closure_set(v_toVar_800_, 0, v_inst_790_);
lean_closure_set(v_toVar_800_, 1, v_toBind_794_);
lean_closure_set(v_toVar_800_, 2, v___f_798_);
v___x_801_ = lean_box(v_skipVar_792_);
lean_inc_ref(v_toVar_800_);
v_toTopVar_802_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v_toTopVar_802_, 0, v___x_801_);
lean_closure_set(v_toTopVar_802_, 1, v_toVar_800_);
lean_closure_set(v_toTopVar_802_, 2, v_toBind_794_);
lean_closure_set(v_toTopVar_802_, 3, v___f_797_);
lean_closure_set(v_toTopVar_802_, 4, v_toPure_795_);
lean_inc_ref(v_toTopVar_802_);
v_asTopVar_803_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8), 4, 3);
lean_closure_set(v_asTopVar_803_, 0, v_toTopVar_802_);
lean_closure_set(v_asTopVar_803_, 1, v_inst_784_);
lean_closure_set(v_asTopVar_803_, 2, v_toBind_794_);
lean_inc(v_inst_785_);
lean_inc_ref(v_e_791_);
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18), 14, 13);
lean_closure_set(v___f_804_, 0, v_toTopVar_802_);
lean_closure_set(v___f_804_, 1, v_e_791_);
lean_closure_set(v___f_804_, 2, v_toPure_795_);
lean_closure_set(v___f_804_, 3, v_inst_785_);
lean_closure_set(v___f_804_, 4, v_inst_786_);
lean_closure_set(v___f_804_, 5, v_inst_787_);
lean_closure_set(v___f_804_, 6, v_inst_788_);
lean_closure_set(v___f_804_, 7, v_inst_789_);
lean_closure_set(v___f_804_, 8, v_toVar_800_);
lean_closure_set(v___f_804_, 9, v_asVar_799_);
lean_closure_set(v___f_804_, 10, v_toBind_794_);
lean_closure_set(v___f_804_, 11, v_asTopVar_803_);
lean_closure_set(v___f_804_, 12, v___f_796_);
v___x_805_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_805_, 0, v_e_791_);
v___x_806_ = lean_apply_2(v_inst_785_, lean_box(0), v___x_805_);
v___x_807_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_806_, v___f_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___boxed(lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_e_815_, lean_object* v_skipVar_816_){
_start:
{
uint8_t v_skipVar_boxed_817_; lean_object* v_res_818_; 
v_skipVar_boxed_817_ = lean_unbox(v_skipVar_816_);
v_res_818_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_808_, v_inst_809_, v_inst_810_, v_inst_811_, v_inst_812_, v_inst_813_, v_inst_814_, v_e_815_, v_skipVar_boxed_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f(lean_object* v_m_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_e_827_, uint8_t v_skipVar_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_820_, v_inst_821_, v_inst_822_, v_inst_823_, v_inst_824_, v_inst_825_, v_inst_826_, v_e_827_, v_skipVar_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___boxed(lean_object* v_m_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_e_838_, lean_object* v_skipVar_839_){
_start:
{
uint8_t v_skipVar_boxed_840_; lean_object* v_res_841_; 
v_skipVar_boxed_840_ = lean_unbox(v_skipVar_839_);
v_res_841_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f(v_m_830_, v_inst_831_, v_inst_832_, v_inst_833_, v_inst_834_, v_inst_835_, v_inst_836_, v_inst_837_, v_e_838_, v_skipVar_boxed_840_);
return v_res_841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(lean_object* v_inst_845_, lean_object* v_e_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_847_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1, &l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1);
v___x_848_ = l_Lean_indentExpr(v_e_846_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_reportIssueIfVerbose___boxed), 8, 1);
lean_closure_set(v___x_850_, 0, v___x_849_);
v___x_851_ = lean_apply_2(v_inst_845_, lean_box(0), v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue(lean_object* v_m_852_, lean_object* v_inst_853_, lean_object* v_e_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_853_, v_e_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(lean_object* v_arg_856_, lean_object* v_asVar_857_, lean_object* v_e_858_, lean_object* v_arg_859_, lean_object* v_toPure_860_, lean_object* v_toVar_861_, lean_object* v_____do__lift_862_){
_start:
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = l_Lean_Expr_appArg_x21(v_____do__lift_862_);
v___x_864_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_863_, v_arg_856_);
lean_dec_ref(v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec(v_toVar_861_);
lean_dec(v_toPure_860_);
lean_dec_ref(v_arg_859_);
v___x_865_ = lean_apply_1(v_asVar_857_, v_e_858_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; 
lean_dec(v_asVar_857_);
v___x_866_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_859_);
if (lean_obj_tag(v___x_866_) == 1)
{
lean_object* v_val_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_toVar_861_);
lean_dec_ref(v_e_858_);
v_val_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_876_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_876_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_val_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_876_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_nat_to_int(v_val_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 0);
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_875_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; 
v___x_874_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_873_);
return v___x_874_;
}
}
}
else
{
lean_object* v___x_877_; 
lean_dec(v___x_866_);
lean_dec(v_toPure_860_);
v___x_877_ = lean_apply_1(v_toVar_861_, v_e_858_);
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed(lean_object* v_arg_878_, lean_object* v_asVar_879_, lean_object* v_e_880_, lean_object* v_arg_881_, lean_object* v_toPure_882_, lean_object* v_toVar_883_, lean_object* v_____do__lift_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(v_arg_878_, v_asVar_879_, v_e_880_, v_arg_881_, v_toPure_882_, v_toVar_883_, v_____do__lift_884_);
lean_dec_ref(v_____do__lift_884_);
lean_dec_ref(v_arg_878_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(lean_object* v_arg_886_, lean_object* v_asVar_887_, lean_object* v_e_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_toVar_894_, lean_object* v_arg_895_, lean_object* v_toBind_896_, lean_object* v___f_897_, lean_object* v_____do__lift_898_){
_start:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = l_Lean_Expr_appArg_x21(v_____do__lift_898_);
v___x_900_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_899_, v_arg_886_);
lean_dec_ref(v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v___f_897_);
lean_dec(v_toBind_896_);
lean_dec_ref(v_arg_895_);
lean_dec(v_toVar_894_);
lean_dec_ref(v_inst_893_);
lean_dec_ref(v_inst_892_);
lean_dec_ref(v_inst_891_);
lean_dec_ref(v_inst_890_);
lean_dec(v_inst_889_);
v___x_901_ = lean_apply_1(v_asVar_887_, v_e_888_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec_ref(v_e_888_);
v___x_902_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_889_, v_inst_890_, v_inst_891_, v_inst_892_, v_inst_893_, v_toVar_894_, v_asVar_887_, v_arg_895_);
v___x_903_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_902_, v___f_897_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed(lean_object* v_arg_904_, lean_object* v_asVar_905_, lean_object* v_e_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_toVar_912_, lean_object* v_arg_913_, lean_object* v_toBind_914_, lean_object* v___f_915_, lean_object* v_____do__lift_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(v_arg_904_, v_asVar_905_, v_e_906_, v_inst_907_, v_inst_908_, v_inst_909_, v_inst_910_, v_inst_911_, v_toVar_912_, v_arg_913_, v_toBind_914_, v___f_915_, v_____do__lift_916_);
lean_dec_ref(v_____do__lift_916_);
lean_dec_ref(v_arg_904_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3(lean_object* v_toPure_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_toVar_924_, lean_object* v_asVar_925_, lean_object* v_arg_926_, lean_object* v_toBind_927_, lean_object* v_____do__lift_928_){
_start:
{
lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___f_929_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_929_, 0, v_____do__lift_928_);
lean_closure_set(v___f_929_, 1, v_toPure_918_);
v___x_930_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_919_, v_inst_920_, v_inst_921_, v_inst_922_, v_inst_923_, v_toVar_924_, v_asVar_925_, v_arg_926_);
v___x_931_ = lean_apply_4(v_toBind_927_, lean_box(0), lean_box(0), v___x_930_, v___f_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2(lean_object* v_toVar_932_, lean_object* v_e_933_, lean_object* v_toPure_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_asVar_940_, lean_object* v_toBind_941_, lean_object* v_____x_942_){
_start:
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = l_Lean_Expr_cleanupAnnotations(v_____x_942_);
v___x_944_ = l_Lean_Expr_isApp(v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
lean_dec_ref(v___x_943_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
lean_dec(v_toPure_934_);
v___x_945_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_945_;
}
else
{
lean_object* v_arg_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_arg_946_ = lean_ctor_get(v___x_943_, 1);
lean_inc_ref(v_arg_946_);
v___x_947_ = l_Lean_Expr_appFnCleanup___redArg(v___x_943_);
v___x_948_ = l_Lean_Expr_isApp(v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v___x_947_);
lean_dec_ref(v_arg_946_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
lean_dec(v_toPure_934_);
v___x_949_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_949_;
}
else
{
lean_object* v_arg_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_arg_950_ = lean_ctor_get(v___x_947_, 1);
lean_inc_ref(v_arg_950_);
v___x_951_ = l_Lean_Expr_appFnCleanup___redArg(v___x_947_);
v___x_952_ = l_Lean_Expr_isApp(v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec_ref(v___x_951_);
lean_dec_ref(v_arg_950_);
lean_dec_ref(v_arg_946_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
lean_dec(v_toPure_934_);
v___x_953_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_953_;
}
else
{
lean_object* v_arg_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_arg_954_ = lean_ctor_get(v___x_951_, 1);
lean_inc_ref(v_arg_954_);
v___x_955_ = l_Lean_Expr_appFnCleanup___redArg(v___x_951_);
v___x_956_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_957_ = l_Lean_Expr_isConstOf(v___x_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_959_ = l_Lean_Expr_isConstOf(v___x_955_, v___x_958_);
if (v___x_959_ == 0)
{
uint8_t v___x_960_; 
v___x_960_ = l_Lean_Expr_isApp(v___x_955_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
lean_dec_ref(v___x_955_);
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_arg_950_);
lean_dec_ref(v_arg_946_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
lean_dec(v_toPure_934_);
v___x_961_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = l_Lean_Expr_appFnCleanup___redArg(v___x_955_);
v___x_963_ = l_Lean_Expr_isApp(v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec_ref(v___x_962_);
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_arg_950_);
lean_dec_ref(v_arg_946_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
lean_dec(v_toPure_934_);
v___x_964_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_962_);
v___x_966_ = l_Lean_Expr_isApp(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec_ref(v___x_965_);
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_arg_950_);
lean_dec_ref(v_arg_946_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
lean_dec(v_toPure_934_);
v___x_967_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_965_);
v___x_969_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_970_ = l_Lean_Expr_isConstOf(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_972_ = l_Lean_Expr_isConstOf(v___x_968_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_974_ = l_Lean_Expr_isConstOf(v___x_968_, v___x_973_);
lean_dec_ref(v___x_968_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_arg_950_);
lean_dec_ref(v_arg_946_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
lean_dec(v_toPure_934_);
v___x_975_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_975_;
}
else
{
lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_inc_n(v_toBind_941_, 2);
lean_inc(v_asVar_940_);
lean_inc(v_toVar_932_);
lean_inc_ref_n(v_inst_939_, 2);
lean_inc_ref_n(v_inst_938_, 2);
lean_inc_ref_n(v_inst_937_, 2);
lean_inc_ref_n(v_inst_936_, 2);
lean_inc_n(v_inst_935_, 2);
v___f_976_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_976_, 0, v_toPure_934_);
lean_closure_set(v___f_976_, 1, v_inst_935_);
lean_closure_set(v___f_976_, 2, v_inst_936_);
lean_closure_set(v___f_976_, 3, v_inst_937_);
lean_closure_set(v___f_976_, 4, v_inst_938_);
lean_closure_set(v___f_976_, 5, v_inst_939_);
lean_closure_set(v___f_976_, 6, v_toVar_932_);
lean_closure_set(v___f_976_, 7, v_asVar_940_);
lean_closure_set(v___f_976_, 8, v_arg_946_);
lean_closure_set(v___f_976_, 9, v_toBind_941_);
v___f_977_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_977_, 0, v_arg_954_);
lean_closure_set(v___f_977_, 1, v_asVar_940_);
lean_closure_set(v___f_977_, 2, v_e_933_);
lean_closure_set(v___f_977_, 3, v_inst_935_);
lean_closure_set(v___f_977_, 4, v_inst_936_);
lean_closure_set(v___f_977_, 5, v_inst_937_);
lean_closure_set(v___f_977_, 6, v_inst_938_);
lean_closure_set(v___f_977_, 7, v_inst_939_);
lean_closure_set(v___f_977_, 8, v_toVar_932_);
lean_closure_set(v___f_977_, 9, v_arg_950_);
lean_closure_set(v___f_977_, 10, v_toBind_941_);
lean_closure_set(v___f_977_, 11, v___f_976_);
v___x_978_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_935_, v_inst_936_, v_inst_937_, v_inst_938_, v_inst_939_);
v___x_979_ = lean_apply_4(v_toBind_941_, lean_box(0), lean_box(0), v___x_978_, v___f_977_);
return v___x_979_;
}
}
else
{
lean_object* v___f_980_; lean_object* v___f_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec_ref(v___x_968_);
lean_inc_n(v_toBind_941_, 2);
lean_inc(v_asVar_940_);
lean_inc(v_toVar_932_);
lean_inc_ref_n(v_inst_939_, 2);
lean_inc_ref_n(v_inst_938_, 2);
lean_inc_ref_n(v_inst_937_, 2);
lean_inc_ref_n(v_inst_936_, 2);
lean_inc_n(v_inst_935_, 2);
v___f_980_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3), 11, 10);
lean_closure_set(v___f_980_, 0, v_toPure_934_);
lean_closure_set(v___f_980_, 1, v_inst_935_);
lean_closure_set(v___f_980_, 2, v_inst_936_);
lean_closure_set(v___f_980_, 3, v_inst_937_);
lean_closure_set(v___f_980_, 4, v_inst_938_);
lean_closure_set(v___f_980_, 5, v_inst_939_);
lean_closure_set(v___f_980_, 6, v_toVar_932_);
lean_closure_set(v___f_980_, 7, v_asVar_940_);
lean_closure_set(v___f_980_, 8, v_arg_946_);
lean_closure_set(v___f_980_, 9, v_toBind_941_);
v___f_981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_981_, 0, v_arg_954_);
lean_closure_set(v___f_981_, 1, v_asVar_940_);
lean_closure_set(v___f_981_, 2, v_e_933_);
lean_closure_set(v___f_981_, 3, v_inst_935_);
lean_closure_set(v___f_981_, 4, v_inst_936_);
lean_closure_set(v___f_981_, 5, v_inst_937_);
lean_closure_set(v___f_981_, 6, v_inst_938_);
lean_closure_set(v___f_981_, 7, v_inst_939_);
lean_closure_set(v___f_981_, 8, v_toVar_932_);
lean_closure_set(v___f_981_, 9, v_arg_950_);
lean_closure_set(v___f_981_, 10, v_toBind_941_);
lean_closure_set(v___f_981_, 11, v___f_980_);
v___x_982_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_935_, v_inst_936_, v_inst_937_, v_inst_938_, v_inst_939_);
v___x_983_ = lean_apply_4(v_toBind_941_, lean_box(0), lean_box(0), v___x_982_, v___f_981_);
return v___x_983_;
}
}
else
{
lean_object* v___x_984_; 
lean_dec_ref(v___x_968_);
v___x_984_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_946_);
if (lean_obj_tag(v___x_984_) == 1)
{
lean_object* v_val_985_; lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_val_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_985_);
lean_dec_ref(v___x_984_);
v___f_986_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9), 3, 2);
lean_closure_set(v___f_986_, 0, v_val_985_);
lean_closure_set(v___f_986_, 1, v_toPure_934_);
lean_inc(v_toBind_941_);
lean_inc_ref(v_inst_939_);
lean_inc_ref(v_inst_938_);
lean_inc_ref(v_inst_937_);
lean_inc_ref(v_inst_936_);
lean_inc(v_inst_935_);
v___f_987_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_987_, 0, v_arg_954_);
lean_closure_set(v___f_987_, 1, v_asVar_940_);
lean_closure_set(v___f_987_, 2, v_e_933_);
lean_closure_set(v___f_987_, 3, v_inst_935_);
lean_closure_set(v___f_987_, 4, v_inst_936_);
lean_closure_set(v___f_987_, 5, v_inst_937_);
lean_closure_set(v___f_987_, 6, v_inst_938_);
lean_closure_set(v___f_987_, 7, v_inst_939_);
lean_closure_set(v___f_987_, 8, v_toVar_932_);
lean_closure_set(v___f_987_, 9, v_arg_950_);
lean_closure_set(v___f_987_, 10, v_toBind_941_);
lean_closure_set(v___f_987_, 11, v___f_986_);
v___x_988_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_935_, v_inst_936_, v_inst_937_, v_inst_938_, v_inst_939_);
v___x_989_ = lean_apply_4(v_toBind_941_, lean_box(0), lean_box(0), v___x_988_, v___f_987_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; 
lean_dec(v___x_984_);
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_arg_950_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
lean_dec(v_toPure_934_);
v___x_990_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_990_;
}
}
}
}
}
}
else
{
lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec_ref(v___x_955_);
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_inst_936_);
v___f_991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_991_, 0, v_arg_950_);
lean_closure_set(v___f_991_, 1, v_asVar_940_);
lean_closure_set(v___f_991_, 2, v_e_933_);
lean_closure_set(v___f_991_, 3, v_arg_946_);
lean_closure_set(v___f_991_, 4, v_toPure_934_);
lean_closure_set(v___f_991_, 5, v_toVar_932_);
v___x_992_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_935_, v_inst_937_, v_inst_938_, v_inst_939_);
v___x_993_ = lean_apply_4(v_toBind_941_, lean_box(0), lean_box(0), v___x_992_, v___f_991_);
return v___x_993_;
}
}
else
{
lean_dec_ref(v___x_955_);
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_arg_946_);
lean_dec(v_toBind_941_);
lean_dec(v_asVar_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
if (lean_obj_tag(v_arg_950_) == 9)
{
lean_object* v_a_994_; 
v_a_994_ = lean_ctor_get(v_arg_950_, 0);
lean_inc_ref(v_a_994_);
lean_dec_ref(v_arg_950_);
if (lean_obj_tag(v_a_994_) == 0)
{
lean_object* v_val_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref(v_e_933_);
lean_dec(v_toVar_932_);
v_val_995_ = lean_ctor_get(v_a_994_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_994_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_997_ = v_a_994_;
v_isShared_998_ = v_isSharedCheck_1004_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_val_995_);
lean_dec(v_a_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1004_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_nat_to_int(v_val_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_apply_2(v_toPure_934_, lean_box(0), v___x_1001_);
return v___x_1002_;
}
}
}
else
{
lean_object* v___x_1005_; 
lean_dec_ref(v_a_994_);
lean_dec(v_toPure_934_);
v___x_1005_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_1005_;
}
}
else
{
lean_object* v___x_1006_; 
lean_dec_ref(v_arg_950_);
lean_dec(v_toPure_934_);
v___x_1006_ = lean_apply_1(v_toVar_932_, v_e_933_);
return v___x_1006_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_toVar_1012_, lean_object* v_asVar_1013_, lean_object* v_e_1014_){
_start:
{
lean_object* v_toApplicative_1015_; lean_object* v_toBind_1016_; lean_object* v_toPure_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; 
v_toApplicative_1015_ = lean_ctor_get(v_inst_1009_, 0);
v_toBind_1016_ = lean_ctor_get(v_inst_1009_, 1);
lean_inc_n(v_toBind_1016_, 2);
v_toPure_1017_ = lean_ctor_get(v_toApplicative_1015_, 1);
lean_inc(v_toPure_1017_);
lean_inc_ref(v_e_1014_);
v___x_1018_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_1018_, 0, v_e_1014_);
lean_inc(v_inst_1007_);
v___x_1019_ = lean_apply_2(v_inst_1007_, lean_box(0), v___x_1018_);
v___f_1020_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1020_, 0, v_toVar_1012_);
lean_closure_set(v___f_1020_, 1, v_e_1014_);
lean_closure_set(v___f_1020_, 2, v_toPure_1017_);
lean_closure_set(v___f_1020_, 3, v_inst_1007_);
lean_closure_set(v___f_1020_, 4, v_inst_1008_);
lean_closure_set(v___f_1020_, 5, v_inst_1009_);
lean_closure_set(v___f_1020_, 6, v_inst_1010_);
lean_closure_set(v___f_1020_, 7, v_inst_1011_);
lean_closure_set(v___f_1020_, 8, v_asVar_1013_);
lean_closure_set(v___f_1020_, 9, v_toBind_1016_);
v___x_1021_ = lean_apply_4(v_toBind_1016_, lean_box(0), lean_box(0), v___x_1019_, v___f_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1(lean_object* v_toPure_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_toVar_1028_, lean_object* v_asVar_1029_, lean_object* v_arg_1030_, lean_object* v_toBind_1031_, lean_object* v_____do__lift_1032_){
_start:
{
lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___f_1033_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1033_, 0, v_____do__lift_1032_);
lean_closure_set(v___f_1033_, 1, v_toPure_1022_);
v___x_1034_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1023_, v_inst_1024_, v_inst_1025_, v_inst_1026_, v_inst_1027_, v_toVar_1028_, v_asVar_1029_, v_arg_1030_);
v___x_1035_ = lean_apply_4(v_toBind_1031_, lean_box(0), lean_box(0), v___x_1034_, v___f_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go(lean_object* v_m_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_toVar_1042_, lean_object* v_asVar_1043_, lean_object* v_e_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1037_, v_inst_1038_, v_inst_1039_, v_inst_1040_, v_inst_1041_, v_toVar_1042_, v_asVar_1043_, v_e_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3(lean_object* v_inst_1046_, lean_object* v_toBind_1047_, lean_object* v___f_1048_, lean_object* v_inst_1049_, lean_object* v_e_1050_){
_start:
{
lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_inc(v_toBind_1047_);
lean_inc_ref(v_e_1050_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1051_, 0, v_inst_1046_);
lean_closure_set(v___f_1051_, 1, v_e_1050_);
lean_closure_set(v___f_1051_, 2, v_toBind_1047_);
lean_closure_set(v___f_1051_, 3, v___f_1048_);
v___x_1052_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_1049_, v_e_1050_);
v___x_1053_ = lean_apply_4(v_toBind_1047_, lean_box(0), lean_box(0), v___x_1052_, v___f_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2(lean_object* v_toVar_1054_, lean_object* v_toBind_1055_, lean_object* v___f_1056_, lean_object* v_e_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_apply_1(v_toVar_1054_, v_e_1057_);
v___x_1059_ = lean_apply_4(v_toBind_1055_, lean_box(0), lean_box(0), v___x_1058_, v___f_1056_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1(lean_object* v_toTopVar_1060_, lean_object* v_inst_1061_, lean_object* v_toBind_1062_, lean_object* v_e_1063_){
_start:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_inc_ref(v_e_1063_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1064_, 0, v_toTopVar_1060_);
lean_closure_set(v___f_1064_, 1, v_e_1063_);
v___x_1065_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_1061_, v_e_1063_);
v___x_1066_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v___x_1065_, v___f_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4(lean_object* v_toPure_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_toVar_1073_, lean_object* v_asVar_1074_, lean_object* v_arg_1075_, lean_object* v_toBind_1076_, lean_object* v_____do__lift_1077_){
_start:
{
lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9), 3, 2);
lean_closure_set(v___f_1078_, 0, v_____do__lift_1077_);
lean_closure_set(v___f_1078_, 1, v_toPure_1067_);
v___x_1079_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1068_, v_inst_1069_, v_inst_1070_, v_inst_1071_, v_inst_1072_, v_toVar_1073_, v_asVar_1074_, v_arg_1075_);
v___x_1080_ = lean_apply_4(v_toBind_1076_, lean_box(0), lean_box(0), v___x_1079_, v___f_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(lean_object* v_arg_1081_, lean_object* v_asTopVar_1082_, lean_object* v_e_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_toVar_1089_, lean_object* v_asVar_1090_, lean_object* v_arg_1091_, lean_object* v_toBind_1092_, lean_object* v___f_1093_, lean_object* v_____do__lift_1094_){
_start:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = l_Lean_Expr_appArg_x21(v_____do__lift_1094_);
v___x_1096_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1095_, v_arg_1081_);
lean_dec_ref(v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v___f_1093_);
lean_dec(v_toBind_1092_);
lean_dec_ref(v_arg_1091_);
lean_dec(v_asVar_1090_);
lean_dec(v_toVar_1089_);
lean_dec_ref(v_inst_1088_);
lean_dec_ref(v_inst_1087_);
lean_dec_ref(v_inst_1086_);
lean_dec_ref(v_inst_1085_);
lean_dec(v_inst_1084_);
v___x_1097_ = lean_apply_1(v_asTopVar_1082_, v_e_1083_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v_e_1083_);
lean_dec(v_asTopVar_1082_);
v___x_1098_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1084_, v_inst_1085_, v_inst_1086_, v_inst_1087_, v_inst_1088_, v_toVar_1089_, v_asVar_1090_, v_arg_1091_);
v___x_1099_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v___x_1098_, v___f_1093_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed(lean_object* v_arg_1100_, lean_object* v_asTopVar_1101_, lean_object* v_e_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_toVar_1108_, lean_object* v_asVar_1109_, lean_object* v_arg_1110_, lean_object* v_toBind_1111_, lean_object* v___f_1112_, lean_object* v_____do__lift_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(v_arg_1100_, v_asTopVar_1101_, v_e_1102_, v_inst_1103_, v_inst_1104_, v_inst_1105_, v_inst_1106_, v_inst_1107_, v_toVar_1108_, v_asVar_1109_, v_arg_1110_, v_toBind_1111_, v___f_1112_, v_____do__lift_1113_);
lean_dec_ref(v_____do__lift_1113_);
lean_dec_ref(v_arg_1100_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6(lean_object* v_toPure_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_toVar_1121_, lean_object* v_asVar_1122_, lean_object* v_arg_1123_, lean_object* v_toBind_1124_, lean_object* v_____do__lift_1125_){
_start:
{
lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12), 3, 2);
lean_closure_set(v___f_1126_, 0, v_____do__lift_1125_);
lean_closure_set(v___f_1126_, 1, v_toPure_1115_);
v___x_1127_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1116_, v_inst_1117_, v_inst_1118_, v_inst_1119_, v_inst_1120_, v_toVar_1121_, v_asVar_1122_, v_arg_1123_);
v___x_1128_ = lean_apply_4(v_toBind_1124_, lean_box(0), lean_box(0), v___x_1127_, v___f_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(lean_object* v_arg_1129_, lean_object* v_asTopVar_1130_, lean_object* v_e_1131_, lean_object* v_arg_1132_, lean_object* v_toPure_1133_, lean_object* v_toTopVar_1134_, lean_object* v_____do__lift_1135_){
_start:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = l_Lean_Expr_appArg_x21(v_____do__lift_1135_);
v___x_1137_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1136_, v_arg_1129_);
lean_dec_ref(v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec(v_toTopVar_1134_);
lean_dec(v_toPure_1133_);
lean_dec_ref(v_arg_1132_);
v___x_1138_ = lean_apply_1(v_asTopVar_1130_, v_e_1131_);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; 
lean_dec(v_asTopVar_1130_);
v___x_1139_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1132_);
if (lean_obj_tag(v___x_1139_) == 1)
{
lean_object* v_val_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_toTopVar_1134_);
lean_dec_ref(v_e_1131_);
v_val_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_val_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1144_ = lean_nat_to_int(v_val_1140_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1145_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_apply_2(v_toPure_1133_, lean_box(0), v___x_1147_);
return v___x_1148_;
}
}
}
else
{
lean_object* v___x_1151_; 
lean_dec(v___x_1139_);
lean_dec(v_toPure_1133_);
v___x_1151_ = lean_apply_1(v_toTopVar_1134_, v_e_1131_);
return v___x_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed(lean_object* v_arg_1152_, lean_object* v_asTopVar_1153_, lean_object* v_e_1154_, lean_object* v_arg_1155_, lean_object* v_toPure_1156_, lean_object* v_toTopVar_1157_, lean_object* v_____do__lift_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(v_arg_1152_, v_asTopVar_1153_, v_e_1154_, v_arg_1155_, v_toPure_1156_, v_toTopVar_1157_, v_____do__lift_1158_);
lean_dec_ref(v_____do__lift_1158_);
lean_dec_ref(v_arg_1152_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5(lean_object* v_toTopVar_1160_, lean_object* v_e_1161_, lean_object* v_toPure_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_toVar_1168_, lean_object* v_asVar_1169_, lean_object* v_toBind_1170_, lean_object* v_asTopVar_1171_, lean_object* v_____x_1172_){
_start:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = l_Lean_Expr_cleanupAnnotations(v_____x_1172_);
v___x_1174_ = l_Lean_Expr_isApp(v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_dec_ref(v___x_1173_);
lean_dec(v_asTopVar_1171_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec(v_toPure_1162_);
v___x_1175_ = lean_apply_1(v_toTopVar_1160_, v_e_1161_);
return v___x_1175_;
}
else
{
lean_object* v_arg_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_arg_1176_ = lean_ctor_get(v___x_1173_, 1);
lean_inc_ref(v_arg_1176_);
v___x_1177_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1173_);
v___x_1178_ = l_Lean_Expr_isApp(v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v___x_1177_);
lean_dec_ref(v_arg_1176_);
lean_dec(v_asTopVar_1171_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec(v_toPure_1162_);
v___x_1179_ = lean_apply_1(v_toTopVar_1160_, v_e_1161_);
return v___x_1179_;
}
else
{
lean_object* v_arg_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v_arg_1180_ = lean_ctor_get(v___x_1177_, 1);
lean_inc_ref(v_arg_1180_);
v___x_1181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1177_);
v___x_1182_ = l_Lean_Expr_isApp(v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec_ref(v___x_1181_);
lean_dec_ref(v_arg_1180_);
lean_dec_ref(v_arg_1176_);
lean_dec(v_asTopVar_1171_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec(v_toPure_1162_);
v___x_1183_ = lean_apply_1(v_toTopVar_1160_, v_e_1161_);
return v___x_1183_;
}
else
{
lean_object* v_arg_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_arg_1184_ = lean_ctor_get(v___x_1181_, 1);
lean_inc_ref(v_arg_1184_);
v___x_1185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1181_);
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_1187_ = l_Lean_Expr_isConstOf(v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_1189_ = l_Lean_Expr_isConstOf(v___x_1185_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Lean_Expr_isApp(v___x_1185_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v___x_1185_);
lean_dec_ref(v_arg_1184_);
lean_dec_ref(v_arg_1180_);
lean_dec_ref(v_arg_1176_);
lean_dec(v_asTopVar_1171_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec(v_toPure_1162_);
v___x_1191_ = lean_apply_1(v_toTopVar_1160_, v_e_1161_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1185_);
v___x_1193_ = l_Lean_Expr_isApp(v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec_ref(v___x_1192_);
lean_dec_ref(v_arg_1184_);
lean_dec_ref(v_arg_1180_);
lean_dec_ref(v_arg_1176_);
lean_dec(v_asTopVar_1171_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec(v_toPure_1162_);
v___x_1194_ = lean_apply_1(v_toTopVar_1160_, v_e_1161_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1192_);
v___x_1196_ = l_Lean_Expr_isApp(v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v___x_1195_);
lean_dec_ref(v_arg_1184_);
lean_dec_ref(v_arg_1180_);
lean_dec_ref(v_arg_1176_);
lean_dec(v_asTopVar_1171_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec(v_toPure_1162_);
v___x_1197_ = lean_apply_1(v_toTopVar_1160_, v_e_1161_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1198_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1195_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_1200_ = l_Lean_Expr_isConstOf(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_1202_ = l_Lean_Expr_isConstOf(v___x_1198_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_1204_ = l_Lean_Expr_isConstOf(v___x_1198_, v___x_1203_);
lean_dec_ref(v___x_1198_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
lean_dec_ref(v_arg_1184_);
lean_dec_ref(v_arg_1180_);
lean_dec_ref(v_arg_1176_);
lean_dec(v_asTopVar_1171_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec(v_toPure_1162_);
v___x_1205_ = lean_apply_1(v_toTopVar_1160_, v_e_1161_);
return v___x_1205_;
}
else
{
lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_toTopVar_1160_);
lean_inc_n(v_toBind_1170_, 2);
lean_inc(v_asVar_1169_);
lean_inc(v_toVar_1168_);
lean_inc_ref_n(v_inst_1167_, 2);
lean_inc_ref_n(v_inst_1166_, 2);
lean_inc_ref_n(v_inst_1165_, 2);
lean_inc_ref_n(v_inst_1164_, 2);
lean_inc_n(v_inst_1163_, 2);
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4), 11, 10);
lean_closure_set(v___f_1206_, 0, v_toPure_1162_);
lean_closure_set(v___f_1206_, 1, v_inst_1163_);
lean_closure_set(v___f_1206_, 2, v_inst_1164_);
lean_closure_set(v___f_1206_, 3, v_inst_1165_);
lean_closure_set(v___f_1206_, 4, v_inst_1166_);
lean_closure_set(v___f_1206_, 5, v_inst_1167_);
lean_closure_set(v___f_1206_, 6, v_toVar_1168_);
lean_closure_set(v___f_1206_, 7, v_asVar_1169_);
lean_closure_set(v___f_1206_, 8, v_arg_1176_);
lean_closure_set(v___f_1206_, 9, v_toBind_1170_);
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1207_, 0, v_arg_1184_);
lean_closure_set(v___f_1207_, 1, v_asTopVar_1171_);
lean_closure_set(v___f_1207_, 2, v_e_1161_);
lean_closure_set(v___f_1207_, 3, v_inst_1163_);
lean_closure_set(v___f_1207_, 4, v_inst_1164_);
lean_closure_set(v___f_1207_, 5, v_inst_1165_);
lean_closure_set(v___f_1207_, 6, v_inst_1166_);
lean_closure_set(v___f_1207_, 7, v_inst_1167_);
lean_closure_set(v___f_1207_, 8, v_toVar_1168_);
lean_closure_set(v___f_1207_, 9, v_asVar_1169_);
lean_closure_set(v___f_1207_, 10, v_arg_1180_);
lean_closure_set(v___f_1207_, 11, v_toBind_1170_);
lean_closure_set(v___f_1207_, 12, v___f_1206_);
v___x_1208_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_inst_1167_);
v___x_1209_ = lean_apply_4(v_toBind_1170_, lean_box(0), lean_box(0), v___x_1208_, v___f_1207_);
return v___x_1209_;
}
}
else
{
lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v___x_1198_);
lean_dec(v_toTopVar_1160_);
lean_inc_n(v_toBind_1170_, 2);
lean_inc(v_asVar_1169_);
lean_inc(v_toVar_1168_);
lean_inc_ref_n(v_inst_1167_, 2);
lean_inc_ref_n(v_inst_1166_, 2);
lean_inc_ref_n(v_inst_1165_, 2);
lean_inc_ref_n(v_inst_1164_, 2);
lean_inc_n(v_inst_1163_, 2);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6), 11, 10);
lean_closure_set(v___f_1210_, 0, v_toPure_1162_);
lean_closure_set(v___f_1210_, 1, v_inst_1163_);
lean_closure_set(v___f_1210_, 2, v_inst_1164_);
lean_closure_set(v___f_1210_, 3, v_inst_1165_);
lean_closure_set(v___f_1210_, 4, v_inst_1166_);
lean_closure_set(v___f_1210_, 5, v_inst_1167_);
lean_closure_set(v___f_1210_, 6, v_toVar_1168_);
lean_closure_set(v___f_1210_, 7, v_asVar_1169_);
lean_closure_set(v___f_1210_, 8, v_arg_1176_);
lean_closure_set(v___f_1210_, 9, v_toBind_1170_);
v___f_1211_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1211_, 0, v_arg_1184_);
lean_closure_set(v___f_1211_, 1, v_asTopVar_1171_);
lean_closure_set(v___f_1211_, 2, v_e_1161_);
lean_closure_set(v___f_1211_, 3, v_inst_1163_);
lean_closure_set(v___f_1211_, 4, v_inst_1164_);
lean_closure_set(v___f_1211_, 5, v_inst_1165_);
lean_closure_set(v___f_1211_, 6, v_inst_1166_);
lean_closure_set(v___f_1211_, 7, v_inst_1167_);
lean_closure_set(v___f_1211_, 8, v_toVar_1168_);
lean_closure_set(v___f_1211_, 9, v_asVar_1169_);
lean_closure_set(v___f_1211_, 10, v_arg_1180_);
lean_closure_set(v___f_1211_, 11, v_toBind_1170_);
lean_closure_set(v___f_1211_, 12, v___f_1210_);
v___x_1212_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_inst_1167_);
v___x_1213_ = lean_apply_4(v_toBind_1170_, lean_box(0), lean_box(0), v___x_1212_, v___f_1211_);
return v___x_1213_;
}
}
else
{
lean_object* v___x_1214_; 
lean_dec_ref(v___x_1198_);
lean_dec(v_toTopVar_1160_);
v___x_1214_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1176_);
if (lean_obj_tag(v___x_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref(v___x_1214_);
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17), 3, 2);
lean_closure_set(v___f_1216_, 0, v_val_1215_);
lean_closure_set(v___f_1216_, 1, v_toPure_1162_);
lean_inc(v_toBind_1170_);
lean_inc_ref(v_inst_1167_);
lean_inc_ref(v_inst_1166_);
lean_inc_ref(v_inst_1165_);
lean_inc_ref(v_inst_1164_);
lean_inc(v_inst_1163_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1217_, 0, v_arg_1184_);
lean_closure_set(v___f_1217_, 1, v_asTopVar_1171_);
lean_closure_set(v___f_1217_, 2, v_e_1161_);
lean_closure_set(v___f_1217_, 3, v_inst_1163_);
lean_closure_set(v___f_1217_, 4, v_inst_1164_);
lean_closure_set(v___f_1217_, 5, v_inst_1165_);
lean_closure_set(v___f_1217_, 6, v_inst_1166_);
lean_closure_set(v___f_1217_, 7, v_inst_1167_);
lean_closure_set(v___f_1217_, 8, v_toVar_1168_);
lean_closure_set(v___f_1217_, 9, v_asVar_1169_);
lean_closure_set(v___f_1217_, 10, v_arg_1180_);
lean_closure_set(v___f_1217_, 11, v_toBind_1170_);
lean_closure_set(v___f_1217_, 12, v___f_1216_);
v___x_1218_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_inst_1167_);
v___x_1219_ = lean_apply_4(v_toBind_1170_, lean_box(0), lean_box(0), v___x_1218_, v___f_1217_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec(v___x_1214_);
lean_dec_ref(v_arg_1184_);
lean_dec_ref(v_arg_1180_);
lean_dec(v_asTopVar_1171_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec_ref(v_e_1161_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_apply_2(v_toPure_1162_, lean_box(0), v___x_1220_);
return v___x_1221_;
}
}
}
}
}
}
else
{
lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v___x_1185_);
lean_dec_ref(v_arg_1184_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1164_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_1222_, 0, v_arg_1180_);
lean_closure_set(v___f_1222_, 1, v_asTopVar_1171_);
lean_closure_set(v___f_1222_, 2, v_e_1161_);
lean_closure_set(v___f_1222_, 3, v_arg_1176_);
lean_closure_set(v___f_1222_, 4, v_toPure_1162_);
lean_closure_set(v___f_1222_, 5, v_toTopVar_1160_);
v___x_1223_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1163_, v_inst_1165_, v_inst_1166_, v_inst_1167_);
v___x_1224_ = lean_apply_4(v_toBind_1170_, lean_box(0), lean_box(0), v___x_1223_, v___f_1222_);
return v___x_1224_;
}
}
else
{
lean_dec_ref(v___x_1185_);
lean_dec_ref(v_arg_1184_);
lean_dec_ref(v_arg_1176_);
lean_dec(v_toBind_1170_);
lean_dec(v_asVar_1169_);
lean_dec(v_toVar_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec(v_inst_1163_);
lean_dec(v_toTopVar_1160_);
if (lean_obj_tag(v_arg_1180_) == 9)
{
lean_object* v_a_1225_; 
v_a_1225_ = lean_ctor_get(v_arg_1180_, 0);
lean_inc_ref(v_a_1225_);
lean_dec_ref(v_arg_1180_);
if (lean_obj_tag(v_a_1225_) == 0)
{
lean_object* v_val_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_asTopVar_1171_);
lean_dec_ref(v_e_1161_);
v_val_1226_ = lean_ctor_get(v_a_1225_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_a_1225_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1228_ = v_a_1225_;
v_isShared_1229_ = v_isSharedCheck_1236_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_val_1226_);
lean_dec(v_a_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1236_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = lean_nat_to_int(v_val_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1230_);
v___x_1232_ = v___x_1228_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
v___x_1234_ = lean_apply_2(v_toPure_1162_, lean_box(0), v___x_1233_);
return v___x_1234_;
}
}
}
else
{
lean_object* v___x_1237_; 
lean_dec_ref(v_a_1225_);
lean_dec(v_toPure_1162_);
v___x_1237_ = lean_apply_1(v_asTopVar_1171_, v_e_1161_);
return v___x_1237_;
}
}
else
{
lean_object* v___x_1238_; 
lean_dec_ref(v_arg_1180_);
lean_dec(v_toPure_1162_);
v___x_1238_ = lean_apply_1(v_asTopVar_1171_, v_e_1161_);
return v___x_1238_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_e_1246_){
_start:
{
lean_object* v_toApplicative_1247_; lean_object* v_toBind_1248_; lean_object* v_toPure_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v_asVar_1252_; lean_object* v_toVar_1253_; lean_object* v_toTopVar_1254_; lean_object* v_asTopVar_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_toApplicative_1247_ = lean_ctor_get(v_inst_1242_, 0);
v_toBind_1248_ = lean_ctor_get(v_inst_1242_, 1);
lean_inc_n(v_toBind_1248_, 6);
v_toPure_1249_ = lean_ctor_get(v_toApplicative_1247_, 1);
lean_inc_n(v_toPure_1249_, 3);
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1250_, 0, v_toPure_1249_);
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1251_, 0, v_toPure_1249_);
lean_inc(v_inst_1239_);
lean_inc_ref(v___f_1251_);
lean_inc(v_inst_1245_);
v_asVar_1252_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v_asVar_1252_, 0, v_inst_1245_);
lean_closure_set(v_asVar_1252_, 1, v_toBind_1248_);
lean_closure_set(v_asVar_1252_, 2, v___f_1251_);
lean_closure_set(v_asVar_1252_, 3, v_inst_1239_);
v_toVar_1253_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6), 4, 3);
lean_closure_set(v_toVar_1253_, 0, v_inst_1245_);
lean_closure_set(v_toVar_1253_, 1, v_toBind_1248_);
lean_closure_set(v_toVar_1253_, 2, v___f_1251_);
lean_inc_ref(v_toVar_1253_);
v_toTopVar_1254_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v_toTopVar_1254_, 0, v_toVar_1253_);
lean_closure_set(v_toTopVar_1254_, 1, v_toBind_1248_);
lean_closure_set(v_toTopVar_1254_, 2, v___f_1250_);
lean_inc_ref(v_toTopVar_1254_);
v_asTopVar_1255_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v_asTopVar_1255_, 0, v_toTopVar_1254_);
lean_closure_set(v_asTopVar_1255_, 1, v_inst_1239_);
lean_closure_set(v_asTopVar_1255_, 2, v_toBind_1248_);
lean_inc(v_inst_1240_);
lean_inc_ref(v_e_1246_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5), 13, 12);
lean_closure_set(v___f_1256_, 0, v_toTopVar_1254_);
lean_closure_set(v___f_1256_, 1, v_e_1246_);
lean_closure_set(v___f_1256_, 2, v_toPure_1249_);
lean_closure_set(v___f_1256_, 3, v_inst_1240_);
lean_closure_set(v___f_1256_, 4, v_inst_1241_);
lean_closure_set(v___f_1256_, 5, v_inst_1242_);
lean_closure_set(v___f_1256_, 6, v_inst_1243_);
lean_closure_set(v___f_1256_, 7, v_inst_1244_);
lean_closure_set(v___f_1256_, 8, v_toVar_1253_);
lean_closure_set(v___f_1256_, 9, v_asVar_1252_);
lean_closure_set(v___f_1256_, 10, v_toBind_1248_);
lean_closure_set(v___f_1256_, 11, v_asTopVar_1255_);
v___x_1257_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_1257_, 0, v_e_1246_);
v___x_1258_ = lean_apply_2(v_inst_1240_, lean_box(0), v___x_1257_);
v___x_1259_ = lean_apply_4(v_toBind_1248_, lean_box(0), lean_box(0), v___x_1258_, v___f_1256_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f(lean_object* v_m_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_e_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(v_inst_1261_, v_inst_1262_, v_inst_1263_, v_inst_1264_, v_inst_1265_, v_inst_1266_, v_inst_1267_, v_e_1268_);
return v___x_1269_;
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
