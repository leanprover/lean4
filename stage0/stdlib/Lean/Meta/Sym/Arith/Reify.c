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
lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(lean_object* v_asVar_173_, lean_object* v_e_174_, lean_object* v_arg_175_, lean_object* v_toPure_176_, lean_object* v_toVar_177_, uint8_t v_____do__lift_178_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_asVar_173_ = stack[0].m_obj;
lean_object* v_e_174_ = stack[1].m_obj;
lean_object* v_arg_175_ = stack[2].m_obj;
lean_object* v_toPure_176_ = stack[3].m_obj;
lean_object* v_toVar_177_ = stack[4].m_obj;
uint8_t v_____do__lift_178_ = stack[5].m_num;
lean_object* v_res_191_;
v_res_191_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(v_asVar_173_, v_e_174_, v_arg_175_, v_toPure_176_, v_toVar_177_, v_____do__lift_178_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed(lean_object* v_asVar_192_, lean_object* v_e_193_, lean_object* v_arg_194_, lean_object* v_toPure_195_, lean_object* v_toVar_196_, lean_object* v_____do__lift_197_){
_start:
{
uint8_t v_____do__lift_1185__boxed_198_; lean_object* v_res_199_; 
v_____do__lift_1185__boxed_198_ = lean_unbox(v_____do__lift_197_);
v_res_199_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(v_asVar_192_, v_e_193_, v_arg_194_, v_toPure_195_, v_toVar_196_, v_____do__lift_1185__boxed_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7(lean_object* v_____do__lift_200_, lean_object* v_toPure_201_, lean_object* v_____do__lift_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_203_, 0, v_____do__lift_200_);
lean_ctor_set(v___x_203_, 1, v_____do__lift_202_);
v___x_204_ = lean_apply_2(v_toPure_201_, lean_box(0), v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4(lean_object* v_____do__lift_205_, lean_object* v_toPure_206_, lean_object* v_____do__lift_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v_____do__lift_205_);
lean_ctor_set(v___x_208_, 1, v_____do__lift_207_);
v___x_209_ = lean_apply_2(v_toPure_206_, lean_box(0), v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9(lean_object* v_val_210_, lean_object* v_toPure_211_, lean_object* v_____do__lift_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_213_, 0, v_____do__lift_212_);
lean_ctor_set(v___x_213_, 1, v_val_210_);
v___x_214_ = lean_apply_2(v_toPure_211_, lean_box(0), v___x_213_);
return v___x_214_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(lean_object* v_asVar_215_, lean_object* v_e_216_, lean_object* v_arg_217_, lean_object* v_toPure_218_, lean_object* v_toVar_219_, uint8_t v_____do__lift_220_){
_start:
{
if (v_____do__lift_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec(v_toVar_219_);
lean_dec(v_toPure_218_);
lean_dec_ref(v_arg_217_);
v___x_221_ = lean_apply_1(v_asVar_215_, v_e_216_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
lean_dec(v_asVar_215_);
v___x_222_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_217_);
if (lean_obj_tag(v___x_222_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
lean_dec(v_toVar_219_);
lean_dec_ref(v_e_216_);
v_val_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_val_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_val_223_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_apply_2(v_toPure_218_, lean_box(0), v___x_228_);
return v___x_229_;
}
}
}
else
{
lean_object* v___x_232_; 
lean_dec(v___x_222_);
lean_dec(v_toPure_218_);
v___x_232_ = lean_apply_1(v_toVar_219_, v_e_216_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_asVar_215_ = stack[0].m_obj;
lean_object* v_e_216_ = stack[1].m_obj;
lean_object* v_arg_217_ = stack[2].m_obj;
lean_object* v_toPure_218_ = stack[3].m_obj;
lean_object* v_toVar_219_ = stack[4].m_obj;
uint8_t v_____do__lift_220_ = stack[5].m_num;
lean_object* v_res_233_;
v_res_233_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(v_asVar_215_, v_e_216_, v_arg_217_, v_toPure_218_, v_toVar_219_, v_____do__lift_220_);
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed(lean_object* v_asVar_234_, lean_object* v_e_235_, lean_object* v_arg_236_, lean_object* v_toPure_237_, lean_object* v_toVar_238_, lean_object* v_____do__lift_239_){
_start:
{
uint8_t v_____do__lift_1267__boxed_240_; lean_object* v_res_241_; 
v_____do__lift_1267__boxed_240_ = lean_unbox(v_____do__lift_239_);
v_res_241_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(v_asVar_234_, v_e_235_, v_arg_236_, v_toPure_237_, v_toVar_238_, v_____do__lift_1267__boxed_240_);
return v_res_241_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(lean_object* v_asVar_286_, lean_object* v_e_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_toVar_293_, lean_object* v_arg_294_, lean_object* v_toBind_295_, lean_object* v___f_296_, uint8_t v_____do__lift_297_){
_start:
{
if (v_____do__lift_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec(v___f_296_);
lean_dec(v_toBind_295_);
lean_dec_ref(v_arg_294_);
lean_dec(v_toVar_293_);
lean_dec_ref(v_inst_292_);
lean_dec_ref(v_inst_291_);
lean_dec_ref(v_inst_290_);
lean_dec_ref(v_inst_289_);
lean_dec(v_inst_288_);
v___x_298_ = lean_apply_1(v_asVar_286_, v_e_287_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec_ref(v_e_287_);
v___x_299_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_288_, v_inst_289_, v_inst_290_, v_inst_291_, v_inst_292_, v_toVar_293_, v_asVar_286_, v_arg_294_);
v___x_300_ = lean_apply_4(v_toBind_295_, lean_box(0), lean_box(0), v___x_299_, v___f_296_);
return v___x_300_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_asVar_286_ = stack[0].m_obj;
lean_object* v_e_287_ = stack[1].m_obj;
lean_object* v_inst_288_ = stack[2].m_obj;
lean_object* v_inst_289_ = stack[3].m_obj;
lean_object* v_inst_290_ = stack[4].m_obj;
lean_object* v_inst_291_ = stack[5].m_obj;
lean_object* v_inst_292_ = stack[6].m_obj;
lean_object* v_toVar_293_ = stack[7].m_obj;
lean_object* v_arg_294_ = stack[8].m_obj;
lean_object* v_toBind_295_ = stack[9].m_obj;
lean_object* v___f_296_ = stack[10].m_obj;
uint8_t v_____do__lift_297_ = stack[11].m_num;
lean_object* v_res_301_;
v_res_301_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(v_asVar_286_, v_e_287_, v_inst_288_, v_inst_289_, v_inst_290_, v_inst_291_, v_inst_292_, v_toVar_293_, v_arg_294_, v_toBind_295_, v___f_296_, v_____do__lift_297_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed(lean_object* v_asVar_302_, lean_object* v_e_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_toVar_309_, lean_object* v_arg_310_, lean_object* v_toBind_311_, lean_object* v___f_312_, lean_object* v_____do__lift_313_){
_start:
{
uint8_t v_____do__lift_1393__boxed_314_; lean_object* v_res_315_; 
v_____do__lift_1393__boxed_314_ = lean_unbox(v_____do__lift_313_);
v_res_315_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(v_asVar_302_, v_e_303_, v_inst_304_, v_inst_305_, v_inst_306_, v_inst_307_, v_inst_308_, v_toVar_309_, v_arg_310_, v_toBind_311_, v___f_312_, v_____do__lift_1393__boxed_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5(lean_object* v_toPure_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_toVar_322_, lean_object* v_asVar_323_, lean_object* v_arg_324_, lean_object* v_toBind_325_, lean_object* v_____do__lift_326_){
_start:
{
lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___f_327_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_327_, 0, v_____do__lift_326_);
lean_closure_set(v___f_327_, 1, v_toPure_316_);
v___x_328_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_317_, v_inst_318_, v_inst_319_, v_inst_320_, v_inst_321_, v_toVar_322_, v_asVar_323_, v_arg_324_);
v___x_329_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_328_, v___f_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6(lean_object* v_toPure_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_toVar_336_, lean_object* v_asVar_337_, lean_object* v_arg_338_, lean_object* v_toBind_339_, lean_object* v_____do__lift_340_){
_start:
{
lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___f_341_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__7), 3, 2);
lean_closure_set(v___f_341_, 0, v_____do__lift_340_);
lean_closure_set(v___f_341_, 1, v_toPure_330_);
v___x_342_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_331_, v_inst_332_, v_inst_333_, v_inst_334_, v_inst_335_, v_toVar_336_, v_asVar_337_, v_arg_338_);
v___x_343_ = lean_apply_4(v_toBind_339_, lean_box(0), lean_box(0), v___x_342_, v___f_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10(lean_object* v_toVar_344_, lean_object* v_e_345_, lean_object* v_toPure_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_asVar_352_, lean_object* v_toBind_353_, lean_object* v___f_354_, lean_object* v_____x_355_){
_start:
{
lean_object* v_n_357_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = l_Lean_Expr_cleanupAnnotations(v_____x_355_);
v___x_372_ = l_Lean_Expr_isApp(v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
lean_dec_ref(v___x_371_);
lean_dec(v___f_354_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
lean_dec(v_toPure_346_);
v___x_373_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_373_;
}
else
{
lean_object* v_arg_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_arg_374_ = lean_ctor_get(v___x_371_, 1);
lean_inc_ref(v_arg_374_);
v___x_375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_371_);
v___x_376_ = l_Lean_Expr_isApp(v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec_ref(v___x_375_);
lean_dec_ref(v_arg_374_);
lean_dec(v___f_354_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
lean_dec(v_toPure_346_);
v___x_377_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_377_;
}
else
{
lean_object* v_arg_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_arg_378_ = lean_ctor_get(v___x_375_, 1);
lean_inc_ref(v_arg_378_);
v___x_379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_375_);
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2));
v___x_381_ = l_Lean_Expr_isConstOf(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
v___x_382_ = l_Lean_Expr_isApp(v___x_379_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v___x_379_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_374_);
lean_dec(v___f_354_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
lean_dec(v_toPure_346_);
v___x_383_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_383_;
}
else
{
lean_object* v_arg_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_arg_384_ = lean_ctor_get(v___x_379_, 1);
lean_inc_ref(v_arg_384_);
v___x_385_ = l_Lean_Expr_appFnCleanup___redArg(v___x_379_);
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_387_ = l_Lean_Expr_isConstOf(v___x_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_389_ = l_Lean_Expr_isConstOf(v___x_385_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10));
v___x_391_ = l_Lean_Expr_isConstOf(v___x_385_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13));
v___x_393_ = l_Lean_Expr_isConstOf(v___x_385_, v___x_392_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; 
lean_dec(v___f_354_);
v___x_394_ = l_Lean_Expr_isApp(v___x_385_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_dec_ref(v___x_385_);
lean_dec_ref(v_arg_384_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_374_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
lean_dec(v_toPure_346_);
v___x_395_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_385_);
v___x_397_ = l_Lean_Expr_isApp(v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v___x_396_);
lean_dec_ref(v_arg_384_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_374_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
lean_dec(v_toPure_346_);
v___x_398_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_396_);
v___x_400_ = l_Lean_Expr_isApp(v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v___x_399_);
lean_dec_ref(v_arg_384_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_374_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
lean_dec(v_toPure_346_);
v___x_401_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = l_Lean_Expr_appFnCleanup___redArg(v___x_399_);
v___x_403_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_404_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19));
v___x_406_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_408_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_410_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_409_);
lean_dec_ref(v___x_402_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v_arg_384_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_374_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
lean_dec(v_toPure_346_);
v___x_411_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_411_;
}
else
{
lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_inc_n(v_toBind_353_, 2);
lean_inc(v_asVar_352_);
lean_inc(v_toVar_344_);
lean_inc_ref_n(v_inst_351_, 2);
lean_inc_ref_n(v_inst_350_, 2);
lean_inc_ref_n(v_inst_349_, 2);
lean_inc_ref_n(v_inst_348_, 2);
lean_inc_n(v_inst_347_, 2);
v___f_412_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2), 11, 10);
lean_closure_set(v___f_412_, 0, v_toPure_346_);
lean_closure_set(v___f_412_, 1, v_inst_347_);
lean_closure_set(v___f_412_, 2, v_inst_348_);
lean_closure_set(v___f_412_, 3, v_inst_349_);
lean_closure_set(v___f_412_, 4, v_inst_350_);
lean_closure_set(v___f_412_, 5, v_inst_351_);
lean_closure_set(v___f_412_, 6, v_toVar_344_);
lean_closure_set(v___f_412_, 7, v_asVar_352_);
lean_closure_set(v___f_412_, 8, v_arg_374_);
lean_closure_set(v___f_412_, 9, v_toBind_353_);
v___f_413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_413_, 0, v_asVar_352_);
lean_closure_set(v___f_413_, 1, v_e_345_);
lean_closure_set(v___f_413_, 2, v_inst_347_);
lean_closure_set(v___f_413_, 3, v_inst_348_);
lean_closure_set(v___f_413_, 4, v_inst_349_);
lean_closure_set(v___f_413_, 5, v_inst_350_);
lean_closure_set(v___f_413_, 6, v_inst_351_);
lean_closure_set(v___f_413_, 7, v_toVar_344_);
lean_closure_set(v___f_413_, 8, v_arg_378_);
lean_closure_set(v___f_413_, 9, v_toBind_353_);
lean_closure_set(v___f_413_, 10, v___f_412_);
v___x_414_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_inst_351_, v_arg_384_);
v___x_415_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_414_, v___f_413_);
return v___x_415_;
}
}
else
{
lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref(v___x_402_);
lean_inc_n(v_toBind_353_, 2);
lean_inc(v_asVar_352_);
lean_inc(v_toVar_344_);
lean_inc_ref_n(v_inst_351_, 2);
lean_inc_ref_n(v_inst_350_, 2);
lean_inc_ref_n(v_inst_349_, 2);
lean_inc_ref_n(v_inst_348_, 2);
lean_inc_n(v_inst_347_, 2);
v___f_416_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__5), 11, 10);
lean_closure_set(v___f_416_, 0, v_toPure_346_);
lean_closure_set(v___f_416_, 1, v_inst_347_);
lean_closure_set(v___f_416_, 2, v_inst_348_);
lean_closure_set(v___f_416_, 3, v_inst_349_);
lean_closure_set(v___f_416_, 4, v_inst_350_);
lean_closure_set(v___f_416_, 5, v_inst_351_);
lean_closure_set(v___f_416_, 6, v_toVar_344_);
lean_closure_set(v___f_416_, 7, v_asVar_352_);
lean_closure_set(v___f_416_, 8, v_arg_374_);
lean_closure_set(v___f_416_, 9, v_toBind_353_);
v___f_417_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_417_, 0, v_asVar_352_);
lean_closure_set(v___f_417_, 1, v_e_345_);
lean_closure_set(v___f_417_, 2, v_inst_347_);
lean_closure_set(v___f_417_, 3, v_inst_348_);
lean_closure_set(v___f_417_, 4, v_inst_349_);
lean_closure_set(v___f_417_, 5, v_inst_350_);
lean_closure_set(v___f_417_, 6, v_inst_351_);
lean_closure_set(v___f_417_, 7, v_toVar_344_);
lean_closure_set(v___f_417_, 8, v_arg_378_);
lean_closure_set(v___f_417_, 9, v_toBind_353_);
lean_closure_set(v___f_417_, 10, v___f_416_);
v___x_418_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_inst_351_, v_arg_384_);
v___x_419_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_418_, v___f_417_);
return v___x_419_;
}
}
else
{
lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v___x_402_);
lean_inc_n(v_toBind_353_, 2);
lean_inc(v_asVar_352_);
lean_inc(v_toVar_344_);
lean_inc_ref_n(v_inst_351_, 2);
lean_inc_ref_n(v_inst_350_, 2);
lean_inc_ref_n(v_inst_349_, 2);
lean_inc_ref_n(v_inst_348_, 2);
lean_inc_n(v_inst_347_, 2);
v___f_420_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__6), 11, 10);
lean_closure_set(v___f_420_, 0, v_toPure_346_);
lean_closure_set(v___f_420_, 1, v_inst_347_);
lean_closure_set(v___f_420_, 2, v_inst_348_);
lean_closure_set(v___f_420_, 3, v_inst_349_);
lean_closure_set(v___f_420_, 4, v_inst_350_);
lean_closure_set(v___f_420_, 5, v_inst_351_);
lean_closure_set(v___f_420_, 6, v_toVar_344_);
lean_closure_set(v___f_420_, 7, v_asVar_352_);
lean_closure_set(v___f_420_, 8, v_arg_374_);
lean_closure_set(v___f_420_, 9, v_toBind_353_);
v___f_421_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_421_, 0, v_asVar_352_);
lean_closure_set(v___f_421_, 1, v_e_345_);
lean_closure_set(v___f_421_, 2, v_inst_347_);
lean_closure_set(v___f_421_, 3, v_inst_348_);
lean_closure_set(v___f_421_, 4, v_inst_349_);
lean_closure_set(v___f_421_, 5, v_inst_350_);
lean_closure_set(v___f_421_, 6, v_inst_351_);
lean_closure_set(v___f_421_, 7, v_toVar_344_);
lean_closure_set(v___f_421_, 8, v_arg_378_);
lean_closure_set(v___f_421_, 9, v_toBind_353_);
lean_closure_set(v___f_421_, 10, v___f_420_);
v___x_422_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_inst_351_, v_arg_384_);
v___x_423_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_422_, v___f_421_);
return v___x_423_;
}
}
else
{
lean_object* v___x_424_; 
lean_dec_ref(v___x_402_);
v___x_424_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_374_);
if (lean_obj_tag(v___x_424_) == 1)
{
lean_object* v_val_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_val_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v___x_424_, 1);
v___f_426_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9), 3, 2);
lean_closure_set(v___f_426_, 0, v_val_425_);
lean_closure_set(v___f_426_, 1, v_toPure_346_);
lean_inc(v_toBind_353_);
lean_inc_ref(v_inst_351_);
lean_inc_ref(v_inst_350_);
lean_inc_ref(v_inst_349_);
lean_inc_ref(v_inst_348_);
lean_inc(v_inst_347_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_427_, 0, v_asVar_352_);
lean_closure_set(v___f_427_, 1, v_e_345_);
lean_closure_set(v___f_427_, 2, v_inst_347_);
lean_closure_set(v___f_427_, 3, v_inst_348_);
lean_closure_set(v___f_427_, 4, v_inst_349_);
lean_closure_set(v___f_427_, 5, v_inst_350_);
lean_closure_set(v___f_427_, 6, v_inst_351_);
lean_closure_set(v___f_427_, 7, v_toVar_344_);
lean_closure_set(v___f_427_, 8, v_arg_378_);
lean_closure_set(v___f_427_, 9, v_toBind_353_);
lean_closure_set(v___f_427_, 10, v___f_426_);
v___x_428_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_inst_351_, v_arg_384_);
v___x_429_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_428_, v___f_427_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
lean_dec(v___x_424_);
lean_dec_ref(v_arg_384_);
lean_dec_ref(v_arg_378_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
lean_dec(v_toPure_346_);
v___x_430_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_430_;
}
}
}
}
}
}
else
{
lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v___x_385_);
lean_dec_ref(v_arg_384_);
lean_dec(v_toPure_346_);
lean_inc(v_toBind_353_);
lean_inc_ref(v_inst_351_);
lean_inc_ref(v_inst_350_);
lean_inc_ref(v_inst_349_);
lean_inc_ref(v_inst_348_);
lean_inc(v_inst_347_);
v___f_431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_431_, 0, v_asVar_352_);
lean_closure_set(v___f_431_, 1, v_e_345_);
lean_closure_set(v___f_431_, 2, v_inst_347_);
lean_closure_set(v___f_431_, 3, v_inst_348_);
lean_closure_set(v___f_431_, 4, v_inst_349_);
lean_closure_set(v___f_431_, 5, v_inst_350_);
lean_closure_set(v___f_431_, 6, v_inst_351_);
lean_closure_set(v___f_431_, 7, v_toVar_344_);
lean_closure_set(v___f_431_, 8, v_arg_374_);
lean_closure_set(v___f_431_, 9, v_toBind_353_);
lean_closure_set(v___f_431_, 10, v___f_354_);
v___x_432_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_inst_351_, v_arg_378_);
v___x_433_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_432_, v___f_431_);
return v___x_433_;
}
}
else
{
lean_object* v___f_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref(v___x_385_);
lean_dec_ref(v_arg_384_);
lean_dec(v___f_354_);
lean_dec_ref(v_inst_348_);
v___f_434_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_434_, 0, v_asVar_352_);
lean_closure_set(v___f_434_, 1, v_e_345_);
lean_closure_set(v___f_434_, 2, v_arg_374_);
lean_closure_set(v___f_434_, 3, v_toPure_346_);
lean_closure_set(v___f_434_, 4, v_toVar_344_);
v___x_435_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_347_, v_inst_349_, v_inst_350_, v_inst_351_, v_arg_378_);
v___x_436_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_435_, v___f_434_);
return v___x_436_;
}
}
else
{
lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec_ref(v___x_385_);
lean_dec_ref(v_arg_384_);
lean_dec(v___f_354_);
lean_dec_ref(v_inst_348_);
v___f_437_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed), 6, 5);
lean_closure_set(v___f_437_, 0, v_asVar_352_);
lean_closure_set(v___f_437_, 1, v_e_345_);
lean_closure_set(v___f_437_, 2, v_arg_374_);
lean_closure_set(v___f_437_, 3, v_toPure_346_);
lean_closure_set(v___f_437_, 4, v_toVar_344_);
v___x_438_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_347_, v_inst_349_, v_inst_350_, v_inst_351_, v_arg_378_);
v___x_439_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_438_, v___f_437_);
return v___x_439_;
}
}
else
{
lean_dec_ref(v___x_385_);
lean_dec_ref(v_arg_384_);
lean_dec_ref(v_arg_374_);
lean_dec(v___f_354_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
v_n_357_ = v_arg_378_;
goto v___jp_356_;
}
}
}
else
{
lean_dec_ref(v___x_379_);
lean_dec_ref(v_arg_378_);
lean_dec(v___f_354_);
lean_dec(v_toBind_353_);
lean_dec(v_asVar_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
v_n_357_ = v_arg_374_;
goto v___jp_356_;
}
}
}
v___jp_356_:
{
if (lean_obj_tag(v_n_357_) == 9)
{
lean_object* v_a_358_; 
v_a_358_ = lean_ctor_get(v_n_357_, 0);
lean_inc_ref(v_a_358_);
lean_dec_ref_known(v_n_357_, 1);
if (lean_obj_tag(v_a_358_) == 0)
{
lean_object* v_val_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref(v_e_345_);
lean_dec(v_toVar_344_);
v_val_359_ = lean_ctor_get(v_a_358_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_a_358_);
if (v_isSharedCheck_368_ == 0)
{
v___x_361_ = v_a_358_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_val_359_);
lean_dec(v_a_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_nat_to_int(v_val_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_apply_2(v_toPure_346_, lean_box(0), v___x_365_);
return v___x_366_;
}
}
}
else
{
lean_object* v___x_369_; 
lean_dec_ref(v_a_358_);
lean_dec(v_toPure_346_);
v___x_369_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_369_;
}
}
else
{
lean_object* v___x_370_; 
lean_dec_ref(v_n_357_);
lean_dec(v_toPure_346_);
v___x_370_ = lean_apply_1(v_toVar_344_, v_e_345_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_toVar_445_, lean_object* v_asVar_446_, lean_object* v_e_447_){
_start:
{
lean_object* v_toApplicative_448_; lean_object* v_toBind_449_; lean_object* v_toPure_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___f_453_; lean_object* v___f_454_; lean_object* v___x_455_; 
v_toApplicative_448_ = lean_ctor_get(v_inst_442_, 0);
v_toBind_449_ = lean_ctor_get(v_inst_442_, 1);
lean_inc_n(v_toBind_449_, 2);
v_toPure_450_ = lean_ctor_get(v_toApplicative_448_, 1);
lean_inc_n(v_toPure_450_, 2);
lean_inc_ref(v_e_447_);
v___x_451_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_451_, 0, v_e_447_);
lean_inc(v_inst_440_);
v___x_452_ = lean_apply_2(v_inst_440_, lean_box(0), v___x_451_);
v___f_453_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_453_, 0, v_toPure_450_);
v___f_454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10), 12, 11);
lean_closure_set(v___f_454_, 0, v_toVar_445_);
lean_closure_set(v___f_454_, 1, v_e_447_);
lean_closure_set(v___f_454_, 2, v_toPure_450_);
lean_closure_set(v___f_454_, 3, v_inst_440_);
lean_closure_set(v___f_454_, 4, v_inst_441_);
lean_closure_set(v___f_454_, 5, v_inst_442_);
lean_closure_set(v___f_454_, 6, v_inst_443_);
lean_closure_set(v___f_454_, 7, v_inst_444_);
lean_closure_set(v___f_454_, 8, v_asVar_446_);
lean_closure_set(v___f_454_, 9, v_toBind_449_);
lean_closure_set(v___f_454_, 10, v___f_453_);
v___x_455_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v___x_452_, v___f_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2(lean_object* v_toPure_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_toVar_462_, lean_object* v_asVar_463_, lean_object* v_arg_464_, lean_object* v_toBind_465_, lean_object* v_____do__lift_466_){
_start:
{
lean_object* v___f_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___f_467_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_467_, 0, v_____do__lift_466_);
lean_closure_set(v___f_467_, 1, v_toPure_456_);
v___x_468_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_457_, v_inst_458_, v_inst_459_, v_inst_460_, v_inst_461_, v_toVar_462_, v_asVar_463_, v_arg_464_);
v___x_469_ = lean_apply_4(v_toBind_465_, lean_box(0), lean_box(0), v___x_468_, v___f_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go(lean_object* v_m_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_toVar_476_, lean_object* v_asVar_477_, lean_object* v_e_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_471_, v_inst_472_, v_inst_473_, v_inst_474_, v_inst_475_, v_toVar_476_, v_asVar_477_, v_e_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0(lean_object* v_toPure_480_, lean_object* v_____do__lift_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_482_, 0, v_____do__lift_481_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___x_484_ = lean_apply_2(v_toPure_480_, lean_box(0), v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1(lean_object* v_toPure_485_, lean_object* v_____do__lift_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v_____do__lift_486_);
v___x_488_ = lean_apply_2(v_toPure_485_, lean_box(0), v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2(lean_object* v_toPure_489_, lean_object* v_____do__lift_490_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_491_, 0, v_____do__lift_490_);
v___x_492_ = lean_apply_2(v_toPure_489_, lean_box(0), v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3(lean_object* v_inst_493_, lean_object* v_e_494_, lean_object* v_toBind_495_, lean_object* v___f_496_, lean_object* v_____r_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_apply_1(v_inst_493_, v_e_494_);
v___x_499_ = lean_apply_4(v_toBind_495_, lean_box(0), lean_box(0), v___x_498_, v___f_496_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4(lean_object* v_inst_500_, lean_object* v_toBind_501_, lean_object* v___f_502_, lean_object* v_inst_503_, lean_object* v_e_504_){
_start:
{
lean_object* v___f_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_inc(v_toBind_501_);
lean_inc_ref(v_e_504_);
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_505_, 0, v_inst_500_);
lean_closure_set(v___f_505_, 1, v_e_504_);
lean_closure_set(v___f_505_, 2, v_toBind_501_);
lean_closure_set(v___f_505_, 3, v___f_502_);
v___x_506_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_503_, v_e_504_);
v___x_507_ = lean_apply_4(v_toBind_501_, lean_box(0), lean_box(0), v___x_506_, v___f_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6(lean_object* v_inst_508_, lean_object* v_toBind_509_, lean_object* v___f_510_, lean_object* v_e_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_apply_1(v_inst_508_, v_e_511_);
v___x_513_ = lean_apply_4(v_toBind_509_, lean_box(0), lean_box(0), v___x_512_, v___f_510_);
return v___x_513_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(uint8_t v_skipVar_514_, lean_object* v_toVar_515_, lean_object* v_toBind_516_, lean_object* v___f_517_, lean_object* v_toPure_518_, lean_object* v_e_519_){
_start:
{
if (v_skipVar_514_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_toPure_518_);
v___x_520_ = lean_apply_1(v_toVar_515_, v_e_519_);
v___x_521_ = lean_apply_4(v_toBind_516_, lean_box(0), lean_box(0), v___x_520_, v___f_517_);
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v_e_519_);
lean_dec(v___f_517_);
lean_dec(v_toBind_516_);
lean_dec(v_toVar_515_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_2(v_toPure_518_, lean_box(0), v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipVar_514_ = stack[0].m_num;
lean_object* v_toVar_515_ = stack[1].m_obj;
lean_object* v_toBind_516_ = stack[2].m_obj;
lean_object* v___f_517_ = stack[3].m_obj;
lean_object* v_toPure_518_ = stack[4].m_obj;
lean_object* v_e_519_ = stack[5].m_obj;
lean_object* v_res_524_;
v_res_524_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(v_skipVar_514_, v_toVar_515_, v_toBind_516_, v___f_517_, v_toPure_518_, v_e_519_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed(lean_object* v_skipVar_525_, lean_object* v_toVar_526_, lean_object* v_toBind_527_, lean_object* v___f_528_, lean_object* v_toPure_529_, lean_object* v_e_530_){
_start:
{
uint8_t v_skipVar_boxed_531_; lean_object* v_res_532_; 
v_skipVar_boxed_531_ = lean_unbox(v_skipVar_525_);
v_res_532_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(v_skipVar_boxed_531_, v_toVar_526_, v_toBind_527_, v___f_528_, v_toPure_529_, v_e_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7(lean_object* v_toTopVar_533_, lean_object* v_e_534_, lean_object* v_____r_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_apply_1(v_toTopVar_533_, v_e_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8(lean_object* v_toTopVar_537_, lean_object* v_inst_538_, lean_object* v_toBind_539_, lean_object* v_e_540_){
_start:
{
lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc_ref(v_e_540_);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7), 3, 2);
lean_closure_set(v___f_541_, 0, v_toTopVar_537_);
lean_closure_set(v___f_541_, 1, v_e_540_);
v___x_542_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_538_, v_e_540_);
v___x_543_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_542_, v___f_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9(lean_object* v_____do__lift_544_, lean_object* v_toPure_545_, lean_object* v_____do__lift_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v_____do__lift_544_);
lean_ctor_set(v___x_547_, 1, v_____do__lift_546_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = lean_apply_2(v_toPure_545_, lean_box(0), v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10(lean_object* v_toPure_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_toVar_556_, lean_object* v_asVar_557_, lean_object* v_arg_558_, lean_object* v_toBind_559_, lean_object* v_____do__lift_560_){
_start:
{
lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___f_561_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9), 3, 2);
lean_closure_set(v___f_561_, 0, v_____do__lift_560_);
lean_closure_set(v___f_561_, 1, v_toPure_550_);
v___x_562_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_551_, v_inst_552_, v_inst_553_, v_inst_554_, v_inst_555_, v_toVar_556_, v_asVar_557_, v_arg_558_);
v___x_563_ = lean_apply_4(v_toBind_559_, lean_box(0), lean_box(0), v___x_562_, v___f_561_);
return v___x_563_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(lean_object* v_asTopVar_564_, lean_object* v_e_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_toVar_571_, lean_object* v_asVar_572_, lean_object* v_arg_573_, lean_object* v_toBind_574_, lean_object* v___f_575_, uint8_t v_____do__lift_576_){
_start:
{
if (v_____do__lift_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v___f_575_);
lean_dec(v_toBind_574_);
lean_dec_ref(v_arg_573_);
lean_dec(v_asVar_572_);
lean_dec(v_toVar_571_);
lean_dec_ref(v_inst_570_);
lean_dec_ref(v_inst_569_);
lean_dec_ref(v_inst_568_);
lean_dec_ref(v_inst_567_);
lean_dec(v_inst_566_);
v___x_577_ = lean_apply_1(v_asTopVar_564_, v_e_565_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref(v_e_565_);
lean_dec(v_asTopVar_564_);
v___x_578_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_566_, v_inst_567_, v_inst_568_, v_inst_569_, v_inst_570_, v_toVar_571_, v_asVar_572_, v_arg_573_);
v___x_579_ = lean_apply_4(v_toBind_574_, lean_box(0), lean_box(0), v___x_578_, v___f_575_);
return v___x_579_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_asTopVar_564_ = stack[0].m_obj;
lean_object* v_e_565_ = stack[1].m_obj;
lean_object* v_inst_566_ = stack[2].m_obj;
lean_object* v_inst_567_ = stack[3].m_obj;
lean_object* v_inst_568_ = stack[4].m_obj;
lean_object* v_inst_569_ = stack[5].m_obj;
lean_object* v_inst_570_ = stack[6].m_obj;
lean_object* v_toVar_571_ = stack[7].m_obj;
lean_object* v_asVar_572_ = stack[8].m_obj;
lean_object* v_arg_573_ = stack[9].m_obj;
lean_object* v_toBind_574_ = stack[10].m_obj;
lean_object* v___f_575_ = stack[11].m_obj;
uint8_t v_____do__lift_576_ = stack[12].m_num;
lean_object* v_res_580_;
v_res_580_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(v_asTopVar_564_, v_e_565_, v_inst_566_, v_inst_567_, v_inst_568_, v_inst_569_, v_inst_570_, v_toVar_571_, v_asVar_572_, v_arg_573_, v_toBind_574_, v___f_575_, v_____do__lift_576_);
stack->m_obj
 = v_res_580_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed(lean_object* v_asTopVar_581_, lean_object* v_e_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_toVar_588_, lean_object* v_asVar_589_, lean_object* v_arg_590_, lean_object* v_toBind_591_, lean_object* v___f_592_, lean_object* v_____do__lift_593_){
_start:
{
uint8_t v_____do__lift_1485__boxed_594_; lean_object* v_res_595_; 
v_____do__lift_1485__boxed_594_ = lean_unbox(v_____do__lift_593_);
v_res_595_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(v_asTopVar_581_, v_e_582_, v_inst_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_toVar_588_, v_asVar_589_, v_arg_590_, v_toBind_591_, v___f_592_, v_____do__lift_1485__boxed_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12(lean_object* v_____do__lift_596_, lean_object* v_toPure_597_, lean_object* v_____do__lift_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v_____do__lift_596_);
lean_ctor_set(v___x_599_, 1, v_____do__lift_598_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___x_601_ = lean_apply_2(v_toPure_597_, lean_box(0), v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13(lean_object* v_toPure_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_toVar_608_, lean_object* v_asVar_609_, lean_object* v_arg_610_, lean_object* v_toBind_611_, lean_object* v_____do__lift_612_){
_start:
{
lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12), 3, 2);
lean_closure_set(v___f_613_, 0, v_____do__lift_612_);
lean_closure_set(v___f_613_, 1, v_toPure_602_);
v___x_614_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_603_, v_inst_604_, v_inst_605_, v_inst_606_, v_inst_607_, v_toVar_608_, v_asVar_609_, v_arg_610_);
v___x_615_ = lean_apply_4(v_toBind_611_, lean_box(0), lean_box(0), v___x_614_, v___f_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15(lean_object* v_____do__lift_616_, lean_object* v_toPure_617_, lean_object* v_____do__lift_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_619_, 0, v_____do__lift_616_);
lean_ctor_set(v___x_619_, 1, v_____do__lift_618_);
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
v___x_621_ = lean_apply_2(v_toPure_617_, lean_box(0), v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14(lean_object* v_toPure_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_toVar_628_, lean_object* v_asVar_629_, lean_object* v_arg_630_, lean_object* v_toBind_631_, lean_object* v_____do__lift_632_){
_start:
{
lean_object* v___f_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15), 3, 2);
lean_closure_set(v___f_633_, 0, v_____do__lift_632_);
lean_closure_set(v___f_633_, 1, v_toPure_622_);
v___x_634_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_inst_627_, v_toVar_628_, v_asVar_629_, v_arg_630_);
v___x_635_ = lean_apply_4(v_toBind_631_, lean_box(0), lean_box(0), v___x_634_, v___f_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17(lean_object* v_val_636_, lean_object* v_toPure_637_, lean_object* v_____do__lift_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_639_, 0, v_____do__lift_638_);
lean_ctor_set(v___x_639_, 1, v_val_636_);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_640_);
return v___x_641_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(lean_object* v_asTopVar_642_, lean_object* v_e_643_, lean_object* v_arg_644_, lean_object* v_toPure_645_, lean_object* v_toTopVar_646_, uint8_t v_____do__lift_647_){
_start:
{
if (v_____do__lift_647_ == 0)
{
lean_object* v___x_648_; 
lean_dec(v_toTopVar_646_);
lean_dec(v_toPure_645_);
lean_dec_ref(v_arg_644_);
v___x_648_ = lean_apply_1(v_asTopVar_642_, v_e_643_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; 
lean_dec(v_asTopVar_642_);
v___x_649_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_644_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_val_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_toTopVar_646_);
lean_dec_ref(v_e_643_);
v_val_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_659_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_val_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_654_, 0, v_val_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_658_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; 
v___x_657_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_656_);
return v___x_657_;
}
}
}
else
{
lean_object* v___x_660_; 
lean_dec(v___x_649_);
lean_dec(v_toPure_645_);
v___x_660_ = lean_apply_1(v_toTopVar_646_, v_e_643_);
return v___x_660_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_asTopVar_642_ = stack[0].m_obj;
lean_object* v_e_643_ = stack[1].m_obj;
lean_object* v_arg_644_ = stack[2].m_obj;
lean_object* v_toPure_645_ = stack[3].m_obj;
lean_object* v_toTopVar_646_ = stack[4].m_obj;
uint8_t v_____do__lift_647_ = stack[5].m_num;
lean_object* v_res_661_;
v_res_661_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(v_asTopVar_642_, v_e_643_, v_arg_644_, v_toPure_645_, v_toTopVar_646_, v_____do__lift_647_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed(lean_object* v_asTopVar_662_, lean_object* v_e_663_, lean_object* v_arg_664_, lean_object* v_toPure_665_, lean_object* v_toTopVar_666_, lean_object* v_____do__lift_667_){
_start:
{
uint8_t v_____do__lift_1633__boxed_668_; lean_object* v_res_669_; 
v_____do__lift_1633__boxed_668_ = lean_unbox(v_____do__lift_667_);
v_res_669_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(v_asTopVar_662_, v_e_663_, v_arg_664_, v_toPure_665_, v_toTopVar_666_, v_____do__lift_1633__boxed_668_);
return v_res_669_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(lean_object* v_asTopVar_670_, lean_object* v_e_671_, lean_object* v_arg_672_, lean_object* v_toPure_673_, lean_object* v_toTopVar_674_, uint8_t v_____do__lift_675_){
_start:
{
if (v_____do__lift_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec(v_toTopVar_674_);
lean_dec(v_toPure_673_);
lean_dec_ref(v_arg_672_);
v___x_676_ = lean_apply_1(v_asTopVar_670_, v_e_671_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; 
lean_dec(v_asTopVar_670_);
v___x_677_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_672_);
if (lean_obj_tag(v___x_677_) == 1)
{
lean_object* v_val_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_toTopVar_674_);
lean_dec_ref(v_e_671_);
v_val_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_687_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_val_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v_val_678_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_686_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; 
v___x_685_ = lean_apply_2(v_toPure_673_, lean_box(0), v___x_684_);
return v___x_685_;
}
}
}
else
{
lean_object* v___x_688_; 
lean_dec(v___x_677_);
lean_dec(v_toPure_673_);
v___x_688_ = lean_apply_1(v_toTopVar_674_, v_e_671_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_asTopVar_670_ = stack[0].m_obj;
lean_object* v_e_671_ = stack[1].m_obj;
lean_object* v_arg_672_ = stack[2].m_obj;
lean_object* v_toPure_673_ = stack[3].m_obj;
lean_object* v_toTopVar_674_ = stack[4].m_obj;
uint8_t v_____do__lift_675_ = stack[5].m_num;
lean_object* v_res_689_;
v_res_689_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(v_asTopVar_670_, v_e_671_, v_arg_672_, v_toPure_673_, v_toTopVar_674_, v_____do__lift_675_);
stack->m_obj
 = v_res_689_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed(lean_object* v_asTopVar_690_, lean_object* v_e_691_, lean_object* v_arg_692_, lean_object* v_toPure_693_, lean_object* v_toTopVar_694_, lean_object* v_____do__lift_695_){
_start:
{
uint8_t v_____do__lift_1682__boxed_696_; lean_object* v_res_697_; 
v_____do__lift_1682__boxed_696_ = lean_unbox(v_____do__lift_695_);
v_res_697_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(v_asTopVar_690_, v_e_691_, v_arg_692_, v_toPure_693_, v_toTopVar_694_, v_____do__lift_1682__boxed_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18(lean_object* v_toTopVar_698_, lean_object* v_e_699_, lean_object* v_toPure_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_toVar_706_, lean_object* v_asVar_707_, lean_object* v_toBind_708_, lean_object* v_asTopVar_709_, lean_object* v___f_710_, lean_object* v_____x_711_){
_start:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = l_Lean_Expr_cleanupAnnotations(v_____x_711_);
v___x_713_ = l_Lean_Expr_isApp(v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v___x_712_);
lean_dec(v___f_710_);
lean_dec(v_asTopVar_709_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toPure_700_);
v___x_714_ = lean_apply_1(v_toTopVar_698_, v_e_699_);
return v___x_714_;
}
else
{
lean_object* v_arg_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_arg_715_ = lean_ctor_get(v___x_712_, 1);
lean_inc_ref(v_arg_715_);
v___x_716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_712_);
v___x_717_ = l_Lean_Expr_isApp(v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec_ref(v___x_716_);
lean_dec_ref(v_arg_715_);
lean_dec(v___f_710_);
lean_dec(v_asTopVar_709_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toPure_700_);
v___x_718_ = lean_apply_1(v_toTopVar_698_, v_e_699_);
return v___x_718_;
}
else
{
lean_object* v_arg_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_arg_719_ = lean_ctor_get(v___x_716_, 1);
lean_inc_ref(v_arg_719_);
v___x_720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_716_);
v___x_721_ = l_Lean_Expr_isApp(v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec_ref(v___x_720_);
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_715_);
lean_dec(v___f_710_);
lean_dec(v_asTopVar_709_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toPure_700_);
v___x_722_ = lean_apply_1(v_toTopVar_698_, v_e_699_);
return v___x_722_;
}
else
{
lean_object* v_arg_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_arg_723_ = lean_ctor_get(v___x_720_, 1);
lean_inc_ref(v_arg_723_);
v___x_724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_720_);
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_726_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_728_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10));
v___x_730_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13));
v___x_732_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_731_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
lean_dec(v___f_710_);
v___x_733_ = l_Lean_Expr_isApp(v___x_724_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_dec_ref(v___x_724_);
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_715_);
lean_dec(v_asTopVar_709_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toPure_700_);
v___x_734_ = lean_apply_1(v_toTopVar_698_, v_e_699_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_724_);
v___x_736_ = l_Lean_Expr_isApp(v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_715_);
lean_dec(v_asTopVar_709_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toPure_700_);
v___x_737_ = lean_apply_1(v_toTopVar_698_, v_e_699_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = l_Lean_Expr_appFnCleanup___redArg(v___x_735_);
v___x_739_ = l_Lean_Expr_isApp(v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_715_);
lean_dec(v_asTopVar_709_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toPure_700_);
v___x_740_ = lean_apply_1(v_toTopVar_698_, v_e_699_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_738_);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_743_ = l_Lean_Expr_isConstOf(v___x_741_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19));
v___x_745_ = l_Lean_Expr_isConstOf(v___x_741_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_747_ = l_Lean_Expr_isConstOf(v___x_741_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_749_ = l_Lean_Expr_isConstOf(v___x_741_, v___x_748_);
lean_dec_ref(v___x_741_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_715_);
lean_dec(v_asTopVar_709_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toPure_700_);
v___x_750_ = lean_apply_1(v_toTopVar_698_, v_e_699_);
return v___x_750_;
}
else
{
lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_toTopVar_698_);
lean_inc_n(v_toBind_708_, 2);
lean_inc(v_asVar_707_);
lean_inc(v_toVar_706_);
lean_inc_ref_n(v_inst_705_, 2);
lean_inc_ref_n(v_inst_704_, 2);
lean_inc_ref_n(v_inst_703_, 2);
lean_inc_ref_n(v_inst_702_, 2);
lean_inc_n(v_inst_701_, 2);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10), 11, 10);
lean_closure_set(v___f_751_, 0, v_toPure_700_);
lean_closure_set(v___f_751_, 1, v_inst_701_);
lean_closure_set(v___f_751_, 2, v_inst_702_);
lean_closure_set(v___f_751_, 3, v_inst_703_);
lean_closure_set(v___f_751_, 4, v_inst_704_);
lean_closure_set(v___f_751_, 5, v_inst_705_);
lean_closure_set(v___f_751_, 6, v_toVar_706_);
lean_closure_set(v___f_751_, 7, v_asVar_707_);
lean_closure_set(v___f_751_, 8, v_arg_715_);
lean_closure_set(v___f_751_, 9, v_toBind_708_);
v___f_752_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_752_, 0, v_asTopVar_709_);
lean_closure_set(v___f_752_, 1, v_e_699_);
lean_closure_set(v___f_752_, 2, v_inst_701_);
lean_closure_set(v___f_752_, 3, v_inst_702_);
lean_closure_set(v___f_752_, 4, v_inst_703_);
lean_closure_set(v___f_752_, 5, v_inst_704_);
lean_closure_set(v___f_752_, 6, v_inst_705_);
lean_closure_set(v___f_752_, 7, v_toVar_706_);
lean_closure_set(v___f_752_, 8, v_asVar_707_);
lean_closure_set(v___f_752_, 9, v_arg_719_);
lean_closure_set(v___f_752_, 10, v_toBind_708_);
lean_closure_set(v___f_752_, 11, v___f_751_);
v___x_753_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_inst_704_, v_inst_705_, v_arg_723_);
v___x_754_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_753_, v___f_752_);
return v___x_754_;
}
}
else
{
lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref(v___x_741_);
lean_dec(v_toTopVar_698_);
lean_inc_n(v_toBind_708_, 2);
lean_inc(v_asVar_707_);
lean_inc(v_toVar_706_);
lean_inc_ref_n(v_inst_705_, 2);
lean_inc_ref_n(v_inst_704_, 2);
lean_inc_ref_n(v_inst_703_, 2);
lean_inc_ref_n(v_inst_702_, 2);
lean_inc_n(v_inst_701_, 2);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13), 11, 10);
lean_closure_set(v___f_755_, 0, v_toPure_700_);
lean_closure_set(v___f_755_, 1, v_inst_701_);
lean_closure_set(v___f_755_, 2, v_inst_702_);
lean_closure_set(v___f_755_, 3, v_inst_703_);
lean_closure_set(v___f_755_, 4, v_inst_704_);
lean_closure_set(v___f_755_, 5, v_inst_705_);
lean_closure_set(v___f_755_, 6, v_toVar_706_);
lean_closure_set(v___f_755_, 7, v_asVar_707_);
lean_closure_set(v___f_755_, 8, v_arg_715_);
lean_closure_set(v___f_755_, 9, v_toBind_708_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_756_, 0, v_asTopVar_709_);
lean_closure_set(v___f_756_, 1, v_e_699_);
lean_closure_set(v___f_756_, 2, v_inst_701_);
lean_closure_set(v___f_756_, 3, v_inst_702_);
lean_closure_set(v___f_756_, 4, v_inst_703_);
lean_closure_set(v___f_756_, 5, v_inst_704_);
lean_closure_set(v___f_756_, 6, v_inst_705_);
lean_closure_set(v___f_756_, 7, v_toVar_706_);
lean_closure_set(v___f_756_, 8, v_asVar_707_);
lean_closure_set(v___f_756_, 9, v_arg_719_);
lean_closure_set(v___f_756_, 10, v_toBind_708_);
lean_closure_set(v___f_756_, 11, v___f_755_);
v___x_757_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_inst_704_, v_inst_705_, v_arg_723_);
v___x_758_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_757_, v___f_756_);
return v___x_758_;
}
}
else
{
lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec_ref(v___x_741_);
lean_dec(v_toTopVar_698_);
lean_inc_n(v_toBind_708_, 2);
lean_inc(v_asVar_707_);
lean_inc(v_toVar_706_);
lean_inc_ref_n(v_inst_705_, 2);
lean_inc_ref_n(v_inst_704_, 2);
lean_inc_ref_n(v_inst_703_, 2);
lean_inc_ref_n(v_inst_702_, 2);
lean_inc_n(v_inst_701_, 2);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14), 11, 10);
lean_closure_set(v___f_759_, 0, v_toPure_700_);
lean_closure_set(v___f_759_, 1, v_inst_701_);
lean_closure_set(v___f_759_, 2, v_inst_702_);
lean_closure_set(v___f_759_, 3, v_inst_703_);
lean_closure_set(v___f_759_, 4, v_inst_704_);
lean_closure_set(v___f_759_, 5, v_inst_705_);
lean_closure_set(v___f_759_, 6, v_toVar_706_);
lean_closure_set(v___f_759_, 7, v_asVar_707_);
lean_closure_set(v___f_759_, 8, v_arg_715_);
lean_closure_set(v___f_759_, 9, v_toBind_708_);
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_760_, 0, v_asTopVar_709_);
lean_closure_set(v___f_760_, 1, v_e_699_);
lean_closure_set(v___f_760_, 2, v_inst_701_);
lean_closure_set(v___f_760_, 3, v_inst_702_);
lean_closure_set(v___f_760_, 4, v_inst_703_);
lean_closure_set(v___f_760_, 5, v_inst_704_);
lean_closure_set(v___f_760_, 6, v_inst_705_);
lean_closure_set(v___f_760_, 7, v_toVar_706_);
lean_closure_set(v___f_760_, 8, v_asVar_707_);
lean_closure_set(v___f_760_, 9, v_arg_719_);
lean_closure_set(v___f_760_, 10, v_toBind_708_);
lean_closure_set(v___f_760_, 11, v___f_759_);
v___x_761_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_inst_704_, v_inst_705_, v_arg_723_);
v___x_762_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_761_, v___f_760_);
return v___x_762_;
}
}
else
{
lean_object* v___x_763_; 
lean_dec_ref(v___x_741_);
lean_dec(v_toTopVar_698_);
v___x_763_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_715_);
if (lean_obj_tag(v___x_763_) == 1)
{
lean_object* v_val_764_; lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_val_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_val_764_);
lean_dec_ref_known(v___x_763_, 1);
v___f_765_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17), 3, 2);
lean_closure_set(v___f_765_, 0, v_val_764_);
lean_closure_set(v___f_765_, 1, v_toPure_700_);
lean_inc(v_toBind_708_);
lean_inc_ref(v_inst_705_);
lean_inc_ref(v_inst_704_);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
lean_inc(v_inst_701_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_766_, 0, v_asTopVar_709_);
lean_closure_set(v___f_766_, 1, v_e_699_);
lean_closure_set(v___f_766_, 2, v_inst_701_);
lean_closure_set(v___f_766_, 3, v_inst_702_);
lean_closure_set(v___f_766_, 4, v_inst_703_);
lean_closure_set(v___f_766_, 5, v_inst_704_);
lean_closure_set(v___f_766_, 6, v_inst_705_);
lean_closure_set(v___f_766_, 7, v_toVar_706_);
lean_closure_set(v___f_766_, 8, v_asVar_707_);
lean_closure_set(v___f_766_, 9, v_arg_719_);
lean_closure_set(v___f_766_, 10, v_toBind_708_);
lean_closure_set(v___f_766_, 11, v___f_765_);
v___x_767_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_inst_704_, v_inst_705_, v_arg_723_);
v___x_768_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_767_, v___f_766_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; 
lean_dec(v___x_763_);
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_719_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toPure_700_);
v___x_769_ = lean_apply_1(v_asTopVar_709_, v_e_699_);
return v___x_769_;
}
}
}
}
}
}
else
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref(v___x_724_);
lean_dec_ref(v_arg_723_);
lean_dec(v_toPure_700_);
lean_dec(v_toTopVar_698_);
lean_inc(v_toBind_708_);
lean_inc_ref(v_inst_705_);
lean_inc_ref(v_inst_704_);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
lean_inc(v_inst_701_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_770_, 0, v_asTopVar_709_);
lean_closure_set(v___f_770_, 1, v_e_699_);
lean_closure_set(v___f_770_, 2, v_inst_701_);
lean_closure_set(v___f_770_, 3, v_inst_702_);
lean_closure_set(v___f_770_, 4, v_inst_703_);
lean_closure_set(v___f_770_, 5, v_inst_704_);
lean_closure_set(v___f_770_, 6, v_inst_705_);
lean_closure_set(v___f_770_, 7, v_toVar_706_);
lean_closure_set(v___f_770_, 8, v_asVar_707_);
lean_closure_set(v___f_770_, 9, v_arg_715_);
lean_closure_set(v___f_770_, 10, v_toBind_708_);
lean_closure_set(v___f_770_, 11, v___f_710_);
v___x_771_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_inst_704_, v_inst_705_, v_arg_719_);
v___x_772_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_771_, v___f_770_);
return v___x_772_;
}
}
else
{
lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec_ref(v___x_724_);
lean_dec_ref(v_arg_723_);
lean_dec(v___f_710_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_702_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed), 6, 5);
lean_closure_set(v___f_773_, 0, v_asTopVar_709_);
lean_closure_set(v___f_773_, 1, v_e_699_);
lean_closure_set(v___f_773_, 2, v_arg_715_);
lean_closure_set(v___f_773_, 3, v_toPure_700_);
lean_closure_set(v___f_773_, 4, v_toTopVar_698_);
v___x_774_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_701_, v_inst_703_, v_inst_704_, v_inst_705_, v_arg_719_);
v___x_775_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_774_, v___f_773_);
return v___x_775_;
}
}
else
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v___x_724_);
lean_dec_ref(v_arg_723_);
lean_dec(v___f_710_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_702_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed), 6, 5);
lean_closure_set(v___f_776_, 0, v_asTopVar_709_);
lean_closure_set(v___f_776_, 1, v_e_699_);
lean_closure_set(v___f_776_, 2, v_arg_715_);
lean_closure_set(v___f_776_, 3, v_toPure_700_);
lean_closure_set(v___f_776_, 4, v_toTopVar_698_);
v___x_777_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_701_, v_inst_703_, v_inst_704_, v_inst_705_, v_arg_719_);
v___x_778_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_777_, v___f_776_);
return v___x_778_;
}
}
else
{
lean_dec_ref(v___x_724_);
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_715_);
lean_dec(v___f_710_);
lean_dec(v_toBind_708_);
lean_dec(v_asVar_707_);
lean_dec(v_toVar_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
lean_dec(v_toTopVar_698_);
if (lean_obj_tag(v_arg_719_) == 9)
{
lean_object* v_a_779_; 
v_a_779_ = lean_ctor_get(v_arg_719_, 0);
lean_inc_ref(v_a_779_);
lean_dec_ref_known(v_arg_719_, 1);
if (lean_obj_tag(v_a_779_) == 0)
{
lean_object* v_val_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_asTopVar_709_);
lean_dec_ref(v_e_699_);
v_val_780_ = lean_ctor_get(v_a_779_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_790_ == 0)
{
v___x_782_ = v_a_779_;
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_val_780_);
lean_dec(v_a_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_nat_to_int(v_val_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_789_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
v___x_788_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_787_);
return v___x_788_;
}
}
}
else
{
lean_object* v___x_791_; 
lean_dec_ref(v_a_779_);
lean_dec(v_toPure_700_);
v___x_791_ = lean_apply_1(v_asTopVar_709_, v_e_699_);
return v___x_791_;
}
}
else
{
lean_object* v___x_792_; 
lean_dec_ref(v_arg_719_);
lean_dec(v_toPure_700_);
v___x_792_ = lean_apply_1(v_asTopVar_709_, v_e_699_);
return v___x_792_;
}
}
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_e_800_, uint8_t v_skipVar_801_){
_start:
{
lean_object* v_toApplicative_802_; lean_object* v_toBind_803_; lean_object* v_toPure_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v_asVar_808_; lean_object* v_toVar_809_; lean_object* v___x_810_; lean_object* v_toTopVar_811_; lean_object* v_asTopVar_812_; lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_toApplicative_802_ = lean_ctor_get(v_inst_796_, 0);
v_toBind_803_ = lean_ctor_get(v_inst_796_, 1);
lean_inc_n(v_toBind_803_, 6);
v_toPure_804_ = lean_ctor_get(v_toApplicative_802_, 1);
lean_inc_n(v_toPure_804_, 5);
v___f_805_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_805_, 0, v_toPure_804_);
v___f_806_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_806_, 0, v_toPure_804_);
v___f_807_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_807_, 0, v_toPure_804_);
lean_inc(v_inst_793_);
lean_inc_ref(v___f_807_);
lean_inc(v_inst_799_);
v_asVar_808_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4), 5, 4);
lean_closure_set(v_asVar_808_, 0, v_inst_799_);
lean_closure_set(v_asVar_808_, 1, v_toBind_803_);
lean_closure_set(v_asVar_808_, 2, v___f_807_);
lean_closure_set(v_asVar_808_, 3, v_inst_793_);
v_toVar_809_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6), 4, 3);
lean_closure_set(v_toVar_809_, 0, v_inst_799_);
lean_closure_set(v_toVar_809_, 1, v_toBind_803_);
lean_closure_set(v_toVar_809_, 2, v___f_807_);
v___x_810_ = lean_box(v_skipVar_801_);
lean_inc_ref(v_toVar_809_);
v_toTopVar_811_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v_toTopVar_811_, 0, v___x_810_);
lean_closure_set(v_toTopVar_811_, 1, v_toVar_809_);
lean_closure_set(v_toTopVar_811_, 2, v_toBind_803_);
lean_closure_set(v_toTopVar_811_, 3, v___f_806_);
lean_closure_set(v_toTopVar_811_, 4, v_toPure_804_);
lean_inc_ref(v_toTopVar_811_);
v_asTopVar_812_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8), 4, 3);
lean_closure_set(v_asTopVar_812_, 0, v_toTopVar_811_);
lean_closure_set(v_asTopVar_812_, 1, v_inst_793_);
lean_closure_set(v_asTopVar_812_, 2, v_toBind_803_);
lean_inc(v_inst_794_);
lean_inc_ref(v_e_800_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18), 14, 13);
lean_closure_set(v___f_813_, 0, v_toTopVar_811_);
lean_closure_set(v___f_813_, 1, v_e_800_);
lean_closure_set(v___f_813_, 2, v_toPure_804_);
lean_closure_set(v___f_813_, 3, v_inst_794_);
lean_closure_set(v___f_813_, 4, v_inst_795_);
lean_closure_set(v___f_813_, 5, v_inst_796_);
lean_closure_set(v___f_813_, 6, v_inst_797_);
lean_closure_set(v___f_813_, 7, v_inst_798_);
lean_closure_set(v___f_813_, 8, v_toVar_809_);
lean_closure_set(v___f_813_, 9, v_asVar_808_);
lean_closure_set(v___f_813_, 10, v_toBind_803_);
lean_closure_set(v___f_813_, 11, v_asTopVar_812_);
lean_closure_set(v___f_813_, 12, v___f_805_);
v___x_814_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_814_, 0, v_e_800_);
v___x_815_ = lean_apply_2(v_inst_794_, lean_box(0), v___x_814_);
v___x_816_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_815_, v___f_813_);
return v___x_816_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_793_ = stack[0].m_obj;
lean_object* v_inst_794_ = stack[1].m_obj;
lean_object* v_inst_795_ = stack[2].m_obj;
lean_object* v_inst_796_ = stack[3].m_obj;
lean_object* v_inst_797_ = stack[4].m_obj;
lean_object* v_inst_798_ = stack[5].m_obj;
lean_object* v_inst_799_ = stack[6].m_obj;
lean_object* v_e_800_ = stack[7].m_obj;
uint8_t v_skipVar_801_ = stack[8].m_num;
lean_object* v_res_817_;
v_res_817_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_793_, v_inst_794_, v_inst_795_, v_inst_796_, v_inst_797_, v_inst_798_, v_inst_799_, v_e_800_, v_skipVar_801_);
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___boxed(lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_e_825_, lean_object* v_skipVar_826_){
_start:
{
uint8_t v_skipVar_boxed_827_; lean_object* v_res_828_; 
v_skipVar_boxed_827_ = lean_unbox(v_skipVar_826_);
v_res_828_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_818_, v_inst_819_, v_inst_820_, v_inst_821_, v_inst_822_, v_inst_823_, v_inst_824_, v_e_825_, v_skipVar_boxed_827_);
return v_res_828_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f(lean_object* v_m_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_e_837_, uint8_t v_skipVar_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_830_, v_inst_831_, v_inst_832_, v_inst_833_, v_inst_834_, v_inst_835_, v_inst_836_, v_e_837_, v_skipVar_838_);
return v___x_839_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_reifyRing_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_830_ = stack[1].m_obj;
lean_object* v_inst_831_ = stack[2].m_obj;
lean_object* v_inst_832_ = stack[3].m_obj;
lean_object* v_inst_833_ = stack[4].m_obj;
lean_object* v_inst_834_ = stack[5].m_obj;
lean_object* v_inst_835_ = stack[6].m_obj;
lean_object* v_inst_836_ = stack[7].m_obj;
lean_object* v_e_837_ = stack[8].m_obj;
uint8_t v_skipVar_838_ = stack[9].m_num;
lean_object* v_res_840_;
v_res_840_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f(lean_box(0), v_inst_830_, v_inst_831_, v_inst_832_, v_inst_833_, v_inst_834_, v_inst_835_, v_inst_836_, v_e_837_, v_skipVar_838_);
stack->m_obj
 = v_res_840_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___boxed(lean_object* v_m_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_e_849_, lean_object* v_skipVar_850_){
_start:
{
uint8_t v_skipVar_boxed_851_; lean_object* v_res_852_; 
v_skipVar_boxed_851_ = lean_unbox(v_skipVar_850_);
v_res_852_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f(v_m_841_, v_inst_842_, v_inst_843_, v_inst_844_, v_inst_845_, v_inst_846_, v_inst_847_, v_inst_848_, v_e_849_, v_skipVar_boxed_851_);
return v_res_852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(lean_object* v_inst_856_, lean_object* v_e_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_858_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1, &l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1);
v___x_859_ = l_Lean_indentExpr(v_e_857_);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_reportIssueIfVerbose___boxed), 8, 1);
lean_closure_set(v___x_861_, 0, v___x_860_);
v___x_862_ = lean_apply_2(v_inst_856_, lean_box(0), v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue(lean_object* v_m_863_, lean_object* v_inst_864_, lean_object* v_e_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_864_, v_e_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(lean_object* v_arg_867_, lean_object* v_asVar_868_, lean_object* v_e_869_, lean_object* v_arg_870_, lean_object* v_toPure_871_, lean_object* v_toVar_872_, lean_object* v_____do__lift_873_){
_start:
{
lean_object* v___x_874_; size_t v___x_875_; size_t v___x_876_; uint8_t v___x_877_; 
v___x_874_ = l_Lean_Expr_appArg_x21(v_____do__lift_873_);
v___x_875_ = lean_ptr_addr(v___x_874_);
lean_dec_ref(v___x_874_);
v___x_876_ = lean_ptr_addr(v_arg_867_);
v___x_877_ = lean_usize_dec_eq(v___x_875_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec(v_toVar_872_);
lean_dec(v_toPure_871_);
lean_dec_ref(v_arg_870_);
v___x_878_ = lean_apply_1(v_asVar_868_, v_e_869_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; 
lean_dec(v_asVar_868_);
v___x_879_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_870_);
if (lean_obj_tag(v___x_879_) == 1)
{
lean_object* v_val_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_889_; 
lean_dec(v_toVar_872_);
lean_dec_ref(v_e_869_);
v_val_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_889_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_val_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_nat_to_int(v_val_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set_tag(v___x_882_, 0);
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = lean_apply_2(v_toPure_871_, lean_box(0), v___x_886_);
return v___x_887_;
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec(v___x_879_);
lean_dec(v_toPure_871_);
v___x_890_ = lean_apply_1(v_toVar_872_, v_e_869_);
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed(lean_object* v_arg_891_, lean_object* v_asVar_892_, lean_object* v_e_893_, lean_object* v_arg_894_, lean_object* v_toPure_895_, lean_object* v_toVar_896_, lean_object* v_____do__lift_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(v_arg_891_, v_asVar_892_, v_e_893_, v_arg_894_, v_toPure_895_, v_toVar_896_, v_____do__lift_897_);
lean_dec_ref(v_____do__lift_897_);
lean_dec_ref(v_arg_891_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(lean_object* v_arg_899_, lean_object* v_asVar_900_, lean_object* v_e_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_toVar_907_, lean_object* v_arg_908_, lean_object* v_toBind_909_, lean_object* v___f_910_, lean_object* v_____do__lift_911_){
_start:
{
lean_object* v___x_912_; size_t v___x_913_; size_t v___x_914_; uint8_t v___x_915_; 
v___x_912_ = l_Lean_Expr_appArg_x21(v_____do__lift_911_);
v___x_913_ = lean_ptr_addr(v___x_912_);
lean_dec_ref(v___x_912_);
v___x_914_ = lean_ptr_addr(v_arg_899_);
v___x_915_ = lean_usize_dec_eq(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_dec(v___f_910_);
lean_dec(v_toBind_909_);
lean_dec_ref(v_arg_908_);
lean_dec(v_toVar_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v_inst_904_);
lean_dec_ref(v_inst_903_);
lean_dec(v_inst_902_);
v___x_916_ = lean_apply_1(v_asVar_900_, v_e_901_);
return v___x_916_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref(v_e_901_);
v___x_917_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_902_, v_inst_903_, v_inst_904_, v_inst_905_, v_inst_906_, v_toVar_907_, v_asVar_900_, v_arg_908_);
v___x_918_ = lean_apply_4(v_toBind_909_, lean_box(0), lean_box(0), v___x_917_, v___f_910_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed(lean_object* v_arg_919_, lean_object* v_asVar_920_, lean_object* v_e_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_toVar_927_, lean_object* v_arg_928_, lean_object* v_toBind_929_, lean_object* v___f_930_, lean_object* v_____do__lift_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(v_arg_919_, v_asVar_920_, v_e_921_, v_inst_922_, v_inst_923_, v_inst_924_, v_inst_925_, v_inst_926_, v_toVar_927_, v_arg_928_, v_toBind_929_, v___f_930_, v_____do__lift_931_);
lean_dec_ref(v_____do__lift_931_);
lean_dec_ref(v_arg_919_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3(lean_object* v_toPure_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_toVar_939_, lean_object* v_asVar_940_, lean_object* v_arg_941_, lean_object* v_toBind_942_, lean_object* v_____do__lift_943_){
_start:
{
lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___f_944_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_944_, 0, v_____do__lift_943_);
lean_closure_set(v___f_944_, 1, v_toPure_933_);
v___x_945_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_934_, v_inst_935_, v_inst_936_, v_inst_937_, v_inst_938_, v_toVar_939_, v_asVar_940_, v_arg_941_);
v___x_946_ = lean_apply_4(v_toBind_942_, lean_box(0), lean_box(0), v___x_945_, v___f_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2(lean_object* v_toVar_947_, lean_object* v_e_948_, lean_object* v_toPure_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_asVar_955_, lean_object* v_toBind_956_, lean_object* v_____x_957_){
_start:
{
lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_958_ = l_Lean_Expr_cleanupAnnotations(v_____x_957_);
v___x_959_ = l_Lean_Expr_isApp(v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec_ref(v___x_958_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec(v_toPure_949_);
v___x_960_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_960_;
}
else
{
lean_object* v_arg_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_arg_961_ = lean_ctor_get(v___x_958_, 1);
lean_inc_ref(v_arg_961_);
v___x_962_ = l_Lean_Expr_appFnCleanup___redArg(v___x_958_);
v___x_963_ = l_Lean_Expr_isApp(v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec_ref(v___x_962_);
lean_dec_ref(v_arg_961_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec(v_toPure_949_);
v___x_964_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_964_;
}
else
{
lean_object* v_arg_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_arg_965_ = lean_ctor_get(v___x_962_, 1);
lean_inc_ref(v_arg_965_);
v___x_966_ = l_Lean_Expr_appFnCleanup___redArg(v___x_962_);
v___x_967_ = l_Lean_Expr_isApp(v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_dec_ref(v___x_966_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_961_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec(v_toPure_949_);
v___x_968_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_968_;
}
else
{
lean_object* v_arg_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_arg_969_ = lean_ctor_get(v___x_966_, 1);
lean_inc_ref(v_arg_969_);
v___x_970_ = l_Lean_Expr_appFnCleanup___redArg(v___x_966_);
v___x_971_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_972_ = l_Lean_Expr_isConstOf(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_974_ = l_Lean_Expr_isConstOf(v___x_970_, v___x_973_);
if (v___x_974_ == 0)
{
uint8_t v___x_975_; 
v___x_975_ = l_Lean_Expr_isApp(v___x_970_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_dec_ref(v___x_970_);
lean_dec_ref(v_arg_969_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_961_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec(v_toPure_949_);
v___x_976_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_970_);
v___x_978_ = l_Lean_Expr_isApp(v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_dec_ref(v___x_977_);
lean_dec_ref(v_arg_969_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_961_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec(v_toPure_949_);
v___x_979_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_977_);
v___x_981_ = l_Lean_Expr_isApp(v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_dec_ref(v___x_980_);
lean_dec_ref(v_arg_969_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_961_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec(v_toPure_949_);
v___x_982_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_980_);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_985_ = l_Lean_Expr_isConstOf(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_987_ = l_Lean_Expr_isConstOf(v___x_983_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_989_ = l_Lean_Expr_isConstOf(v___x_983_, v___x_988_);
lean_dec_ref(v___x_983_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; 
lean_dec_ref(v_arg_969_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_961_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec(v_toPure_949_);
v___x_990_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_990_;
}
else
{
lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_inc_n(v_toBind_956_, 2);
lean_inc(v_asVar_955_);
lean_inc(v_toVar_947_);
lean_inc_ref_n(v_inst_954_, 2);
lean_inc_ref_n(v_inst_953_, 2);
lean_inc_ref_n(v_inst_952_, 2);
lean_inc_ref_n(v_inst_951_, 2);
lean_inc_n(v_inst_950_, 2);
v___f_991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_991_, 0, v_toPure_949_);
lean_closure_set(v___f_991_, 1, v_inst_950_);
lean_closure_set(v___f_991_, 2, v_inst_951_);
lean_closure_set(v___f_991_, 3, v_inst_952_);
lean_closure_set(v___f_991_, 4, v_inst_953_);
lean_closure_set(v___f_991_, 5, v_inst_954_);
lean_closure_set(v___f_991_, 6, v_toVar_947_);
lean_closure_set(v___f_991_, 7, v_asVar_955_);
lean_closure_set(v___f_991_, 8, v_arg_961_);
lean_closure_set(v___f_991_, 9, v_toBind_956_);
v___f_992_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_992_, 0, v_arg_969_);
lean_closure_set(v___f_992_, 1, v_asVar_955_);
lean_closure_set(v___f_992_, 2, v_e_948_);
lean_closure_set(v___f_992_, 3, v_inst_950_);
lean_closure_set(v___f_992_, 4, v_inst_951_);
lean_closure_set(v___f_992_, 5, v_inst_952_);
lean_closure_set(v___f_992_, 6, v_inst_953_);
lean_closure_set(v___f_992_, 7, v_inst_954_);
lean_closure_set(v___f_992_, 8, v_toVar_947_);
lean_closure_set(v___f_992_, 9, v_arg_965_);
lean_closure_set(v___f_992_, 10, v_toBind_956_);
lean_closure_set(v___f_992_, 11, v___f_991_);
v___x_993_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_950_, v_inst_951_, v_inst_952_, v_inst_953_, v_inst_954_);
v___x_994_ = lean_apply_4(v_toBind_956_, lean_box(0), lean_box(0), v___x_993_, v___f_992_);
return v___x_994_;
}
}
else
{
lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref(v___x_983_);
lean_inc_n(v_toBind_956_, 2);
lean_inc(v_asVar_955_);
lean_inc(v_toVar_947_);
lean_inc_ref_n(v_inst_954_, 2);
lean_inc_ref_n(v_inst_953_, 2);
lean_inc_ref_n(v_inst_952_, 2);
lean_inc_ref_n(v_inst_951_, 2);
lean_inc_n(v_inst_950_, 2);
v___f_995_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3), 11, 10);
lean_closure_set(v___f_995_, 0, v_toPure_949_);
lean_closure_set(v___f_995_, 1, v_inst_950_);
lean_closure_set(v___f_995_, 2, v_inst_951_);
lean_closure_set(v___f_995_, 3, v_inst_952_);
lean_closure_set(v___f_995_, 4, v_inst_953_);
lean_closure_set(v___f_995_, 5, v_inst_954_);
lean_closure_set(v___f_995_, 6, v_toVar_947_);
lean_closure_set(v___f_995_, 7, v_asVar_955_);
lean_closure_set(v___f_995_, 8, v_arg_961_);
lean_closure_set(v___f_995_, 9, v_toBind_956_);
v___f_996_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_996_, 0, v_arg_969_);
lean_closure_set(v___f_996_, 1, v_asVar_955_);
lean_closure_set(v___f_996_, 2, v_e_948_);
lean_closure_set(v___f_996_, 3, v_inst_950_);
lean_closure_set(v___f_996_, 4, v_inst_951_);
lean_closure_set(v___f_996_, 5, v_inst_952_);
lean_closure_set(v___f_996_, 6, v_inst_953_);
lean_closure_set(v___f_996_, 7, v_inst_954_);
lean_closure_set(v___f_996_, 8, v_toVar_947_);
lean_closure_set(v___f_996_, 9, v_arg_965_);
lean_closure_set(v___f_996_, 10, v_toBind_956_);
lean_closure_set(v___f_996_, 11, v___f_995_);
v___x_997_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_950_, v_inst_951_, v_inst_952_, v_inst_953_, v_inst_954_);
v___x_998_ = lean_apply_4(v_toBind_956_, lean_box(0), lean_box(0), v___x_997_, v___f_996_);
return v___x_998_;
}
}
else
{
lean_object* v___x_999_; 
lean_dec_ref(v___x_983_);
v___x_999_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_961_);
if (lean_obj_tag(v___x_999_) == 1)
{
lean_object* v_val_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_val_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_val_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___f_1001_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9), 3, 2);
lean_closure_set(v___f_1001_, 0, v_val_1000_);
lean_closure_set(v___f_1001_, 1, v_toPure_949_);
lean_inc(v_toBind_956_);
lean_inc_ref(v_inst_954_);
lean_inc_ref(v_inst_953_);
lean_inc_ref(v_inst_952_);
lean_inc_ref(v_inst_951_);
lean_inc(v_inst_950_);
v___f_1002_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_1002_, 0, v_arg_969_);
lean_closure_set(v___f_1002_, 1, v_asVar_955_);
lean_closure_set(v___f_1002_, 2, v_e_948_);
lean_closure_set(v___f_1002_, 3, v_inst_950_);
lean_closure_set(v___f_1002_, 4, v_inst_951_);
lean_closure_set(v___f_1002_, 5, v_inst_952_);
lean_closure_set(v___f_1002_, 6, v_inst_953_);
lean_closure_set(v___f_1002_, 7, v_inst_954_);
lean_closure_set(v___f_1002_, 8, v_toVar_947_);
lean_closure_set(v___f_1002_, 9, v_arg_965_);
lean_closure_set(v___f_1002_, 10, v_toBind_956_);
lean_closure_set(v___f_1002_, 11, v___f_1001_);
v___x_1003_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_950_, v_inst_951_, v_inst_952_, v_inst_953_, v_inst_954_);
v___x_1004_ = lean_apply_4(v_toBind_956_, lean_box(0), lean_box(0), v___x_1003_, v___f_1002_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; 
lean_dec(v___x_999_);
lean_dec_ref(v_arg_969_);
lean_dec_ref(v_arg_965_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec(v_toPure_949_);
v___x_1005_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_1005_;
}
}
}
}
}
}
else
{
lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v___x_970_);
lean_dec_ref(v_arg_969_);
lean_dec_ref(v_inst_951_);
v___f_1006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_1006_, 0, v_arg_965_);
lean_closure_set(v___f_1006_, 1, v_asVar_955_);
lean_closure_set(v___f_1006_, 2, v_e_948_);
lean_closure_set(v___f_1006_, 3, v_arg_961_);
lean_closure_set(v___f_1006_, 4, v_toPure_949_);
lean_closure_set(v___f_1006_, 5, v_toVar_947_);
v___x_1007_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_950_, v_inst_952_, v_inst_953_, v_inst_954_);
v___x_1008_ = lean_apply_4(v_toBind_956_, lean_box(0), lean_box(0), v___x_1007_, v___f_1006_);
return v___x_1008_;
}
}
else
{
lean_dec_ref(v___x_970_);
lean_dec_ref(v_arg_969_);
lean_dec_ref(v_arg_961_);
lean_dec(v_toBind_956_);
lean_dec(v_asVar_955_);
lean_dec_ref(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec_ref(v_inst_951_);
lean_dec(v_inst_950_);
if (lean_obj_tag(v_arg_965_) == 9)
{
lean_object* v_a_1009_; 
v_a_1009_ = lean_ctor_get(v_arg_965_, 0);
lean_inc_ref(v_a_1009_);
lean_dec_ref_known(v_arg_965_, 1);
if (lean_obj_tag(v_a_1009_) == 0)
{
lean_object* v_val_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_e_948_);
lean_dec(v_toVar_947_);
v_val_1010_ = lean_ctor_get(v_a_1009_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1012_ = v_a_1009_;
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_val_1010_);
lean_dec(v_a_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = lean_nat_to_int(v_val_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1014_);
v___x_1016_ = v___x_1012_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_apply_2(v_toPure_949_, lean_box(0), v___x_1016_);
return v___x_1017_;
}
}
}
else
{
lean_object* v___x_1020_; 
lean_dec_ref(v_a_1009_);
lean_dec(v_toPure_949_);
v___x_1020_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_1020_;
}
}
else
{
lean_object* v___x_1021_; 
lean_dec_ref(v_arg_965_);
lean_dec(v_toPure_949_);
v___x_1021_ = lean_apply_1(v_toVar_947_, v_e_948_);
return v___x_1021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_toVar_1027_, lean_object* v_asVar_1028_, lean_object* v_e_1029_){
_start:
{
lean_object* v_toApplicative_1030_; lean_object* v_toBind_1031_; lean_object* v_toPure_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; 
v_toApplicative_1030_ = lean_ctor_get(v_inst_1024_, 0);
v_toBind_1031_ = lean_ctor_get(v_inst_1024_, 1);
lean_inc_n(v_toBind_1031_, 2);
v_toPure_1032_ = lean_ctor_get(v_toApplicative_1030_, 1);
lean_inc(v_toPure_1032_);
lean_inc_ref(v_e_1029_);
v___x_1033_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_1033_, 0, v_e_1029_);
lean_inc(v_inst_1022_);
v___x_1034_ = lean_apply_2(v_inst_1022_, lean_box(0), v___x_1033_);
v___f_1035_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1035_, 0, v_toVar_1027_);
lean_closure_set(v___f_1035_, 1, v_e_1029_);
lean_closure_set(v___f_1035_, 2, v_toPure_1032_);
lean_closure_set(v___f_1035_, 3, v_inst_1022_);
lean_closure_set(v___f_1035_, 4, v_inst_1023_);
lean_closure_set(v___f_1035_, 5, v_inst_1024_);
lean_closure_set(v___f_1035_, 6, v_inst_1025_);
lean_closure_set(v___f_1035_, 7, v_inst_1026_);
lean_closure_set(v___f_1035_, 8, v_asVar_1028_);
lean_closure_set(v___f_1035_, 9, v_toBind_1031_);
v___x_1036_ = lean_apply_4(v_toBind_1031_, lean_box(0), lean_box(0), v___x_1034_, v___f_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1(lean_object* v_toPure_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_toVar_1043_, lean_object* v_asVar_1044_, lean_object* v_arg_1045_, lean_object* v_toBind_1046_, lean_object* v_____do__lift_1047_){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___f_1048_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1048_, 0, v_____do__lift_1047_);
lean_closure_set(v___f_1048_, 1, v_toPure_1037_);
v___x_1049_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1038_, v_inst_1039_, v_inst_1040_, v_inst_1041_, v_inst_1042_, v_toVar_1043_, v_asVar_1044_, v_arg_1045_);
v___x_1050_ = lean_apply_4(v_toBind_1046_, lean_box(0), lean_box(0), v___x_1049_, v___f_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go(lean_object* v_m_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_toVar_1057_, lean_object* v_asVar_1058_, lean_object* v_e_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1052_, v_inst_1053_, v_inst_1054_, v_inst_1055_, v_inst_1056_, v_toVar_1057_, v_asVar_1058_, v_e_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3(lean_object* v_inst_1061_, lean_object* v_toBind_1062_, lean_object* v___f_1063_, lean_object* v_inst_1064_, lean_object* v_e_1065_){
_start:
{
lean_object* v___f_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_inc(v_toBind_1062_);
lean_inc_ref(v_e_1065_);
v___f_1066_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1066_, 0, v_inst_1061_);
lean_closure_set(v___f_1066_, 1, v_e_1065_);
lean_closure_set(v___f_1066_, 2, v_toBind_1062_);
lean_closure_set(v___f_1066_, 3, v___f_1063_);
v___x_1067_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_1064_, v_e_1065_);
v___x_1068_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v___x_1067_, v___f_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2(lean_object* v_toVar_1069_, lean_object* v_toBind_1070_, lean_object* v___f_1071_, lean_object* v_e_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_apply_1(v_toVar_1069_, v_e_1072_);
v___x_1074_ = lean_apply_4(v_toBind_1070_, lean_box(0), lean_box(0), v___x_1073_, v___f_1071_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1(lean_object* v_toTopVar_1075_, lean_object* v_inst_1076_, lean_object* v_toBind_1077_, lean_object* v_e_1078_){
_start:
{
lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_inc_ref(v_e_1078_);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1079_, 0, v_toTopVar_1075_);
lean_closure_set(v___f_1079_, 1, v_e_1078_);
v___x_1080_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_1076_, v_e_1078_);
v___x_1081_ = lean_apply_4(v_toBind_1077_, lean_box(0), lean_box(0), v___x_1080_, v___f_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4(lean_object* v_toPure_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_toVar_1088_, lean_object* v_asVar_1089_, lean_object* v_arg_1090_, lean_object* v_toBind_1091_, lean_object* v_____do__lift_1092_){
_start:
{
lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9), 3, 2);
lean_closure_set(v___f_1093_, 0, v_____do__lift_1092_);
lean_closure_set(v___f_1093_, 1, v_toPure_1082_);
v___x_1094_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1083_, v_inst_1084_, v_inst_1085_, v_inst_1086_, v_inst_1087_, v_toVar_1088_, v_asVar_1089_, v_arg_1090_);
v___x_1095_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v___x_1094_, v___f_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(lean_object* v_arg_1096_, lean_object* v_asTopVar_1097_, lean_object* v_e_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_toVar_1104_, lean_object* v_asVar_1105_, lean_object* v_arg_1106_, lean_object* v_toBind_1107_, lean_object* v___f_1108_, lean_object* v_____do__lift_1109_){
_start:
{
lean_object* v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1110_ = l_Lean_Expr_appArg_x21(v_____do__lift_1109_);
v___x_1111_ = lean_ptr_addr(v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = lean_ptr_addr(v_arg_1096_);
v___x_1113_ = lean_usize_dec_eq(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec(v___f_1108_);
lean_dec(v_toBind_1107_);
lean_dec_ref(v_arg_1106_);
lean_dec(v_asVar_1105_);
lean_dec(v_toVar_1104_);
lean_dec_ref(v_inst_1103_);
lean_dec_ref(v_inst_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_inst_1100_);
lean_dec(v_inst_1099_);
v___x_1114_ = lean_apply_1(v_asTopVar_1097_, v_e_1098_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec_ref(v_e_1098_);
lean_dec(v_asTopVar_1097_);
v___x_1115_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1099_, v_inst_1100_, v_inst_1101_, v_inst_1102_, v_inst_1103_, v_toVar_1104_, v_asVar_1105_, v_arg_1106_);
v___x_1116_ = lean_apply_4(v_toBind_1107_, lean_box(0), lean_box(0), v___x_1115_, v___f_1108_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed(lean_object* v_arg_1117_, lean_object* v_asTopVar_1118_, lean_object* v_e_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_toVar_1125_, lean_object* v_asVar_1126_, lean_object* v_arg_1127_, lean_object* v_toBind_1128_, lean_object* v___f_1129_, lean_object* v_____do__lift_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(v_arg_1117_, v_asTopVar_1118_, v_e_1119_, v_inst_1120_, v_inst_1121_, v_inst_1122_, v_inst_1123_, v_inst_1124_, v_toVar_1125_, v_asVar_1126_, v_arg_1127_, v_toBind_1128_, v___f_1129_, v_____do__lift_1130_);
lean_dec_ref(v_____do__lift_1130_);
lean_dec_ref(v_arg_1117_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6(lean_object* v_toPure_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_toVar_1138_, lean_object* v_asVar_1139_, lean_object* v_arg_1140_, lean_object* v_toBind_1141_, lean_object* v_____do__lift_1142_){
_start:
{
lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___f_1143_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12), 3, 2);
lean_closure_set(v___f_1143_, 0, v_____do__lift_1142_);
lean_closure_set(v___f_1143_, 1, v_toPure_1132_);
v___x_1144_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1133_, v_inst_1134_, v_inst_1135_, v_inst_1136_, v_inst_1137_, v_toVar_1138_, v_asVar_1139_, v_arg_1140_);
v___x_1145_ = lean_apply_4(v_toBind_1141_, lean_box(0), lean_box(0), v___x_1144_, v___f_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(lean_object* v_arg_1146_, lean_object* v_asTopVar_1147_, lean_object* v_e_1148_, lean_object* v_arg_1149_, lean_object* v_toPure_1150_, lean_object* v_toTopVar_1151_, lean_object* v_____do__lift_1152_){
_start:
{
lean_object* v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1153_ = l_Lean_Expr_appArg_x21(v_____do__lift_1152_);
v___x_1154_ = lean_ptr_addr(v___x_1153_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = lean_ptr_addr(v_arg_1146_);
v___x_1156_ = lean_usize_dec_eq(v___x_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v_toTopVar_1151_);
lean_dec(v_toPure_1150_);
lean_dec_ref(v_arg_1149_);
v___x_1157_ = lean_apply_1(v_asTopVar_1147_, v_e_1148_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; 
lean_dec(v_asTopVar_1147_);
v___x_1158_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1149_);
if (lean_obj_tag(v___x_1158_) == 1)
{
lean_object* v_val_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_toTopVar_1151_);
lean_dec_ref(v_e_1148_);
v_val_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1169_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_val_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1169_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1163_ = lean_nat_to_int(v_val_1159_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1164_);
v___x_1166_ = v___x_1161_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1166_);
return v___x_1167_;
}
}
}
else
{
lean_object* v___x_1170_; 
lean_dec(v___x_1158_);
lean_dec(v_toPure_1150_);
v___x_1170_ = lean_apply_1(v_toTopVar_1151_, v_e_1148_);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed(lean_object* v_arg_1171_, lean_object* v_asTopVar_1172_, lean_object* v_e_1173_, lean_object* v_arg_1174_, lean_object* v_toPure_1175_, lean_object* v_toTopVar_1176_, lean_object* v_____do__lift_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(v_arg_1171_, v_asTopVar_1172_, v_e_1173_, v_arg_1174_, v_toPure_1175_, v_toTopVar_1176_, v_____do__lift_1177_);
lean_dec_ref(v_____do__lift_1177_);
lean_dec_ref(v_arg_1171_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5(lean_object* v_toTopVar_1179_, lean_object* v_e_1180_, lean_object* v_toPure_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_toVar_1187_, lean_object* v_asVar_1188_, lean_object* v_toBind_1189_, lean_object* v_asTopVar_1190_, lean_object* v_____x_1191_){
_start:
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = l_Lean_Expr_cleanupAnnotations(v_____x_1191_);
v___x_1193_ = l_Lean_Expr_isApp(v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec_ref(v___x_1192_);
lean_dec(v_asTopVar_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec(v_toPure_1181_);
v___x_1194_ = lean_apply_1(v_toTopVar_1179_, v_e_1180_);
return v___x_1194_;
}
else
{
lean_object* v_arg_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_arg_1195_ = lean_ctor_get(v___x_1192_, 1);
lean_inc_ref(v_arg_1195_);
v___x_1196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1192_);
v___x_1197_ = l_Lean_Expr_isApp(v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v___x_1196_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_asTopVar_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec(v_toPure_1181_);
v___x_1198_ = lean_apply_1(v_toTopVar_1179_, v_e_1180_);
return v___x_1198_;
}
else
{
lean_object* v_arg_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_arg_1199_ = lean_ctor_get(v___x_1196_, 1);
lean_inc_ref(v_arg_1199_);
v___x_1200_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1196_);
v___x_1201_ = l_Lean_Expr_isApp(v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_asTopVar_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec(v_toPure_1181_);
v___x_1202_ = lean_apply_1(v_toTopVar_1179_, v_e_1180_);
return v___x_1202_;
}
else
{
lean_object* v_arg_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_arg_1203_ = lean_ctor_get(v___x_1200_, 1);
lean_inc_ref(v_arg_1203_);
v___x_1204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1200_);
v___x_1205_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_1206_ = l_Lean_Expr_isConstOf(v___x_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_1208_ = l_Lean_Expr_isConstOf(v___x_1204_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = l_Lean_Expr_isApp(v___x_1204_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v___x_1204_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_asTopVar_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec(v_toPure_1181_);
v___x_1210_ = lean_apply_1(v_toTopVar_1179_, v_e_1180_);
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1204_);
v___x_1212_ = l_Lean_Expr_isApp(v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_asTopVar_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec(v_toPure_1181_);
v___x_1213_ = lean_apply_1(v_toTopVar_1179_, v_e_1180_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1211_);
v___x_1215_ = l_Lean_Expr_isApp(v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v___x_1214_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_asTopVar_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec(v_toPure_1181_);
v___x_1216_ = lean_apply_1(v_toTopVar_1179_, v_e_1180_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1217_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1214_);
v___x_1218_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_1219_ = l_Lean_Expr_isConstOf(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_1221_ = l_Lean_Expr_isConstOf(v___x_1217_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_1223_ = l_Lean_Expr_isConstOf(v___x_1217_, v___x_1222_);
lean_dec_ref(v___x_1217_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1199_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_asTopVar_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec(v_toPure_1181_);
v___x_1224_ = lean_apply_1(v_toTopVar_1179_, v_e_1180_);
return v___x_1224_;
}
else
{
lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_toTopVar_1179_);
lean_inc_n(v_toBind_1189_, 2);
lean_inc(v_asVar_1188_);
lean_inc(v_toVar_1187_);
lean_inc_ref_n(v_inst_1186_, 2);
lean_inc_ref_n(v_inst_1185_, 2);
lean_inc_ref_n(v_inst_1184_, 2);
lean_inc_ref_n(v_inst_1183_, 2);
lean_inc_n(v_inst_1182_, 2);
v___f_1225_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4), 11, 10);
lean_closure_set(v___f_1225_, 0, v_toPure_1181_);
lean_closure_set(v___f_1225_, 1, v_inst_1182_);
lean_closure_set(v___f_1225_, 2, v_inst_1183_);
lean_closure_set(v___f_1225_, 3, v_inst_1184_);
lean_closure_set(v___f_1225_, 4, v_inst_1185_);
lean_closure_set(v___f_1225_, 5, v_inst_1186_);
lean_closure_set(v___f_1225_, 6, v_toVar_1187_);
lean_closure_set(v___f_1225_, 7, v_asVar_1188_);
lean_closure_set(v___f_1225_, 8, v_arg_1195_);
lean_closure_set(v___f_1225_, 9, v_toBind_1189_);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1226_, 0, v_arg_1203_);
lean_closure_set(v___f_1226_, 1, v_asTopVar_1190_);
lean_closure_set(v___f_1226_, 2, v_e_1180_);
lean_closure_set(v___f_1226_, 3, v_inst_1182_);
lean_closure_set(v___f_1226_, 4, v_inst_1183_);
lean_closure_set(v___f_1226_, 5, v_inst_1184_);
lean_closure_set(v___f_1226_, 6, v_inst_1185_);
lean_closure_set(v___f_1226_, 7, v_inst_1186_);
lean_closure_set(v___f_1226_, 8, v_toVar_1187_);
lean_closure_set(v___f_1226_, 9, v_asVar_1188_);
lean_closure_set(v___f_1226_, 10, v_arg_1199_);
lean_closure_set(v___f_1226_, 11, v_toBind_1189_);
lean_closure_set(v___f_1226_, 12, v___f_1225_);
v___x_1227_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1182_, v_inst_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_);
v___x_1228_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1227_, v___f_1226_);
return v___x_1228_;
}
}
else
{
lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec_ref(v___x_1217_);
lean_dec(v_toTopVar_1179_);
lean_inc_n(v_toBind_1189_, 2);
lean_inc(v_asVar_1188_);
lean_inc(v_toVar_1187_);
lean_inc_ref_n(v_inst_1186_, 2);
lean_inc_ref_n(v_inst_1185_, 2);
lean_inc_ref_n(v_inst_1184_, 2);
lean_inc_ref_n(v_inst_1183_, 2);
lean_inc_n(v_inst_1182_, 2);
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6), 11, 10);
lean_closure_set(v___f_1229_, 0, v_toPure_1181_);
lean_closure_set(v___f_1229_, 1, v_inst_1182_);
lean_closure_set(v___f_1229_, 2, v_inst_1183_);
lean_closure_set(v___f_1229_, 3, v_inst_1184_);
lean_closure_set(v___f_1229_, 4, v_inst_1185_);
lean_closure_set(v___f_1229_, 5, v_inst_1186_);
lean_closure_set(v___f_1229_, 6, v_toVar_1187_);
lean_closure_set(v___f_1229_, 7, v_asVar_1188_);
lean_closure_set(v___f_1229_, 8, v_arg_1195_);
lean_closure_set(v___f_1229_, 9, v_toBind_1189_);
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1230_, 0, v_arg_1203_);
lean_closure_set(v___f_1230_, 1, v_asTopVar_1190_);
lean_closure_set(v___f_1230_, 2, v_e_1180_);
lean_closure_set(v___f_1230_, 3, v_inst_1182_);
lean_closure_set(v___f_1230_, 4, v_inst_1183_);
lean_closure_set(v___f_1230_, 5, v_inst_1184_);
lean_closure_set(v___f_1230_, 6, v_inst_1185_);
lean_closure_set(v___f_1230_, 7, v_inst_1186_);
lean_closure_set(v___f_1230_, 8, v_toVar_1187_);
lean_closure_set(v___f_1230_, 9, v_asVar_1188_);
lean_closure_set(v___f_1230_, 10, v_arg_1199_);
lean_closure_set(v___f_1230_, 11, v_toBind_1189_);
lean_closure_set(v___f_1230_, 12, v___f_1229_);
v___x_1231_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1182_, v_inst_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_);
v___x_1232_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1231_, v___f_1230_);
return v___x_1232_;
}
}
else
{
lean_object* v___x_1233_; 
lean_dec_ref(v___x_1217_);
lean_dec(v_toTopVar_1179_);
v___x_1233_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1195_);
if (lean_obj_tag(v___x_1233_) == 1)
{
lean_object* v_val_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_val_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17), 3, 2);
lean_closure_set(v___f_1235_, 0, v_val_1234_);
lean_closure_set(v___f_1235_, 1, v_toPure_1181_);
lean_inc(v_toBind_1189_);
lean_inc_ref(v_inst_1186_);
lean_inc_ref(v_inst_1185_);
lean_inc_ref(v_inst_1184_);
lean_inc_ref(v_inst_1183_);
lean_inc(v_inst_1182_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1236_, 0, v_arg_1203_);
lean_closure_set(v___f_1236_, 1, v_asTopVar_1190_);
lean_closure_set(v___f_1236_, 2, v_e_1180_);
lean_closure_set(v___f_1236_, 3, v_inst_1182_);
lean_closure_set(v___f_1236_, 4, v_inst_1183_);
lean_closure_set(v___f_1236_, 5, v_inst_1184_);
lean_closure_set(v___f_1236_, 6, v_inst_1185_);
lean_closure_set(v___f_1236_, 7, v_inst_1186_);
lean_closure_set(v___f_1236_, 8, v_toVar_1187_);
lean_closure_set(v___f_1236_, 9, v_asVar_1188_);
lean_closure_set(v___f_1236_, 10, v_arg_1199_);
lean_closure_set(v___f_1236_, 11, v_toBind_1189_);
lean_closure_set(v___f_1236_, 12, v___f_1235_);
v___x_1237_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1182_, v_inst_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_);
v___x_1238_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1237_, v___f_1236_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v___x_1233_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1199_);
lean_dec(v_asTopVar_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec_ref(v_e_1180_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_apply_2(v_toPure_1181_, lean_box(0), v___x_1239_);
return v___x_1240_;
}
}
}
}
}
}
else
{
lean_object* v___f_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v___x_1204_);
lean_dec_ref(v_arg_1203_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1183_);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_1241_, 0, v_arg_1199_);
lean_closure_set(v___f_1241_, 1, v_asTopVar_1190_);
lean_closure_set(v___f_1241_, 2, v_e_1180_);
lean_closure_set(v___f_1241_, 3, v_arg_1195_);
lean_closure_set(v___f_1241_, 4, v_toPure_1181_);
lean_closure_set(v___f_1241_, 5, v_toTopVar_1179_);
v___x_1242_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1182_, v_inst_1184_, v_inst_1185_, v_inst_1186_);
v___x_1243_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1242_, v___f_1241_);
return v___x_1243_;
}
}
else
{
lean_dec_ref(v___x_1204_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1195_);
lean_dec(v_toBind_1189_);
lean_dec(v_asVar_1188_);
lean_dec(v_toVar_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
lean_dec(v_inst_1182_);
lean_dec(v_toTopVar_1179_);
if (lean_obj_tag(v_arg_1199_) == 9)
{
lean_object* v_a_1244_; 
v_a_1244_ = lean_ctor_get(v_arg_1199_, 0);
lean_inc_ref(v_a_1244_);
lean_dec_ref_known(v_arg_1199_, 1);
if (lean_obj_tag(v_a_1244_) == 0)
{
lean_object* v_val_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_asTopVar_1190_);
lean_dec_ref(v_e_1180_);
v_val_1245_ = lean_ctor_get(v_a_1244_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_a_1244_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1247_ = v_a_1244_;
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_val_1245_);
lean_dec(v_a_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_nat_to_int(v_val_1245_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
v___x_1253_ = lean_apply_2(v_toPure_1181_, lean_box(0), v___x_1252_);
return v___x_1253_;
}
}
}
else
{
lean_object* v___x_1256_; 
lean_dec_ref(v_a_1244_);
lean_dec(v_toPure_1181_);
v___x_1256_ = lean_apply_1(v_asTopVar_1190_, v_e_1180_);
return v___x_1256_;
}
}
else
{
lean_object* v___x_1257_; 
lean_dec_ref(v_arg_1199_);
lean_dec(v_toPure_1181_);
v___x_1257_ = lean_apply_1(v_asTopVar_1190_, v_e_1180_);
return v___x_1257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_e_1265_){
_start:
{
lean_object* v_toApplicative_1266_; lean_object* v_toBind_1267_; lean_object* v_toPure_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v_asVar_1271_; lean_object* v_toVar_1272_; lean_object* v_toTopVar_1273_; lean_object* v_asTopVar_1274_; lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_toApplicative_1266_ = lean_ctor_get(v_inst_1261_, 0);
v_toBind_1267_ = lean_ctor_get(v_inst_1261_, 1);
lean_inc_n(v_toBind_1267_, 6);
v_toPure_1268_ = lean_ctor_get(v_toApplicative_1266_, 1);
lean_inc_n(v_toPure_1268_, 3);
v___f_1269_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1269_, 0, v_toPure_1268_);
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1270_, 0, v_toPure_1268_);
lean_inc(v_inst_1258_);
lean_inc_ref(v___f_1270_);
lean_inc(v_inst_1264_);
v_asVar_1271_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v_asVar_1271_, 0, v_inst_1264_);
lean_closure_set(v_asVar_1271_, 1, v_toBind_1267_);
lean_closure_set(v_asVar_1271_, 2, v___f_1270_);
lean_closure_set(v_asVar_1271_, 3, v_inst_1258_);
v_toVar_1272_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6), 4, 3);
lean_closure_set(v_toVar_1272_, 0, v_inst_1264_);
lean_closure_set(v_toVar_1272_, 1, v_toBind_1267_);
lean_closure_set(v_toVar_1272_, 2, v___f_1270_);
lean_inc_ref(v_toVar_1272_);
v_toTopVar_1273_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v_toTopVar_1273_, 0, v_toVar_1272_);
lean_closure_set(v_toTopVar_1273_, 1, v_toBind_1267_);
lean_closure_set(v_toTopVar_1273_, 2, v___f_1269_);
lean_inc_ref(v_toTopVar_1273_);
v_asTopVar_1274_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v_asTopVar_1274_, 0, v_toTopVar_1273_);
lean_closure_set(v_asTopVar_1274_, 1, v_inst_1258_);
lean_closure_set(v_asTopVar_1274_, 2, v_toBind_1267_);
lean_inc(v_inst_1259_);
lean_inc_ref(v_e_1265_);
v___f_1275_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5), 13, 12);
lean_closure_set(v___f_1275_, 0, v_toTopVar_1273_);
lean_closure_set(v___f_1275_, 1, v_e_1265_);
lean_closure_set(v___f_1275_, 2, v_toPure_1268_);
lean_closure_set(v___f_1275_, 3, v_inst_1259_);
lean_closure_set(v___f_1275_, 4, v_inst_1260_);
lean_closure_set(v___f_1275_, 5, v_inst_1261_);
lean_closure_set(v___f_1275_, 6, v_inst_1262_);
lean_closure_set(v___f_1275_, 7, v_inst_1263_);
lean_closure_set(v___f_1275_, 8, v_toVar_1272_);
lean_closure_set(v___f_1275_, 9, v_asVar_1271_);
lean_closure_set(v___f_1275_, 10, v_toBind_1267_);
lean_closure_set(v___f_1275_, 11, v_asTopVar_1274_);
v___x_1276_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_1276_, 0, v_e_1265_);
v___x_1277_ = lean_apply_2(v_inst_1259_, lean_box(0), v___x_1276_);
v___x_1278_ = lean_apply_4(v_toBind_1267_, lean_box(0), lean_box(0), v___x_1277_, v___f_1275_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f(lean_object* v_m_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_e_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(v_inst_1280_, v_inst_1281_, v_inst_1282_, v_inst_1283_, v_inst_1284_, v_inst_1285_, v_inst_1286_, v_e_1287_);
return v___x_1288_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Reify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
