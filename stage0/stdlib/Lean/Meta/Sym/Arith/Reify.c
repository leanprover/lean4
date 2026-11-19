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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_____do__lift_1138__boxed_197_; lean_object* v_res_198_; 
v_____do__lift_1138__boxed_197_ = lean_unbox(v_____do__lift_196_);
v_res_198_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11(v_asVar_191_, v_e_192_, v_arg_193_, v_toPure_194_, v_toVar_195_, v_____do__lift_1138__boxed_197_);
lean_dec_ref(v_arg_193_);
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
uint8_t v_____do__lift_1192__boxed_238_; lean_object* v_res_239_; 
v_____do__lift_1192__boxed_238_ = lean_unbox(v_____do__lift_237_);
v_res_239_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8(v_asVar_232_, v_e_233_, v_arg_234_, v_toPure_235_, v_toVar_236_, v_____do__lift_1192__boxed_238_);
lean_dec_ref(v_arg_234_);
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
uint8_t v_____do__lift_1302__boxed_311_; lean_object* v_res_312_; 
v_____do__lift_1302__boxed_311_ = lean_unbox(v_____do__lift_310_);
v_res_312_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__3(v_asVar_299_, v_e_300_, v_inst_301_, v_inst_302_, v_inst_303_, v_inst_304_, v_inst_305_, v_toVar_306_, v_arg_307_, v_toBind_308_, v___f_309_, v_____do__lift_1302__boxed_311_);
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
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = l_Lean_Expr_appFnCleanup___redArg(v___x_368_);
v___x_372_ = l_Lean_Expr_isApp(v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
lean_dec_ref(v___x_371_);
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
v___x_373_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_373_;
}
else
{
lean_object* v_arg_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_arg_374_ = lean_ctor_get(v___x_368_, 1);
lean_inc_ref(v_arg_374_);
lean_dec_ref(v___x_368_);
v___x_375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_371_);
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__2));
v___x_377_ = l_Lean_Expr_isConstOf(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_Expr_isApp(v___x_375_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec_ref(v___x_375_);
lean_dec_ref(v_arg_374_);
lean_dec_ref(v___x_371_);
lean_dec(v___f_351_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_379_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_379_;
}
else
{
lean_object* v_arg_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_arg_380_ = lean_ctor_get(v___x_371_, 1);
lean_inc_ref(v_arg_380_);
lean_dec_ref(v___x_371_);
v___x_381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_375_);
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_383_ = l_Lean_Expr_isConstOf(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_385_ = l_Lean_Expr_isConstOf(v___x_381_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10));
v___x_387_ = l_Lean_Expr_isConstOf(v___x_381_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13));
v___x_389_ = l_Lean_Expr_isConstOf(v___x_381_, v___x_388_);
if (v___x_389_ == 0)
{
uint8_t v___x_390_; 
lean_dec(v___f_351_);
v___x_390_ = l_Lean_Expr_isApp(v___x_381_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v_arg_380_);
lean_dec_ref(v___x_375_);
lean_dec_ref(v_arg_374_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_391_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = l_Lean_Expr_appFnCleanup___redArg(v___x_381_);
lean_dec_ref(v___x_381_);
v___x_393_ = l_Lean_Expr_isApp(v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v___x_392_);
lean_dec_ref(v_arg_380_);
lean_dec_ref(v___x_375_);
lean_dec_ref(v_arg_374_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_394_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_392_);
lean_dec_ref(v___x_392_);
v___x_396_ = l_Lean_Expr_isApp(v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec_ref(v___x_395_);
lean_dec_ref(v_arg_380_);
lean_dec_ref(v___x_375_);
lean_dec_ref(v_arg_374_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
lean_dec(v_toPure_343_);
v___x_397_ = lean_apply_1(v_toVar_341_, v_e_342_);
return v___x_397_;
}
else
{
lean_object* v_arg_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_arg_398_ = lean_ctor_get(v___x_375_, 1);
lean_inc_ref(v_arg_398_);
lean_dec_ref(v___x_375_);
v___x_399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_395_);
lean_dec_ref(v___x_395_);
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
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_380_);
lean_dec_ref(v_arg_374_);
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
lean_closure_set(v___f_409_, 8, v_arg_374_);
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
lean_closure_set(v___f_410_, 8, v_arg_380_);
lean_closure_set(v___f_410_, 9, v_toBind_350_);
lean_closure_set(v___f_410_, 10, v___f_409_);
v___x_411_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_398_);
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
lean_closure_set(v___f_413_, 8, v_arg_374_);
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
lean_closure_set(v___f_414_, 8, v_arg_380_);
lean_closure_set(v___f_414_, 9, v_toBind_350_);
lean_closure_set(v___f_414_, 10, v___f_413_);
v___x_415_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_398_);
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
lean_closure_set(v___f_417_, 8, v_arg_374_);
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
lean_closure_set(v___f_418_, 8, v_arg_380_);
lean_closure_set(v___f_418_, 9, v_toBind_350_);
lean_closure_set(v___f_418_, 10, v___f_417_);
v___x_419_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_398_);
v___x_420_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_419_, v___f_418_);
return v___x_420_;
}
}
else
{
lean_object* v___x_421_; 
lean_dec_ref(v___x_399_);
v___x_421_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_374_);
lean_dec_ref(v_arg_374_);
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
lean_closure_set(v___f_424_, 8, v_arg_380_);
lean_closure_set(v___f_424_, 9, v_toBind_350_);
lean_closure_set(v___f_424_, 10, v___f_423_);
v___x_425_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_398_);
v___x_426_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_425_, v___f_424_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
lean_dec(v___x_421_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_380_);
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
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_375_);
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
lean_closure_set(v___f_428_, 8, v_arg_374_);
lean_closure_set(v___f_428_, 9, v_toBind_350_);
lean_closure_set(v___f_428_, 10, v___f_351_);
v___x_429_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_380_);
v___x_430_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_429_, v___f_428_);
return v___x_430_;
}
}
else
{
lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_375_);
lean_dec(v___f_351_);
lean_dec_ref(v_inst_345_);
v___f_431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_431_, 0, v_asVar_349_);
lean_closure_set(v___f_431_, 1, v_e_342_);
lean_closure_set(v___f_431_, 2, v_arg_374_);
lean_closure_set(v___f_431_, 3, v_toPure_343_);
lean_closure_set(v___f_431_, 4, v_toVar_341_);
v___x_432_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_344_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_380_);
v___x_433_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_432_, v___f_431_);
return v___x_433_;
}
}
else
{
lean_object* v___f_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_375_);
lean_dec(v___f_351_);
lean_dec_ref(v_inst_345_);
v___f_434_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__8___boxed), 6, 5);
lean_closure_set(v___f_434_, 0, v_asVar_349_);
lean_closure_set(v___f_434_, 1, v_e_342_);
lean_closure_set(v___f_434_, 2, v_arg_374_);
lean_closure_set(v___f_434_, 3, v_toPure_343_);
lean_closure_set(v___f_434_, 4, v_toVar_341_);
v___x_435_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_344_, v_inst_346_, v_inst_347_, v_inst_348_, v_arg_380_);
v___x_436_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_435_, v___f_434_);
return v___x_436_;
}
}
else
{
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_375_);
lean_dec_ref(v_arg_374_);
lean_dec(v___f_351_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
v_n_354_ = v_arg_380_;
goto v___jp_353_;
}
}
}
else
{
lean_dec_ref(v___x_375_);
lean_dec_ref(v___x_371_);
lean_dec(v___f_351_);
lean_dec(v_toBind_350_);
lean_dec(v_asVar_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec(v_inst_344_);
v_n_354_ = v_arg_374_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___boxed(lean_object* v_toVar_437_, lean_object* v_e_438_, lean_object* v_toPure_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_asVar_445_, lean_object* v_toBind_446_, lean_object* v___f_447_, lean_object* v_____x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10(v_toVar_437_, v_e_438_, v_toPure_439_, v_inst_440_, v_inst_441_, v_inst_442_, v_inst_443_, v_inst_444_, v_asVar_445_, v_toBind_446_, v___f_447_, v_____x_448_);
lean_dec_ref(v_____x_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_toVar_455_, lean_object* v_asVar_456_, lean_object* v_e_457_){
_start:
{
lean_object* v_toApplicative_458_; lean_object* v_toBind_459_; lean_object* v_toPure_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___f_463_; lean_object* v___f_464_; lean_object* v___x_465_; 
v_toApplicative_458_ = lean_ctor_get(v_inst_452_, 0);
v_toBind_459_ = lean_ctor_get(v_inst_452_, 1);
lean_inc_n(v_toBind_459_, 2);
v_toPure_460_ = lean_ctor_get(v_toApplicative_458_, 1);
lean_inc_n(v_toPure_460_, 2);
lean_inc_ref(v_e_457_);
v___x_461_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_461_, 0, v_e_457_);
lean_inc(v_inst_450_);
v___x_462_ = lean_apply_2(v_inst_450_, lean_box(0), v___x_461_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_463_, 0, v_toPure_460_);
v___f_464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___boxed), 12, 11);
lean_closure_set(v___f_464_, 0, v_toVar_455_);
lean_closure_set(v___f_464_, 1, v_e_457_);
lean_closure_set(v___f_464_, 2, v_toPure_460_);
lean_closure_set(v___f_464_, 3, v_inst_450_);
lean_closure_set(v___f_464_, 4, v_inst_451_);
lean_closure_set(v___f_464_, 5, v_inst_452_);
lean_closure_set(v___f_464_, 6, v_inst_453_);
lean_closure_set(v___f_464_, 7, v_inst_454_);
lean_closure_set(v___f_464_, 8, v_asVar_456_);
lean_closure_set(v___f_464_, 9, v_toBind_459_);
lean_closure_set(v___f_464_, 10, v___f_463_);
v___x_465_ = lean_apply_4(v_toBind_459_, lean_box(0), lean_box(0), v___x_462_, v___f_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__2(lean_object* v_toPure_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_toVar_472_, lean_object* v_asVar_473_, lean_object* v_arg_474_, lean_object* v_toBind_475_, lean_object* v_____do__lift_476_){
_start:
{
lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___f_477_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_477_, 0, v_____do__lift_476_);
lean_closure_set(v___f_477_, 1, v_toPure_466_);
v___x_478_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_467_, v_inst_468_, v_inst_469_, v_inst_470_, v_inst_471_, v_toVar_472_, v_asVar_473_, v_arg_474_);
v___x_479_ = lean_apply_4(v_toBind_475_, lean_box(0), lean_box(0), v___x_478_, v___f_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go(lean_object* v_m_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_toVar_486_, lean_object* v_asVar_487_, lean_object* v_e_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_481_, v_inst_482_, v_inst_483_, v_inst_484_, v_inst_485_, v_toVar_486_, v_asVar_487_, v_e_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0(lean_object* v_toPure_490_, lean_object* v_____do__lift_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_492_, 0, v_____do__lift_491_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
v___x_494_ = lean_apply_2(v_toPure_490_, lean_box(0), v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1(lean_object* v_toPure_495_, lean_object* v_____do__lift_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v_____do__lift_496_);
v___x_498_ = lean_apply_2(v_toPure_495_, lean_box(0), v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2(lean_object* v_toPure_499_, lean_object* v_____do__lift_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_501_, 0, v_____do__lift_500_);
v___x_502_ = lean_apply_2(v_toPure_499_, lean_box(0), v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3(lean_object* v_inst_503_, lean_object* v_e_504_, lean_object* v_toBind_505_, lean_object* v___f_506_, lean_object* v_____r_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_apply_1(v_inst_503_, v_e_504_);
v___x_509_ = lean_apply_4(v_toBind_505_, lean_box(0), lean_box(0), v___x_508_, v___f_506_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4(lean_object* v_inst_510_, lean_object* v_toBind_511_, lean_object* v___f_512_, lean_object* v_inst_513_, lean_object* v_e_514_){
_start:
{
lean_object* v___f_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_inc(v_toBind_511_);
lean_inc_ref(v_e_514_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_515_, 0, v_inst_510_);
lean_closure_set(v___f_515_, 1, v_e_514_);
lean_closure_set(v___f_515_, 2, v_toBind_511_);
lean_closure_set(v___f_515_, 3, v___f_512_);
v___x_516_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_513_, v_e_514_);
v___x_517_ = lean_apply_4(v_toBind_511_, lean_box(0), lean_box(0), v___x_516_, v___f_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6(lean_object* v_inst_518_, lean_object* v_toBind_519_, lean_object* v___f_520_, lean_object* v_e_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_apply_1(v_inst_518_, v_e_521_);
v___x_523_ = lean_apply_4(v_toBind_519_, lean_box(0), lean_box(0), v___x_522_, v___f_520_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(uint8_t v_skipVar_524_, lean_object* v_toVar_525_, lean_object* v_toBind_526_, lean_object* v___f_527_, lean_object* v_toPure_528_, lean_object* v_e_529_){
_start:
{
if (v_skipVar_524_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec(v_toPure_528_);
v___x_530_ = lean_apply_1(v_toVar_525_, v_e_529_);
v___x_531_ = lean_apply_4(v_toBind_526_, lean_box(0), lean_box(0), v___x_530_, v___f_527_);
return v___x_531_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec_ref(v_e_529_);
lean_dec(v___f_527_);
lean_dec(v_toBind_526_);
lean_dec(v_toVar_525_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_apply_2(v_toPure_528_, lean_box(0), v___x_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed(lean_object* v_skipVar_534_, lean_object* v_toVar_535_, lean_object* v_toBind_536_, lean_object* v___f_537_, lean_object* v_toPure_538_, lean_object* v_e_539_){
_start:
{
uint8_t v_skipVar_boxed_540_; lean_object* v_res_541_; 
v_skipVar_boxed_540_ = lean_unbox(v_skipVar_534_);
v_res_541_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5(v_skipVar_boxed_540_, v_toVar_535_, v_toBind_536_, v___f_537_, v_toPure_538_, v_e_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7(lean_object* v_toTopVar_542_, lean_object* v_e_543_, lean_object* v_____r_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_apply_1(v_toTopVar_542_, v_e_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8(lean_object* v_toTopVar_546_, lean_object* v_inst_547_, lean_object* v_toBind_548_, lean_object* v_e_549_){
_start:
{
lean_object* v___f_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc_ref(v_e_549_);
v___f_550_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7), 3, 2);
lean_closure_set(v___f_550_, 0, v_toTopVar_546_);
lean_closure_set(v___f_550_, 1, v_e_549_);
v___x_551_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportRingAppIssue___redArg(v_inst_547_, v_e_549_);
v___x_552_ = lean_apply_4(v_toBind_548_, lean_box(0), lean_box(0), v___x_551_, v___f_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9(lean_object* v_____do__lift_553_, lean_object* v_toPure_554_, lean_object* v_____do__lift_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v_____do__lift_553_);
lean_ctor_set(v___x_556_, 1, v_____do__lift_555_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = lean_apply_2(v_toPure_554_, lean_box(0), v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10(lean_object* v_toPure_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_toVar_565_, lean_object* v_asVar_566_, lean_object* v_arg_567_, lean_object* v_toBind_568_, lean_object* v_____do__lift_569_){
_start:
{
lean_object* v___f_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9), 3, 2);
lean_closure_set(v___f_570_, 0, v_____do__lift_569_);
lean_closure_set(v___f_570_, 1, v_toPure_559_);
v___x_571_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_560_, v_inst_561_, v_inst_562_, v_inst_563_, v_inst_564_, v_toVar_565_, v_asVar_566_, v_arg_567_);
v___x_572_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v___x_571_, v___f_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(lean_object* v_asTopVar_573_, lean_object* v_e_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_toVar_580_, lean_object* v_asVar_581_, lean_object* v_arg_582_, lean_object* v_toBind_583_, lean_object* v___f_584_, uint8_t v_____do__lift_585_){
_start:
{
if (v_____do__lift_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec(v___f_584_);
lean_dec(v_toBind_583_);
lean_dec_ref(v_arg_582_);
lean_dec(v_asVar_581_);
lean_dec(v_toVar_580_);
lean_dec_ref(v_inst_579_);
lean_dec_ref(v_inst_578_);
lean_dec_ref(v_inst_577_);
lean_dec_ref(v_inst_576_);
lean_dec(v_inst_575_);
v___x_586_ = lean_apply_1(v_asTopVar_573_, v_e_574_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec_ref(v_e_574_);
lean_dec(v_asTopVar_573_);
v___x_587_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_toVar_580_, v_asVar_581_, v_arg_582_);
v___x_588_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v___x_587_, v___f_584_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed(lean_object* v_asTopVar_589_, lean_object* v_e_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_toVar_596_, lean_object* v_asVar_597_, lean_object* v_arg_598_, lean_object* v_toBind_599_, lean_object* v___f_600_, lean_object* v_____do__lift_601_){
_start:
{
uint8_t v_____do__lift_1422__boxed_602_; lean_object* v_res_603_; 
v_____do__lift_1422__boxed_602_ = lean_unbox(v_____do__lift_601_);
v_res_603_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11(v_asTopVar_589_, v_e_590_, v_inst_591_, v_inst_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_toVar_596_, v_asVar_597_, v_arg_598_, v_toBind_599_, v___f_600_, v_____do__lift_1422__boxed_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12(lean_object* v_____do__lift_604_, lean_object* v_toPure_605_, lean_object* v_____do__lift_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v_____do__lift_604_);
lean_ctor_set(v___x_607_, 1, v_____do__lift_606_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = lean_apply_2(v_toPure_605_, lean_box(0), v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13(lean_object* v_toPure_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_toVar_616_, lean_object* v_asVar_617_, lean_object* v_arg_618_, lean_object* v_toBind_619_, lean_object* v_____do__lift_620_){
_start:
{
lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12), 3, 2);
lean_closure_set(v___f_621_, 0, v_____do__lift_620_);
lean_closure_set(v___f_621_, 1, v_toPure_610_);
v___x_622_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_611_, v_inst_612_, v_inst_613_, v_inst_614_, v_inst_615_, v_toVar_616_, v_asVar_617_, v_arg_618_);
v___x_623_ = lean_apply_4(v_toBind_619_, lean_box(0), lean_box(0), v___x_622_, v___f_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15(lean_object* v_____do__lift_624_, lean_object* v_toPure_625_, lean_object* v_____do__lift_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_627_, 0, v_____do__lift_624_);
lean_ctor_set(v___x_627_, 1, v_____do__lift_626_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = lean_apply_2(v_toPure_625_, lean_box(0), v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14(lean_object* v_toPure_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_toVar_636_, lean_object* v_asVar_637_, lean_object* v_arg_638_, lean_object* v_toBind_639_, lean_object* v_____do__lift_640_){
_start:
{
lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__15), 3, 2);
lean_closure_set(v___f_641_, 0, v_____do__lift_640_);
lean_closure_set(v___f_641_, 1, v_toPure_630_);
v___x_642_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg(v_inst_631_, v_inst_632_, v_inst_633_, v_inst_634_, v_inst_635_, v_toVar_636_, v_asVar_637_, v_arg_638_);
v___x_643_ = lean_apply_4(v_toBind_639_, lean_box(0), lean_box(0), v___x_642_, v___f_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17(lean_object* v_val_644_, lean_object* v_toPure_645_, lean_object* v_____do__lift_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_647_, 0, v_____do__lift_646_);
lean_ctor_set(v___x_647_, 1, v_val_644_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___x_649_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(lean_object* v_asTopVar_650_, lean_object* v_e_651_, lean_object* v_arg_652_, lean_object* v_toPure_653_, lean_object* v_toTopVar_654_, uint8_t v_____do__lift_655_){
_start:
{
if (v_____do__lift_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v_toTopVar_654_);
lean_dec(v_toPure_653_);
v___x_656_ = lean_apply_1(v_asTopVar_650_, v_e_651_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; 
lean_dec(v_asTopVar_650_);
v___x_657_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_652_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_667_; 
lean_dec(v_toTopVar_654_);
lean_dec_ref(v_e_651_);
v_val_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_667_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_662_, 0, v_val_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; 
v___x_665_ = lean_apply_2(v_toPure_653_, lean_box(0), v___x_664_);
return v___x_665_;
}
}
}
else
{
lean_object* v___x_668_; 
lean_dec(v___x_657_);
lean_dec(v_toPure_653_);
v___x_668_ = lean_apply_1(v_toTopVar_654_, v_e_651_);
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed(lean_object* v_asTopVar_669_, lean_object* v_e_670_, lean_object* v_arg_671_, lean_object* v_toPure_672_, lean_object* v_toTopVar_673_, lean_object* v_____do__lift_674_){
_start:
{
uint8_t v_____do__lift_1516__boxed_675_; lean_object* v_res_676_; 
v_____do__lift_1516__boxed_675_ = lean_unbox(v_____do__lift_674_);
v_res_676_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19(v_asTopVar_669_, v_e_670_, v_arg_671_, v_toPure_672_, v_toTopVar_673_, v_____do__lift_1516__boxed_675_);
lean_dec_ref(v_arg_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(lean_object* v_asTopVar_677_, lean_object* v_e_678_, lean_object* v_arg_679_, lean_object* v_toPure_680_, lean_object* v_toTopVar_681_, uint8_t v_____do__lift_682_){
_start:
{
if (v_____do__lift_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec(v_toTopVar_681_);
lean_dec(v_toPure_680_);
v___x_683_ = lean_apply_1(v_asTopVar_677_, v_e_678_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; 
lean_dec(v_asTopVar_677_);
v___x_684_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_679_);
if (lean_obj_tag(v___x_684_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_694_; 
lean_dec(v_toTopVar_681_);
lean_dec_ref(v_e_678_);
v_val_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_694_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_val_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = lean_apply_2(v_toPure_680_, lean_box(0), v___x_691_);
return v___x_692_;
}
}
}
else
{
lean_object* v___x_695_; 
lean_dec(v___x_684_);
lean_dec(v_toPure_680_);
v___x_695_ = lean_apply_1(v_toTopVar_681_, v_e_678_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed(lean_object* v_asTopVar_696_, lean_object* v_e_697_, lean_object* v_arg_698_, lean_object* v_toPure_699_, lean_object* v_toTopVar_700_, lean_object* v_____do__lift_701_){
_start:
{
uint8_t v_____do__lift_1548__boxed_702_; lean_object* v_res_703_; 
v_____do__lift_1548__boxed_702_ = lean_unbox(v_____do__lift_701_);
v_res_703_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16(v_asTopVar_696_, v_e_697_, v_arg_698_, v_toPure_699_, v_toTopVar_700_, v_____do__lift_1548__boxed_702_);
lean_dec_ref(v_arg_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18(lean_object* v_toTopVar_704_, lean_object* v_e_705_, lean_object* v_toPure_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_toVar_712_, lean_object* v_asVar_713_, lean_object* v_toBind_714_, lean_object* v_asTopVar_715_, lean_object* v___f_716_, lean_object* v_____x_717_){
_start:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Expr_cleanupAnnotations(v_____x_717_);
v___x_719_ = l_Lean_Expr_isApp(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec_ref(v___x_718_);
lean_dec(v___f_716_);
lean_dec(v_asTopVar_715_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toPure_706_);
v___x_720_ = lean_apply_1(v_toTopVar_704_, v_e_705_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
v___x_722_ = l_Lean_Expr_isApp(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec_ref(v___x_721_);
lean_dec_ref(v___x_718_);
lean_dec(v___f_716_);
lean_dec(v_asTopVar_715_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toPure_706_);
v___x_723_ = lean_apply_1(v_toTopVar_704_, v_e_705_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_721_);
v___x_725_ = l_Lean_Expr_isApp(v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v___x_724_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v___x_718_);
lean_dec(v___f_716_);
lean_dec(v_asTopVar_715_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toPure_706_);
v___x_726_ = lean_apply_1(v_toTopVar_704_, v_e_705_);
return v___x_726_;
}
else
{
lean_object* v_arg_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_arg_727_ = lean_ctor_get(v___x_721_, 1);
lean_inc_ref(v_arg_727_);
lean_dec_ref(v___x_721_);
v___x_728_ = l_Lean_Expr_appFnCleanup___redArg(v___x_724_);
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_730_ = l_Lean_Expr_isConstOf(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v_arg_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_arg_731_ = lean_ctor_get(v___x_718_, 1);
lean_inc_ref(v_arg_731_);
lean_dec_ref(v___x_718_);
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_733_ = l_Lean_Expr_isConstOf(v___x_728_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__10));
v___x_735_ = l_Lean_Expr_isConstOf(v___x_728_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__13));
v___x_737_ = l_Lean_Expr_isConstOf(v___x_728_, v___x_736_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; 
lean_dec(v___f_716_);
v___x_738_ = l_Lean_Expr_isApp(v___x_728_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
lean_dec_ref(v_arg_731_);
lean_dec_ref(v___x_728_);
lean_dec_ref(v_arg_727_);
lean_dec_ref(v___x_724_);
lean_dec(v_asTopVar_715_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toPure_706_);
v___x_739_ = lean_apply_1(v_toTopVar_704_, v_e_705_);
return v___x_739_;
}
else
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = l_Lean_Expr_appFnCleanup___redArg(v___x_728_);
lean_dec_ref(v___x_728_);
v___x_741_ = l_Lean_Expr_isApp(v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec_ref(v___x_740_);
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_727_);
lean_dec_ref(v___x_724_);
lean_dec(v_asTopVar_715_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toPure_706_);
v___x_742_ = lean_apply_1(v_toTopVar_704_, v_e_705_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = l_Lean_Expr_appFnCleanup___redArg(v___x_740_);
lean_dec_ref(v___x_740_);
v___x_744_ = l_Lean_Expr_isApp(v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_dec_ref(v___x_743_);
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_727_);
lean_dec_ref(v___x_724_);
lean_dec(v_asTopVar_715_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toPure_706_);
v___x_745_ = lean_apply_1(v_toTopVar_704_, v_e_705_);
return v___x_745_;
}
else
{
lean_object* v_arg_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_arg_746_ = lean_ctor_get(v___x_724_, 1);
lean_inc_ref(v_arg_746_);
lean_dec_ref(v___x_724_);
v___x_747_ = l_Lean_Expr_appFnCleanup___redArg(v___x_743_);
lean_dec_ref(v___x_743_);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_749_ = l_Lean_Expr_isConstOf(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__19));
v___x_751_ = l_Lean_Expr_isConstOf(v___x_747_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_753_ = l_Lean_Expr_isConstOf(v___x_747_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_755_ = l_Lean_Expr_isConstOf(v___x_747_, v___x_754_);
lean_dec_ref(v___x_747_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_dec_ref(v_arg_746_);
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_727_);
lean_dec(v_asTopVar_715_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toPure_706_);
v___x_756_ = lean_apply_1(v_toTopVar_704_, v_e_705_);
return v___x_756_;
}
else
{
lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec(v_toTopVar_704_);
lean_inc_n(v_toBind_714_, 2);
lean_inc(v_asVar_713_);
lean_inc(v_toVar_712_);
lean_inc_ref_n(v_inst_711_, 2);
lean_inc_ref_n(v_inst_710_, 2);
lean_inc_ref_n(v_inst_709_, 2);
lean_inc_ref_n(v_inst_708_, 2);
lean_inc_n(v_inst_707_, 2);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__10), 11, 10);
lean_closure_set(v___f_757_, 0, v_toPure_706_);
lean_closure_set(v___f_757_, 1, v_inst_707_);
lean_closure_set(v___f_757_, 2, v_inst_708_);
lean_closure_set(v___f_757_, 3, v_inst_709_);
lean_closure_set(v___f_757_, 4, v_inst_710_);
lean_closure_set(v___f_757_, 5, v_inst_711_);
lean_closure_set(v___f_757_, 6, v_toVar_712_);
lean_closure_set(v___f_757_, 7, v_asVar_713_);
lean_closure_set(v___f_757_, 8, v_arg_731_);
lean_closure_set(v___f_757_, 9, v_toBind_714_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_758_, 0, v_asTopVar_715_);
lean_closure_set(v___f_758_, 1, v_e_705_);
lean_closure_set(v___f_758_, 2, v_inst_707_);
lean_closure_set(v___f_758_, 3, v_inst_708_);
lean_closure_set(v___f_758_, 4, v_inst_709_);
lean_closure_set(v___f_758_, 5, v_inst_710_);
lean_closure_set(v___f_758_, 6, v_inst_711_);
lean_closure_set(v___f_758_, 7, v_toVar_712_);
lean_closure_set(v___f_758_, 8, v_asVar_713_);
lean_closure_set(v___f_758_, 9, v_arg_727_);
lean_closure_set(v___f_758_, 10, v_toBind_714_);
lean_closure_set(v___f_758_, 11, v___f_757_);
v___x_759_ = l_Lean_Meta_Sym_Arith_isAddInst___redArg(v_inst_707_, v_inst_708_, v_inst_709_, v_inst_710_, v_inst_711_, v_arg_746_);
v___x_760_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_759_, v___f_758_);
return v___x_760_;
}
}
else
{
lean_object* v___f_761_; lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v___x_747_);
lean_dec(v_toTopVar_704_);
lean_inc_n(v_toBind_714_, 2);
lean_inc(v_asVar_713_);
lean_inc(v_toVar_712_);
lean_inc_ref_n(v_inst_711_, 2);
lean_inc_ref_n(v_inst_710_, 2);
lean_inc_ref_n(v_inst_709_, 2);
lean_inc_ref_n(v_inst_708_, 2);
lean_inc_n(v_inst_707_, 2);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__13), 11, 10);
lean_closure_set(v___f_761_, 0, v_toPure_706_);
lean_closure_set(v___f_761_, 1, v_inst_707_);
lean_closure_set(v___f_761_, 2, v_inst_708_);
lean_closure_set(v___f_761_, 3, v_inst_709_);
lean_closure_set(v___f_761_, 4, v_inst_710_);
lean_closure_set(v___f_761_, 5, v_inst_711_);
lean_closure_set(v___f_761_, 6, v_toVar_712_);
lean_closure_set(v___f_761_, 7, v_asVar_713_);
lean_closure_set(v___f_761_, 8, v_arg_731_);
lean_closure_set(v___f_761_, 9, v_toBind_714_);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_762_, 0, v_asTopVar_715_);
lean_closure_set(v___f_762_, 1, v_e_705_);
lean_closure_set(v___f_762_, 2, v_inst_707_);
lean_closure_set(v___f_762_, 3, v_inst_708_);
lean_closure_set(v___f_762_, 4, v_inst_709_);
lean_closure_set(v___f_762_, 5, v_inst_710_);
lean_closure_set(v___f_762_, 6, v_inst_711_);
lean_closure_set(v___f_762_, 7, v_toVar_712_);
lean_closure_set(v___f_762_, 8, v_asVar_713_);
lean_closure_set(v___f_762_, 9, v_arg_727_);
lean_closure_set(v___f_762_, 10, v_toBind_714_);
lean_closure_set(v___f_762_, 11, v___f_761_);
v___x_763_ = l_Lean_Meta_Sym_Arith_isMulInst___redArg(v_inst_707_, v_inst_708_, v_inst_709_, v_inst_710_, v_inst_711_, v_arg_746_);
v___x_764_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_763_, v___f_762_);
return v___x_764_;
}
}
else
{
lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v___x_747_);
lean_dec(v_toTopVar_704_);
lean_inc_n(v_toBind_714_, 2);
lean_inc(v_asVar_713_);
lean_inc(v_toVar_712_);
lean_inc_ref_n(v_inst_711_, 2);
lean_inc_ref_n(v_inst_710_, 2);
lean_inc_ref_n(v_inst_709_, 2);
lean_inc_ref_n(v_inst_708_, 2);
lean_inc_n(v_inst_707_, 2);
v___f_765_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__14), 11, 10);
lean_closure_set(v___f_765_, 0, v_toPure_706_);
lean_closure_set(v___f_765_, 1, v_inst_707_);
lean_closure_set(v___f_765_, 2, v_inst_708_);
lean_closure_set(v___f_765_, 3, v_inst_709_);
lean_closure_set(v___f_765_, 4, v_inst_710_);
lean_closure_set(v___f_765_, 5, v_inst_711_);
lean_closure_set(v___f_765_, 6, v_toVar_712_);
lean_closure_set(v___f_765_, 7, v_asVar_713_);
lean_closure_set(v___f_765_, 8, v_arg_731_);
lean_closure_set(v___f_765_, 9, v_toBind_714_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_766_, 0, v_asTopVar_715_);
lean_closure_set(v___f_766_, 1, v_e_705_);
lean_closure_set(v___f_766_, 2, v_inst_707_);
lean_closure_set(v___f_766_, 3, v_inst_708_);
lean_closure_set(v___f_766_, 4, v_inst_709_);
lean_closure_set(v___f_766_, 5, v_inst_710_);
lean_closure_set(v___f_766_, 6, v_inst_711_);
lean_closure_set(v___f_766_, 7, v_toVar_712_);
lean_closure_set(v___f_766_, 8, v_asVar_713_);
lean_closure_set(v___f_766_, 9, v_arg_727_);
lean_closure_set(v___f_766_, 10, v_toBind_714_);
lean_closure_set(v___f_766_, 11, v___f_765_);
v___x_767_ = l_Lean_Meta_Sym_Arith_isSubInst___redArg(v_inst_707_, v_inst_708_, v_inst_709_, v_inst_710_, v_inst_711_, v_arg_746_);
v___x_768_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_767_, v___f_766_);
return v___x_768_;
}
}
else
{
lean_object* v___x_769_; 
lean_dec_ref(v___x_747_);
lean_dec(v_toTopVar_704_);
v___x_769_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_731_);
lean_dec_ref(v_arg_731_);
if (lean_obj_tag(v___x_769_) == 1)
{
lean_object* v_val_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_val_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_769_, 1);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17), 3, 2);
lean_closure_set(v___f_771_, 0, v_val_770_);
lean_closure_set(v___f_771_, 1, v_toPure_706_);
lean_inc(v_toBind_714_);
lean_inc_ref(v_inst_711_);
lean_inc_ref(v_inst_710_);
lean_inc_ref(v_inst_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_772_, 0, v_asTopVar_715_);
lean_closure_set(v___f_772_, 1, v_e_705_);
lean_closure_set(v___f_772_, 2, v_inst_707_);
lean_closure_set(v___f_772_, 3, v_inst_708_);
lean_closure_set(v___f_772_, 4, v_inst_709_);
lean_closure_set(v___f_772_, 5, v_inst_710_);
lean_closure_set(v___f_772_, 6, v_inst_711_);
lean_closure_set(v___f_772_, 7, v_toVar_712_);
lean_closure_set(v___f_772_, 8, v_asVar_713_);
lean_closure_set(v___f_772_, 9, v_arg_727_);
lean_closure_set(v___f_772_, 10, v_toBind_714_);
lean_closure_set(v___f_772_, 11, v___f_771_);
v___x_773_ = l_Lean_Meta_Sym_Arith_isPowInst___redArg(v_inst_707_, v_inst_708_, v_inst_709_, v_inst_710_, v_inst_711_, v_arg_746_);
v___x_774_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_773_, v___f_772_);
return v___x_774_;
}
else
{
lean_object* v___x_775_; 
lean_dec(v___x_769_);
lean_dec_ref(v_arg_746_);
lean_dec_ref(v_arg_727_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toPure_706_);
v___x_775_ = lean_apply_1(v_asTopVar_715_, v_e_705_);
return v___x_775_;
}
}
}
}
}
}
else
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v___x_728_);
lean_dec_ref(v___x_724_);
lean_dec(v_toPure_706_);
lean_dec(v_toTopVar_704_);
lean_inc(v_toBind_714_);
lean_inc_ref(v_inst_711_);
lean_inc_ref(v_inst_710_);
lean_inc_ref(v_inst_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_776_, 0, v_asTopVar_715_);
lean_closure_set(v___f_776_, 1, v_e_705_);
lean_closure_set(v___f_776_, 2, v_inst_707_);
lean_closure_set(v___f_776_, 3, v_inst_708_);
lean_closure_set(v___f_776_, 4, v_inst_709_);
lean_closure_set(v___f_776_, 5, v_inst_710_);
lean_closure_set(v___f_776_, 6, v_inst_711_);
lean_closure_set(v___f_776_, 7, v_toVar_712_);
lean_closure_set(v___f_776_, 8, v_asVar_713_);
lean_closure_set(v___f_776_, 9, v_arg_731_);
lean_closure_set(v___f_776_, 10, v_toBind_714_);
lean_closure_set(v___f_776_, 11, v___f_716_);
v___x_777_ = l_Lean_Meta_Sym_Arith_isNegInst___redArg(v_inst_707_, v_inst_708_, v_inst_709_, v_inst_710_, v_inst_711_, v_arg_727_);
v___x_778_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_777_, v___f_776_);
return v___x_778_;
}
}
else
{
lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v___x_728_);
lean_dec_ref(v___x_724_);
lean_dec(v___f_716_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_708_);
v___f_779_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__19___boxed), 6, 5);
lean_closure_set(v___f_779_, 0, v_asTopVar_715_);
lean_closure_set(v___f_779_, 1, v_e_705_);
lean_closure_set(v___f_779_, 2, v_arg_731_);
lean_closure_set(v___f_779_, 3, v_toPure_706_);
lean_closure_set(v___f_779_, 4, v_toTopVar_704_);
v___x_780_ = l_Lean_Meta_Sym_Arith_isIntCastInst___redArg(v_inst_707_, v_inst_709_, v_inst_710_, v_inst_711_, v_arg_727_);
v___x_781_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_780_, v___f_779_);
return v___x_781_;
}
}
else
{
lean_object* v___f_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v___x_728_);
lean_dec_ref(v___x_724_);
lean_dec(v___f_716_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_708_);
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__16___boxed), 6, 5);
lean_closure_set(v___f_782_, 0, v_asTopVar_715_);
lean_closure_set(v___f_782_, 1, v_e_705_);
lean_closure_set(v___f_782_, 2, v_arg_731_);
lean_closure_set(v___f_782_, 3, v_toPure_706_);
lean_closure_set(v___f_782_, 4, v_toTopVar_704_);
v___x_783_ = l_Lean_Meta_Sym_Arith_isNatCastInst___redArg(v_inst_707_, v_inst_709_, v_inst_710_, v_inst_711_, v_arg_727_);
v___x_784_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_783_, v___f_782_);
return v___x_784_;
}
}
else
{
lean_dec_ref(v___x_728_);
lean_dec_ref(v___x_724_);
lean_dec_ref(v___x_718_);
lean_dec(v___f_716_);
lean_dec(v_toBind_714_);
lean_dec(v_asVar_713_);
lean_dec(v_toVar_712_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec(v_toTopVar_704_);
if (lean_obj_tag(v_arg_727_) == 9)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v_arg_727_, 0);
lean_inc_ref(v_a_785_);
lean_dec_ref_known(v_arg_727_, 1);
if (lean_obj_tag(v_a_785_) == 0)
{
lean_object* v_val_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_asTopVar_715_);
lean_dec_ref(v_e_705_);
v_val_786_ = lean_ctor_get(v_a_785_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_a_785_);
if (v_isSharedCheck_796_ == 0)
{
v___x_788_ = v_a_785_;
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_val_786_);
lean_dec(v_a_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_nat_to_int(v_val_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_795_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___x_794_ = lean_apply_2(v_toPure_706_, lean_box(0), v___x_793_);
return v___x_794_;
}
}
}
else
{
lean_object* v___x_797_; 
lean_dec_ref(v_a_785_);
lean_dec(v_toPure_706_);
v___x_797_ = lean_apply_1(v_asTopVar_715_, v_e_705_);
return v___x_797_;
}
}
else
{
lean_object* v___x_798_; 
lean_dec_ref(v_arg_727_);
lean_dec(v_toPure_706_);
v___x_798_ = lean_apply_1(v_asTopVar_715_, v_e_705_);
return v___x_798_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18___boxed(lean_object* v_toTopVar_799_, lean_object* v_e_800_, lean_object* v_toPure_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_toVar_807_, lean_object* v_asVar_808_, lean_object* v_toBind_809_, lean_object* v_asTopVar_810_, lean_object* v___f_811_, lean_object* v_____x_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18(v_toTopVar_799_, v_e_800_, v_toPure_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_inst_805_, v_inst_806_, v_toVar_807_, v_asVar_808_, v_toBind_809_, v_asTopVar_810_, v___f_811_, v_____x_812_);
lean_dec_ref(v_____x_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_e_821_, uint8_t v_skipVar_822_){
_start:
{
lean_object* v_toApplicative_823_; lean_object* v_toBind_824_; lean_object* v_toPure_825_; lean_object* v___f_826_; lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v_asVar_829_; lean_object* v_toVar_830_; lean_object* v___x_831_; lean_object* v_toTopVar_832_; lean_object* v_asTopVar_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_toApplicative_823_ = lean_ctor_get(v_inst_817_, 0);
v_toBind_824_ = lean_ctor_get(v_inst_817_, 1);
lean_inc_n(v_toBind_824_, 6);
v_toPure_825_ = lean_ctor_get(v_toApplicative_823_, 1);
lean_inc_n(v_toPure_825_, 5);
v___f_826_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_826_, 0, v_toPure_825_);
v___f_827_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_827_, 0, v_toPure_825_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_828_, 0, v_toPure_825_);
lean_inc(v_inst_814_);
lean_inc_ref(v___f_828_);
lean_inc(v_inst_820_);
v_asVar_829_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__4), 5, 4);
lean_closure_set(v_asVar_829_, 0, v_inst_820_);
lean_closure_set(v_asVar_829_, 1, v_toBind_824_);
lean_closure_set(v_asVar_829_, 2, v___f_828_);
lean_closure_set(v_asVar_829_, 3, v_inst_814_);
v_toVar_830_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6), 4, 3);
lean_closure_set(v_toVar_830_, 0, v_inst_820_);
lean_closure_set(v_toVar_830_, 1, v_toBind_824_);
lean_closure_set(v_toVar_830_, 2, v___f_828_);
v___x_831_ = lean_box(v_skipVar_822_);
lean_inc_ref(v_toVar_830_);
v_toTopVar_832_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v_toTopVar_832_, 0, v___x_831_);
lean_closure_set(v_toTopVar_832_, 1, v_toVar_830_);
lean_closure_set(v_toTopVar_832_, 2, v_toBind_824_);
lean_closure_set(v_toTopVar_832_, 3, v___f_827_);
lean_closure_set(v_toTopVar_832_, 4, v_toPure_825_);
lean_inc_ref(v_toTopVar_832_);
v_asTopVar_833_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__8), 4, 3);
lean_closure_set(v_asTopVar_833_, 0, v_toTopVar_832_);
lean_closure_set(v_asTopVar_833_, 1, v_inst_814_);
lean_closure_set(v_asTopVar_833_, 2, v_toBind_824_);
lean_inc(v_inst_815_);
lean_inc_ref(v_e_821_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__18___boxed), 14, 13);
lean_closure_set(v___f_834_, 0, v_toTopVar_832_);
lean_closure_set(v___f_834_, 1, v_e_821_);
lean_closure_set(v___f_834_, 2, v_toPure_825_);
lean_closure_set(v___f_834_, 3, v_inst_815_);
lean_closure_set(v___f_834_, 4, v_inst_816_);
lean_closure_set(v___f_834_, 5, v_inst_817_);
lean_closure_set(v___f_834_, 6, v_inst_818_);
lean_closure_set(v___f_834_, 7, v_inst_819_);
lean_closure_set(v___f_834_, 8, v_toVar_830_);
lean_closure_set(v___f_834_, 9, v_asVar_829_);
lean_closure_set(v___f_834_, 10, v_toBind_824_);
lean_closure_set(v___f_834_, 11, v_asTopVar_833_);
lean_closure_set(v___f_834_, 12, v___f_826_);
v___x_835_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_835_, 0, v_e_821_);
v___x_836_ = lean_apply_2(v_inst_815_, lean_box(0), v___x_835_);
v___x_837_ = lean_apply_4(v_toBind_824_, lean_box(0), lean_box(0), v___x_836_, v___f_834_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___boxed(lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_e_845_, lean_object* v_skipVar_846_){
_start:
{
uint8_t v_skipVar_boxed_847_; lean_object* v_res_848_; 
v_skipVar_boxed_847_ = lean_unbox(v_skipVar_846_);
v_res_848_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_838_, v_inst_839_, v_inst_840_, v_inst_841_, v_inst_842_, v_inst_843_, v_inst_844_, v_e_845_, v_skipVar_boxed_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f(lean_object* v_m_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_e_857_, uint8_t v_skipVar_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg(v_inst_850_, v_inst_851_, v_inst_852_, v_inst_853_, v_inst_854_, v_inst_855_, v_inst_856_, v_e_857_, v_skipVar_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifyRing_x3f___boxed(lean_object* v_m_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_e_868_, lean_object* v_skipVar_869_){
_start:
{
uint8_t v_skipVar_boxed_870_; lean_object* v_res_871_; 
v_skipVar_boxed_870_ = lean_unbox(v_skipVar_869_);
v_res_871_ = l_Lean_Meta_Sym_Arith_reifyRing_x3f(v_m_860_, v_inst_861_, v_inst_862_, v_inst_863_, v_inst_864_, v_inst_865_, v_inst_866_, v_inst_867_, v_e_868_, v_skipVar_boxed_870_);
return v_res_871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__0));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(lean_object* v_inst_875_, lean_object* v_e_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1, &l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg___closed__1);
v___x_878_ = l_Lean_indentExpr(v_e_876_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_reportIssueIfVerbose___boxed), 8, 1);
lean_closure_set(v___x_880_, 0, v___x_879_);
v___x_881_ = lean_apply_2(v_inst_875_, lean_box(0), v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue(lean_object* v_m_882_, lean_object* v_inst_883_, lean_object* v_e_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_883_, v_e_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(lean_object* v_arg_886_, lean_object* v_asVar_887_, lean_object* v_e_888_, lean_object* v_arg_889_, lean_object* v_toPure_890_, lean_object* v_toVar_891_, lean_object* v_____do__lift_892_){
_start:
{
lean_object* v___x_893_; size_t v___x_894_; size_t v___x_895_; uint8_t v___x_896_; 
v___x_893_ = l_Lean_Expr_appArg_x21(v_____do__lift_892_);
v___x_894_ = lean_ptr_addr(v___x_893_);
lean_dec_ref(v___x_893_);
v___x_895_ = lean_ptr_addr(v_arg_886_);
v___x_896_ = lean_usize_dec_eq(v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_dec(v_toVar_891_);
lean_dec(v_toPure_890_);
v___x_897_ = lean_apply_1(v_asVar_887_, v_e_888_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; 
lean_dec(v_asVar_887_);
v___x_898_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_889_);
if (lean_obj_tag(v___x_898_) == 1)
{
lean_object* v_val_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_toVar_891_);
lean_dec_ref(v_e_888_);
v_val_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_908_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_val_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = lean_nat_to_int(v_val_899_);
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 0);
lean_ctor_set(v___x_901_, 0, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_907_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; 
v___x_906_ = lean_apply_2(v_toPure_890_, lean_box(0), v___x_905_);
return v___x_906_;
}
}
}
else
{
lean_object* v___x_909_; 
lean_dec(v___x_898_);
lean_dec(v_toPure_890_);
v___x_909_ = lean_apply_1(v_toVar_891_, v_e_888_);
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed(lean_object* v_arg_910_, lean_object* v_asVar_911_, lean_object* v_e_912_, lean_object* v_arg_913_, lean_object* v_toPure_914_, lean_object* v_toVar_915_, lean_object* v_____do__lift_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6(v_arg_910_, v_asVar_911_, v_e_912_, v_arg_913_, v_toPure_914_, v_toVar_915_, v_____do__lift_916_);
lean_dec_ref(v_____do__lift_916_);
lean_dec_ref(v_arg_913_);
lean_dec_ref(v_arg_910_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(lean_object* v_arg_918_, lean_object* v_asVar_919_, lean_object* v_e_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_toVar_926_, lean_object* v_arg_927_, lean_object* v_toBind_928_, lean_object* v___f_929_, lean_object* v_____do__lift_930_){
_start:
{
lean_object* v___x_931_; size_t v___x_932_; size_t v___x_933_; uint8_t v___x_934_; 
v___x_931_ = l_Lean_Expr_appArg_x21(v_____do__lift_930_);
v___x_932_ = lean_ptr_addr(v___x_931_);
lean_dec_ref(v___x_931_);
v___x_933_ = lean_ptr_addr(v_arg_918_);
v___x_934_ = lean_usize_dec_eq(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec(v___f_929_);
lean_dec(v_toBind_928_);
lean_dec_ref(v_arg_927_);
lean_dec(v_toVar_926_);
lean_dec_ref(v_inst_925_);
lean_dec_ref(v_inst_924_);
lean_dec_ref(v_inst_923_);
lean_dec_ref(v_inst_922_);
lean_dec(v_inst_921_);
v___x_935_ = lean_apply_1(v_asVar_919_, v_e_920_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref(v_e_920_);
v___x_936_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_921_, v_inst_922_, v_inst_923_, v_inst_924_, v_inst_925_, v_toVar_926_, v_asVar_919_, v_arg_927_);
v___x_937_ = lean_apply_4(v_toBind_928_, lean_box(0), lean_box(0), v___x_936_, v___f_929_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed(lean_object* v_arg_938_, lean_object* v_asVar_939_, lean_object* v_e_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_toVar_946_, lean_object* v_arg_947_, lean_object* v_toBind_948_, lean_object* v___f_949_, lean_object* v_____do__lift_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0(v_arg_938_, v_asVar_939_, v_e_940_, v_inst_941_, v_inst_942_, v_inst_943_, v_inst_944_, v_inst_945_, v_toVar_946_, v_arg_947_, v_toBind_948_, v___f_949_, v_____do__lift_950_);
lean_dec_ref(v_____do__lift_950_);
lean_dec_ref(v_arg_938_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3(lean_object* v_toPure_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_toVar_958_, lean_object* v_asVar_959_, lean_object* v_arg_960_, lean_object* v_toBind_961_, lean_object* v_____do__lift_962_){
_start:
{
lean_object* v___f_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___f_963_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_963_, 0, v_____do__lift_962_);
lean_closure_set(v___f_963_, 1, v_toPure_952_);
v___x_964_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_953_, v_inst_954_, v_inst_955_, v_inst_956_, v_inst_957_, v_toVar_958_, v_asVar_959_, v_arg_960_);
v___x_965_ = lean_apply_4(v_toBind_961_, lean_box(0), lean_box(0), v___x_964_, v___f_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2(lean_object* v_toVar_966_, lean_object* v_e_967_, lean_object* v_toPure_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_asVar_974_, lean_object* v_toBind_975_, lean_object* v_____x_976_){
_start:
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = l_Lean_Expr_cleanupAnnotations(v_____x_976_);
v___x_978_ = l_Lean_Expr_isApp(v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_dec_ref(v___x_977_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
lean_dec(v_toPure_968_);
v___x_979_ = lean_apply_1(v_toVar_966_, v_e_967_);
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
lean_dec_ref(v___x_977_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
lean_dec(v_toPure_968_);
v___x_982_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_980_);
v___x_984_ = l_Lean_Expr_isApp(v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_980_);
lean_dec_ref(v___x_977_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
lean_dec(v_toPure_968_);
v___x_985_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_985_;
}
else
{
lean_object* v_arg_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_arg_986_ = lean_ctor_get(v___x_980_, 1);
lean_inc_ref(v_arg_986_);
lean_dec_ref(v___x_980_);
v___x_987_ = l_Lean_Expr_appFnCleanup___redArg(v___x_983_);
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_989_ = l_Lean_Expr_isConstOf(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v_arg_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_arg_990_ = lean_ctor_get(v___x_977_, 1);
lean_inc_ref(v_arg_990_);
lean_dec_ref(v___x_977_);
v___x_991_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_992_ = l_Lean_Expr_isConstOf(v___x_987_, v___x_991_);
if (v___x_992_ == 0)
{
uint8_t v___x_993_; 
v___x_993_ = l_Lean_Expr_isApp(v___x_987_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
lean_dec_ref(v_arg_990_);
lean_dec_ref(v___x_987_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v___x_983_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
lean_dec(v_toPure_968_);
v___x_994_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_987_);
lean_dec_ref(v___x_987_);
v___x_996_ = l_Lean_Expr_isApp(v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
lean_dec_ref(v___x_995_);
lean_dec_ref(v_arg_990_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v___x_983_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
lean_dec(v_toPure_968_);
v___x_997_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_997_;
}
else
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = l_Lean_Expr_appFnCleanup___redArg(v___x_995_);
lean_dec_ref(v___x_995_);
v___x_999_ = l_Lean_Expr_isApp(v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref(v___x_998_);
lean_dec_ref(v_arg_990_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v___x_983_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
lean_dec(v_toPure_968_);
v___x_1000_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_1000_;
}
else
{
lean_object* v_arg_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_arg_1001_ = lean_ctor_get(v___x_983_, 1);
lean_inc_ref(v_arg_1001_);
lean_dec_ref(v___x_983_);
v___x_1002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_998_);
lean_dec_ref(v___x_998_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_1004_ = l_Lean_Expr_isConstOf(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_1006_ = l_Lean_Expr_isConstOf(v___x_1002_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_1008_ = l_Lean_Expr_isConstOf(v___x_1002_, v___x_1007_);
lean_dec_ref(v___x_1002_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_dec_ref(v_arg_1001_);
lean_dec_ref(v_arg_990_);
lean_dec_ref(v_arg_986_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
lean_dec(v_toPure_968_);
v___x_1009_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_1009_;
}
else
{
lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_inc_n(v_toBind_975_, 2);
lean_inc(v_asVar_974_);
lean_inc(v_toVar_966_);
lean_inc_ref_n(v_inst_973_, 2);
lean_inc_ref_n(v_inst_972_, 2);
lean_inc_ref_n(v_inst_971_, 2);
lean_inc_ref_n(v_inst_970_, 2);
lean_inc_n(v_inst_969_, 2);
v___f_1010_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_1010_, 0, v_toPure_968_);
lean_closure_set(v___f_1010_, 1, v_inst_969_);
lean_closure_set(v___f_1010_, 2, v_inst_970_);
lean_closure_set(v___f_1010_, 3, v_inst_971_);
lean_closure_set(v___f_1010_, 4, v_inst_972_);
lean_closure_set(v___f_1010_, 5, v_inst_973_);
lean_closure_set(v___f_1010_, 6, v_toVar_966_);
lean_closure_set(v___f_1010_, 7, v_asVar_974_);
lean_closure_set(v___f_1010_, 8, v_arg_990_);
lean_closure_set(v___f_1010_, 9, v_toBind_975_);
v___f_1011_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_1011_, 0, v_arg_1001_);
lean_closure_set(v___f_1011_, 1, v_asVar_974_);
lean_closure_set(v___f_1011_, 2, v_e_967_);
lean_closure_set(v___f_1011_, 3, v_inst_969_);
lean_closure_set(v___f_1011_, 4, v_inst_970_);
lean_closure_set(v___f_1011_, 5, v_inst_971_);
lean_closure_set(v___f_1011_, 6, v_inst_972_);
lean_closure_set(v___f_1011_, 7, v_inst_973_);
lean_closure_set(v___f_1011_, 8, v_toVar_966_);
lean_closure_set(v___f_1011_, 9, v_arg_986_);
lean_closure_set(v___f_1011_, 10, v_toBind_975_);
lean_closure_set(v___f_1011_, 11, v___f_1010_);
v___x_1012_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_969_, v_inst_970_, v_inst_971_, v_inst_972_, v_inst_973_);
v___x_1013_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v___x_1012_, v___f_1011_);
return v___x_1013_;
}
}
else
{
lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v___x_1002_);
lean_inc_n(v_toBind_975_, 2);
lean_inc(v_asVar_974_);
lean_inc(v_toVar_966_);
lean_inc_ref_n(v_inst_973_, 2);
lean_inc_ref_n(v_inst_972_, 2);
lean_inc_ref_n(v_inst_971_, 2);
lean_inc_ref_n(v_inst_970_, 2);
lean_inc_n(v_inst_969_, 2);
v___f_1014_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__3), 11, 10);
lean_closure_set(v___f_1014_, 0, v_toPure_968_);
lean_closure_set(v___f_1014_, 1, v_inst_969_);
lean_closure_set(v___f_1014_, 2, v_inst_970_);
lean_closure_set(v___f_1014_, 3, v_inst_971_);
lean_closure_set(v___f_1014_, 4, v_inst_972_);
lean_closure_set(v___f_1014_, 5, v_inst_973_);
lean_closure_set(v___f_1014_, 6, v_toVar_966_);
lean_closure_set(v___f_1014_, 7, v_asVar_974_);
lean_closure_set(v___f_1014_, 8, v_arg_990_);
lean_closure_set(v___f_1014_, 9, v_toBind_975_);
v___f_1015_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_1015_, 0, v_arg_1001_);
lean_closure_set(v___f_1015_, 1, v_asVar_974_);
lean_closure_set(v___f_1015_, 2, v_e_967_);
lean_closure_set(v___f_1015_, 3, v_inst_969_);
lean_closure_set(v___f_1015_, 4, v_inst_970_);
lean_closure_set(v___f_1015_, 5, v_inst_971_);
lean_closure_set(v___f_1015_, 6, v_inst_972_);
lean_closure_set(v___f_1015_, 7, v_inst_973_);
lean_closure_set(v___f_1015_, 8, v_toVar_966_);
lean_closure_set(v___f_1015_, 9, v_arg_986_);
lean_closure_set(v___f_1015_, 10, v_toBind_975_);
lean_closure_set(v___f_1015_, 11, v___f_1014_);
v___x_1016_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_969_, v_inst_970_, v_inst_971_, v_inst_972_, v_inst_973_);
v___x_1017_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v___x_1016_, v___f_1015_);
return v___x_1017_;
}
}
else
{
lean_object* v___x_1018_; 
lean_dec_ref(v___x_1002_);
v___x_1018_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_990_);
lean_dec_ref(v_arg_990_);
if (lean_obj_tag(v___x_1018_) == 1)
{
lean_object* v_val_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_val_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_val_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___f_1020_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__9), 3, 2);
lean_closure_set(v___f_1020_, 0, v_val_1019_);
lean_closure_set(v___f_1020_, 1, v_toPure_968_);
lean_inc(v_toBind_975_);
lean_inc_ref(v_inst_973_);
lean_inc_ref(v_inst_972_);
lean_inc_ref(v_inst_971_);
lean_inc_ref(v_inst_970_);
lean_inc(v_inst_969_);
v___f_1021_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_1021_, 0, v_arg_1001_);
lean_closure_set(v___f_1021_, 1, v_asVar_974_);
lean_closure_set(v___f_1021_, 2, v_e_967_);
lean_closure_set(v___f_1021_, 3, v_inst_969_);
lean_closure_set(v___f_1021_, 4, v_inst_970_);
lean_closure_set(v___f_1021_, 5, v_inst_971_);
lean_closure_set(v___f_1021_, 6, v_inst_972_);
lean_closure_set(v___f_1021_, 7, v_inst_973_);
lean_closure_set(v___f_1021_, 8, v_toVar_966_);
lean_closure_set(v___f_1021_, 9, v_arg_986_);
lean_closure_set(v___f_1021_, 10, v_toBind_975_);
lean_closure_set(v___f_1021_, 11, v___f_1020_);
v___x_1022_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_969_, v_inst_970_, v_inst_971_, v_inst_972_, v_inst_973_);
v___x_1023_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v___x_1022_, v___f_1021_);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; 
lean_dec(v___x_1018_);
lean_dec_ref(v_arg_1001_);
lean_dec_ref(v_arg_986_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
lean_dec(v_toPure_968_);
v___x_1024_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_1024_;
}
}
}
}
}
}
else
{
lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec_ref(v___x_987_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v_inst_970_);
v___f_1025_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_1025_, 0, v_arg_986_);
lean_closure_set(v___f_1025_, 1, v_asVar_974_);
lean_closure_set(v___f_1025_, 2, v_e_967_);
lean_closure_set(v___f_1025_, 3, v_arg_990_);
lean_closure_set(v___f_1025_, 4, v_toPure_968_);
lean_closure_set(v___f_1025_, 5, v_toVar_966_);
v___x_1026_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_969_, v_inst_971_, v_inst_972_, v_inst_973_);
v___x_1027_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v___x_1026_, v___f_1025_);
return v___x_1027_;
}
}
else
{
lean_dec_ref(v___x_987_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_977_);
lean_dec(v_toBind_975_);
lean_dec(v_asVar_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_inst_969_);
if (lean_obj_tag(v_arg_986_) == 9)
{
lean_object* v_a_1028_; 
v_a_1028_ = lean_ctor_get(v_arg_986_, 0);
lean_inc_ref(v_a_1028_);
lean_dec_ref_known(v_arg_986_, 1);
if (lean_obj_tag(v_a_1028_) == 0)
{
lean_object* v_val_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_e_967_);
lean_dec(v_toVar_966_);
v_val_1029_ = lean_ctor_get(v_a_1028_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_1028_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1031_ = v_a_1028_;
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_val_1029_);
lean_dec(v_a_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_nat_to_int(v_val_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_apply_2(v_toPure_968_, lean_box(0), v___x_1035_);
return v___x_1036_;
}
}
}
else
{
lean_object* v___x_1039_; 
lean_dec_ref(v_a_1028_);
lean_dec(v_toPure_968_);
v___x_1039_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_1039_;
}
}
else
{
lean_object* v___x_1040_; 
lean_dec_ref(v_arg_986_);
lean_dec(v_toPure_968_);
v___x_1040_ = lean_apply_1(v_toVar_966_, v_e_967_);
return v___x_1040_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2___boxed(lean_object* v_toVar_1041_, lean_object* v_e_1042_, lean_object* v_toPure_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_asVar_1049_, lean_object* v_toBind_1050_, lean_object* v_____x_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2(v_toVar_1041_, v_e_1042_, v_toPure_1043_, v_inst_1044_, v_inst_1045_, v_inst_1046_, v_inst_1047_, v_inst_1048_, v_asVar_1049_, v_toBind_1050_, v_____x_1051_);
lean_dec_ref(v_____x_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_toVar_1058_, lean_object* v_asVar_1059_, lean_object* v_e_1060_){
_start:
{
lean_object* v_toApplicative_1061_; lean_object* v_toBind_1062_; lean_object* v_toPure_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; 
v_toApplicative_1061_ = lean_ctor_get(v_inst_1055_, 0);
v_toBind_1062_ = lean_ctor_get(v_inst_1055_, 1);
lean_inc_n(v_toBind_1062_, 2);
v_toPure_1063_ = lean_ctor_get(v_toApplicative_1061_, 1);
lean_inc(v_toPure_1063_);
lean_inc_ref(v_e_1060_);
v___x_1064_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_1064_, 0, v_e_1060_);
lean_inc(v_inst_1053_);
v___x_1065_ = lean_apply_2(v_inst_1053_, lean_box(0), v___x_1064_);
v___f_1066_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_1066_, 0, v_toVar_1058_);
lean_closure_set(v___f_1066_, 1, v_e_1060_);
lean_closure_set(v___f_1066_, 2, v_toPure_1063_);
lean_closure_set(v___f_1066_, 3, v_inst_1053_);
lean_closure_set(v___f_1066_, 4, v_inst_1054_);
lean_closure_set(v___f_1066_, 5, v_inst_1055_);
lean_closure_set(v___f_1066_, 6, v_inst_1056_);
lean_closure_set(v___f_1066_, 7, v_inst_1057_);
lean_closure_set(v___f_1066_, 8, v_asVar_1059_);
lean_closure_set(v___f_1066_, 9, v_toBind_1062_);
v___x_1067_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v___x_1065_, v___f_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg___lam__1(lean_object* v_toPure_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_toVar_1074_, lean_object* v_asVar_1075_, lean_object* v_arg_1076_, lean_object* v_toBind_1077_, lean_object* v_____do__lift_1078_){
_start:
{
lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___f_1079_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1079_, 0, v_____do__lift_1078_);
lean_closure_set(v___f_1079_, 1, v_toPure_1068_);
v___x_1080_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1069_, v_inst_1070_, v_inst_1071_, v_inst_1072_, v_inst_1073_, v_toVar_1074_, v_asVar_1075_, v_arg_1076_);
v___x_1081_ = lean_apply_4(v_toBind_1077_, lean_box(0), lean_box(0), v___x_1080_, v___f_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go(lean_object* v_m_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_toVar_1088_, lean_object* v_asVar_1089_, lean_object* v_e_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1083_, v_inst_1084_, v_inst_1085_, v_inst_1086_, v_inst_1087_, v_toVar_1088_, v_asVar_1089_, v_e_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3(lean_object* v_inst_1092_, lean_object* v_toBind_1093_, lean_object* v___f_1094_, lean_object* v_inst_1095_, lean_object* v_e_1096_){
_start:
{
lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_inc(v_toBind_1093_);
lean_inc_ref(v_e_1096_);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1097_, 0, v_inst_1092_);
lean_closure_set(v___f_1097_, 1, v_e_1096_);
lean_closure_set(v___f_1097_, 2, v_toBind_1093_);
lean_closure_set(v___f_1097_, 3, v___f_1094_);
v___x_1098_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_1095_, v_e_1096_);
v___x_1099_ = lean_apply_4(v_toBind_1093_, lean_box(0), lean_box(0), v___x_1098_, v___f_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2(lean_object* v_toVar_1100_, lean_object* v_toBind_1101_, lean_object* v___f_1102_, lean_object* v_e_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_apply_1(v_toVar_1100_, v_e_1103_);
v___x_1105_ = lean_apply_4(v_toBind_1101_, lean_box(0), lean_box(0), v___x_1104_, v___f_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1(lean_object* v_toTopVar_1106_, lean_object* v_inst_1107_, lean_object* v_toBind_1108_, lean_object* v_e_1109_){
_start:
{
lean_object* v___f_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_inc_ref(v_e_1109_);
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1110_, 0, v_toTopVar_1106_);
lean_closure_set(v___f_1110_, 1, v_e_1109_);
v___x_1111_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reportSemiringAppIssue___redArg(v_inst_1107_, v_e_1109_);
v___x_1112_ = lean_apply_4(v_toBind_1108_, lean_box(0), lean_box(0), v___x_1111_, v___f_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4(lean_object* v_toPure_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_toVar_1119_, lean_object* v_asVar_1120_, lean_object* v_arg_1121_, lean_object* v_toBind_1122_, lean_object* v_____do__lift_1123_){
_start:
{
lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__9), 3, 2);
lean_closure_set(v___f_1124_, 0, v_____do__lift_1123_);
lean_closure_set(v___f_1124_, 1, v_toPure_1113_);
v___x_1125_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1114_, v_inst_1115_, v_inst_1116_, v_inst_1117_, v_inst_1118_, v_toVar_1119_, v_asVar_1120_, v_arg_1121_);
v___x_1126_ = lean_apply_4(v_toBind_1122_, lean_box(0), lean_box(0), v___x_1125_, v___f_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(lean_object* v_arg_1127_, lean_object* v_asTopVar_1128_, lean_object* v_e_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_toVar_1135_, lean_object* v_asVar_1136_, lean_object* v_arg_1137_, lean_object* v_toBind_1138_, lean_object* v___f_1139_, lean_object* v_____do__lift_1140_){
_start:
{
lean_object* v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1141_ = l_Lean_Expr_appArg_x21(v_____do__lift_1140_);
v___x_1142_ = lean_ptr_addr(v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1143_ = lean_ptr_addr(v_arg_1127_);
v___x_1144_ = lean_usize_dec_eq(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
lean_dec(v___f_1139_);
lean_dec(v_toBind_1138_);
lean_dec_ref(v_arg_1137_);
lean_dec(v_asVar_1136_);
lean_dec(v_toVar_1135_);
lean_dec_ref(v_inst_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_inst_1132_);
lean_dec_ref(v_inst_1131_);
lean_dec(v_inst_1130_);
v___x_1145_ = lean_apply_1(v_asTopVar_1128_, v_e_1129_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec_ref(v_e_1129_);
lean_dec(v_asTopVar_1128_);
v___x_1146_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1130_, v_inst_1131_, v_inst_1132_, v_inst_1133_, v_inst_1134_, v_toVar_1135_, v_asVar_1136_, v_arg_1137_);
v___x_1147_ = lean_apply_4(v_toBind_1138_, lean_box(0), lean_box(0), v___x_1146_, v___f_1139_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed(lean_object* v_arg_1148_, lean_object* v_asTopVar_1149_, lean_object* v_e_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_toVar_1156_, lean_object* v_asVar_1157_, lean_object* v_arg_1158_, lean_object* v_toBind_1159_, lean_object* v___f_1160_, lean_object* v_____do__lift_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0(v_arg_1148_, v_asTopVar_1149_, v_e_1150_, v_inst_1151_, v_inst_1152_, v_inst_1153_, v_inst_1154_, v_inst_1155_, v_toVar_1156_, v_asVar_1157_, v_arg_1158_, v_toBind_1159_, v___f_1160_, v_____do__lift_1161_);
lean_dec_ref(v_____do__lift_1161_);
lean_dec_ref(v_arg_1148_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6(lean_object* v_toPure_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_toVar_1169_, lean_object* v_asVar_1170_, lean_object* v_arg_1171_, lean_object* v_toBind_1172_, lean_object* v_____do__lift_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__12), 3, 2);
lean_closure_set(v___f_1174_, 0, v_____do__lift_1173_);
lean_closure_set(v___f_1174_, 1, v_toPure_1163_);
v___x_1175_ = l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifySemiring_x3f_go___redArg(v_inst_1164_, v_inst_1165_, v_inst_1166_, v_inst_1167_, v_inst_1168_, v_toVar_1169_, v_asVar_1170_, v_arg_1171_);
v___x_1176_ = lean_apply_4(v_toBind_1172_, lean_box(0), lean_box(0), v___x_1175_, v___f_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(lean_object* v_arg_1177_, lean_object* v_asTopVar_1178_, lean_object* v_e_1179_, lean_object* v_arg_1180_, lean_object* v_toPure_1181_, lean_object* v_toTopVar_1182_, lean_object* v_____do__lift_1183_){
_start:
{
lean_object* v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1184_ = l_Lean_Expr_appArg_x21(v_____do__lift_1183_);
v___x_1185_ = lean_ptr_addr(v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_ptr_addr(v_arg_1177_);
v___x_1187_ = lean_usize_dec_eq(v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
lean_dec(v_toTopVar_1182_);
lean_dec(v_toPure_1181_);
v___x_1188_ = lean_apply_1(v_asTopVar_1178_, v_e_1179_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; 
lean_dec(v_asTopVar_1178_);
v___x_1189_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1180_);
if (lean_obj_tag(v___x_1189_) == 1)
{
lean_object* v_val_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_toTopVar_1182_);
lean_dec_ref(v_e_1179_);
v_val_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1200_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_val_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1200_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = lean_nat_to_int(v_val_1190_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_apply_2(v_toPure_1181_, lean_box(0), v___x_1197_);
return v___x_1198_;
}
}
}
else
{
lean_object* v___x_1201_; 
lean_dec(v___x_1189_);
lean_dec(v_toPure_1181_);
v___x_1201_ = lean_apply_1(v_toTopVar_1182_, v_e_1179_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed(lean_object* v_arg_1202_, lean_object* v_asTopVar_1203_, lean_object* v_e_1204_, lean_object* v_arg_1205_, lean_object* v_toPure_1206_, lean_object* v_toTopVar_1207_, lean_object* v_____do__lift_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9(v_arg_1202_, v_asTopVar_1203_, v_e_1204_, v_arg_1205_, v_toPure_1206_, v_toTopVar_1207_, v_____do__lift_1208_);
lean_dec_ref(v_____do__lift_1208_);
lean_dec_ref(v_arg_1205_);
lean_dec_ref(v_arg_1202_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5(lean_object* v_toTopVar_1210_, lean_object* v_e_1211_, lean_object* v_toPure_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_toVar_1218_, lean_object* v_asVar_1219_, lean_object* v_toBind_1220_, lean_object* v_asTopVar_1221_, lean_object* v_____x_1222_){
_start:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = l_Lean_Expr_cleanupAnnotations(v_____x_1222_);
v___x_1224_ = l_Lean_Expr_isApp(v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v___x_1223_);
lean_dec(v_asTopVar_1221_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec(v_toPure_1212_);
v___x_1225_ = lean_apply_1(v_toTopVar_1210_, v_e_1211_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1223_);
v___x_1227_ = l_Lean_Expr_isApp(v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1223_);
lean_dec(v_asTopVar_1221_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec(v_toPure_1212_);
v___x_1228_ = lean_apply_1(v_toTopVar_1210_, v_e_1211_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1226_);
v___x_1230_ = l_Lean_Expr_isApp(v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1223_);
lean_dec(v_asTopVar_1221_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec(v_toPure_1212_);
v___x_1231_ = lean_apply_1(v_toTopVar_1210_, v_e_1211_);
return v___x_1231_;
}
else
{
lean_object* v_arg_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_arg_1232_ = lean_ctor_get(v___x_1226_, 1);
lean_inc_ref(v_arg_1232_);
lean_dec_ref(v___x_1226_);
v___x_1233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1229_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__4));
v___x_1235_ = l_Lean_Expr_isConstOf(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v_arg_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_arg_1236_ = lean_ctor_get(v___x_1223_, 1);
lean_inc_ref(v_arg_1236_);
lean_dec_ref(v___x_1223_);
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__7));
v___x_1238_ = l_Lean_Expr_isConstOf(v___x_1233_, v___x_1237_);
if (v___x_1238_ == 0)
{
uint8_t v___x_1239_; 
v___x_1239_ = l_Lean_Expr_isApp(v___x_1233_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v_arg_1236_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v_arg_1232_);
lean_dec_ref(v___x_1229_);
lean_dec(v_asTopVar_1221_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec(v_toPure_1212_);
v___x_1240_ = lean_apply_1(v_toTopVar_1210_, v_e_1211_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1233_);
lean_dec_ref(v___x_1233_);
v___x_1242_ = l_Lean_Expr_isApp(v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec_ref(v___x_1241_);
lean_dec_ref(v_arg_1236_);
lean_dec_ref(v_arg_1232_);
lean_dec_ref(v___x_1229_);
lean_dec(v_asTopVar_1221_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec(v_toPure_1212_);
v___x_1243_ = lean_apply_1(v_toTopVar_1210_, v_e_1211_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1245_ = l_Lean_Expr_isApp(v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_arg_1236_);
lean_dec_ref(v_arg_1232_);
lean_dec_ref(v___x_1229_);
lean_dec(v_asTopVar_1221_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec(v_toPure_1212_);
v___x_1246_ = lean_apply_1(v_toTopVar_1210_, v_e_1211_);
return v___x_1246_;
}
else
{
lean_object* v_arg_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_arg_1247_ = lean_ctor_get(v___x_1229_, 1);
lean_inc_ref(v_arg_1247_);
lean_dec_ref(v___x_1229_);
v___x_1248_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1244_);
lean_dec_ref(v___x_1244_);
v___x_1249_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__16));
v___x_1250_ = l_Lean_Expr_isConstOf(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__22));
v___x_1252_ = l_Lean_Expr_isConstOf(v___x_1248_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Reify_0__Lean_Meta_Sym_Arith_reifyRing_x3f_go___redArg___lam__10___closed__25));
v___x_1254_ = l_Lean_Expr_isConstOf(v___x_1248_, v___x_1253_);
lean_dec_ref(v___x_1248_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1236_);
lean_dec_ref(v_arg_1232_);
lean_dec(v_asTopVar_1221_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec(v_toPure_1212_);
v___x_1255_ = lean_apply_1(v_toTopVar_1210_, v_e_1211_);
return v___x_1255_;
}
else
{
lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v_toTopVar_1210_);
lean_inc_n(v_toBind_1220_, 2);
lean_inc(v_asVar_1219_);
lean_inc(v_toVar_1218_);
lean_inc_ref_n(v_inst_1217_, 2);
lean_inc_ref_n(v_inst_1216_, 2);
lean_inc_ref_n(v_inst_1215_, 2);
lean_inc_ref_n(v_inst_1214_, 2);
lean_inc_n(v_inst_1213_, 2);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__4), 11, 10);
lean_closure_set(v___f_1256_, 0, v_toPure_1212_);
lean_closure_set(v___f_1256_, 1, v_inst_1213_);
lean_closure_set(v___f_1256_, 2, v_inst_1214_);
lean_closure_set(v___f_1256_, 3, v_inst_1215_);
lean_closure_set(v___f_1256_, 4, v_inst_1216_);
lean_closure_set(v___f_1256_, 5, v_inst_1217_);
lean_closure_set(v___f_1256_, 6, v_toVar_1218_);
lean_closure_set(v___f_1256_, 7, v_asVar_1219_);
lean_closure_set(v___f_1256_, 8, v_arg_1236_);
lean_closure_set(v___f_1256_, 9, v_toBind_1220_);
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1257_, 0, v_arg_1247_);
lean_closure_set(v___f_1257_, 1, v_asTopVar_1221_);
lean_closure_set(v___f_1257_, 2, v_e_1211_);
lean_closure_set(v___f_1257_, 3, v_inst_1213_);
lean_closure_set(v___f_1257_, 4, v_inst_1214_);
lean_closure_set(v___f_1257_, 5, v_inst_1215_);
lean_closure_set(v___f_1257_, 6, v_inst_1216_);
lean_closure_set(v___f_1257_, 7, v_inst_1217_);
lean_closure_set(v___f_1257_, 8, v_toVar_1218_);
lean_closure_set(v___f_1257_, 9, v_asVar_1219_);
lean_closure_set(v___f_1257_, 10, v_arg_1232_);
lean_closure_set(v___f_1257_, 11, v_toBind_1220_);
lean_closure_set(v___f_1257_, 12, v___f_1256_);
v___x_1258_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1213_, v_inst_1214_, v_inst_1215_, v_inst_1216_, v_inst_1217_);
v___x_1259_ = lean_apply_4(v_toBind_1220_, lean_box(0), lean_box(0), v___x_1258_, v___f_1257_);
return v___x_1259_;
}
}
else
{
lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v___x_1248_);
lean_dec(v_toTopVar_1210_);
lean_inc_n(v_toBind_1220_, 2);
lean_inc(v_asVar_1219_);
lean_inc(v_toVar_1218_);
lean_inc_ref_n(v_inst_1217_, 2);
lean_inc_ref_n(v_inst_1216_, 2);
lean_inc_ref_n(v_inst_1215_, 2);
lean_inc_ref_n(v_inst_1214_, 2);
lean_inc_n(v_inst_1213_, 2);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__6), 11, 10);
lean_closure_set(v___f_1260_, 0, v_toPure_1212_);
lean_closure_set(v___f_1260_, 1, v_inst_1213_);
lean_closure_set(v___f_1260_, 2, v_inst_1214_);
lean_closure_set(v___f_1260_, 3, v_inst_1215_);
lean_closure_set(v___f_1260_, 4, v_inst_1216_);
lean_closure_set(v___f_1260_, 5, v_inst_1217_);
lean_closure_set(v___f_1260_, 6, v_toVar_1218_);
lean_closure_set(v___f_1260_, 7, v_asVar_1219_);
lean_closure_set(v___f_1260_, 8, v_arg_1236_);
lean_closure_set(v___f_1260_, 9, v_toBind_1220_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1261_, 0, v_arg_1247_);
lean_closure_set(v___f_1261_, 1, v_asTopVar_1221_);
lean_closure_set(v___f_1261_, 2, v_e_1211_);
lean_closure_set(v___f_1261_, 3, v_inst_1213_);
lean_closure_set(v___f_1261_, 4, v_inst_1214_);
lean_closure_set(v___f_1261_, 5, v_inst_1215_);
lean_closure_set(v___f_1261_, 6, v_inst_1216_);
lean_closure_set(v___f_1261_, 7, v_inst_1217_);
lean_closure_set(v___f_1261_, 8, v_toVar_1218_);
lean_closure_set(v___f_1261_, 9, v_asVar_1219_);
lean_closure_set(v___f_1261_, 10, v_arg_1232_);
lean_closure_set(v___f_1261_, 11, v_toBind_1220_);
lean_closure_set(v___f_1261_, 12, v___f_1260_);
v___x_1262_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1213_, v_inst_1214_, v_inst_1215_, v_inst_1216_, v_inst_1217_);
v___x_1263_ = lean_apply_4(v_toBind_1220_, lean_box(0), lean_box(0), v___x_1262_, v___f_1261_);
return v___x_1263_;
}
}
else
{
lean_object* v___x_1264_; 
lean_dec_ref(v___x_1248_);
lean_dec(v_toTopVar_1210_);
v___x_1264_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1236_);
lean_dec_ref(v_arg_1236_);
if (lean_obj_tag(v___x_1264_) == 1)
{
lean_object* v_val_1265_; lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_val_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__17), 3, 2);
lean_closure_set(v___f_1266_, 0, v_val_1265_);
lean_closure_set(v___f_1266_, 1, v_toPure_1212_);
lean_inc(v_toBind_1220_);
lean_inc_ref(v_inst_1217_);
lean_inc_ref(v_inst_1216_);
lean_inc_ref(v_inst_1215_);
lean_inc_ref(v_inst_1214_);
lean_inc(v_inst_1213_);
v___f_1267_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1267_, 0, v_arg_1247_);
lean_closure_set(v___f_1267_, 1, v_asTopVar_1221_);
lean_closure_set(v___f_1267_, 2, v_e_1211_);
lean_closure_set(v___f_1267_, 3, v_inst_1213_);
lean_closure_set(v___f_1267_, 4, v_inst_1214_);
lean_closure_set(v___f_1267_, 5, v_inst_1215_);
lean_closure_set(v___f_1267_, 6, v_inst_1216_);
lean_closure_set(v___f_1267_, 7, v_inst_1217_);
lean_closure_set(v___f_1267_, 8, v_toVar_1218_);
lean_closure_set(v___f_1267_, 9, v_asVar_1219_);
lean_closure_set(v___f_1267_, 10, v_arg_1232_);
lean_closure_set(v___f_1267_, 11, v_toBind_1220_);
lean_closure_set(v___f_1267_, 12, v___f_1266_);
v___x_1268_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1213_, v_inst_1214_, v_inst_1215_, v_inst_1216_, v_inst_1217_);
v___x_1269_ = lean_apply_4(v_toBind_1220_, lean_box(0), lean_box(0), v___x_1268_, v___f_1267_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v___x_1264_);
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1232_);
lean_dec(v_asTopVar_1221_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec_ref(v_e_1211_);
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_apply_2(v_toPure_1212_, lean_box(0), v___x_1270_);
return v___x_1271_;
}
}
}
}
}
}
else
{
lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1229_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1214_);
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_1272_, 0, v_arg_1232_);
lean_closure_set(v___f_1272_, 1, v_asTopVar_1221_);
lean_closure_set(v___f_1272_, 2, v_e_1211_);
lean_closure_set(v___f_1272_, 3, v_arg_1236_);
lean_closure_set(v___f_1272_, 4, v_toPure_1212_);
lean_closure_set(v___f_1272_, 5, v_toTopVar_1210_);
v___x_1273_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1213_, v_inst_1215_, v_inst_1216_, v_inst_1217_);
v___x_1274_ = lean_apply_4(v_toBind_1220_, lean_box(0), lean_box(0), v___x_1273_, v___f_1272_);
return v___x_1274_;
}
}
else
{
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1223_);
lean_dec(v_toBind_1220_);
lean_dec(v_asVar_1219_);
lean_dec(v_toVar_1218_);
lean_dec_ref(v_inst_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_inst_1213_);
lean_dec(v_toTopVar_1210_);
if (lean_obj_tag(v_arg_1232_) == 9)
{
lean_object* v_a_1275_; 
v_a_1275_ = lean_ctor_get(v_arg_1232_, 0);
lean_inc_ref(v_a_1275_);
lean_dec_ref_known(v_arg_1232_, 1);
if (lean_obj_tag(v_a_1275_) == 0)
{
lean_object* v_val_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_asTopVar_1221_);
lean_dec_ref(v_e_1211_);
v_val_1276_ = lean_ctor_get(v_a_1275_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1275_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1278_ = v_a_1275_;
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_val_1276_);
lean_dec(v_a_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = lean_nat_to_int(v_val_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
v___x_1284_ = lean_apply_2(v_toPure_1212_, lean_box(0), v___x_1283_);
return v___x_1284_;
}
}
}
else
{
lean_object* v___x_1287_; 
lean_dec_ref(v_a_1275_);
lean_dec(v_toPure_1212_);
v___x_1287_ = lean_apply_1(v_asTopVar_1221_, v_e_1211_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v_arg_1232_);
lean_dec(v_toPure_1212_);
v___x_1288_ = lean_apply_1(v_asTopVar_1221_, v_e_1211_);
return v___x_1288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5___boxed(lean_object* v_toTopVar_1289_, lean_object* v_e_1290_, lean_object* v_toPure_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_toVar_1297_, lean_object* v_asVar_1298_, lean_object* v_toBind_1299_, lean_object* v_asTopVar_1300_, lean_object* v_____x_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5(v_toTopVar_1289_, v_e_1290_, v_toPure_1291_, v_inst_1292_, v_inst_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_, v_toVar_1297_, v_asVar_1298_, v_toBind_1299_, v_asTopVar_1300_, v_____x_1301_);
lean_dec_ref(v_____x_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_e_1310_){
_start:
{
lean_object* v_toApplicative_1311_; lean_object* v_toBind_1312_; lean_object* v_toPure_1313_; lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v_asVar_1316_; lean_object* v_toVar_1317_; lean_object* v_toTopVar_1318_; lean_object* v_asTopVar_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_toApplicative_1311_ = lean_ctor_get(v_inst_1306_, 0);
v_toBind_1312_ = lean_ctor_get(v_inst_1306_, 1);
lean_inc_n(v_toBind_1312_, 6);
v_toPure_1313_ = lean_ctor_get(v_toApplicative_1311_, 1);
lean_inc_n(v_toPure_1313_, 3);
v___f_1314_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1314_, 0, v_toPure_1313_);
v___f_1315_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1315_, 0, v_toPure_1313_);
lean_inc(v_inst_1303_);
lean_inc_ref(v___f_1315_);
lean_inc(v_inst_1309_);
v_asVar_1316_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v_asVar_1316_, 0, v_inst_1309_);
lean_closure_set(v_asVar_1316_, 1, v_toBind_1312_);
lean_closure_set(v_asVar_1316_, 2, v___f_1315_);
lean_closure_set(v_asVar_1316_, 3, v_inst_1303_);
v_toVar_1317_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifyRing_x3f___redArg___lam__6), 4, 3);
lean_closure_set(v_toVar_1317_, 0, v_inst_1309_);
lean_closure_set(v_toVar_1317_, 1, v_toBind_1312_);
lean_closure_set(v_toVar_1317_, 2, v___f_1315_);
lean_inc_ref(v_toVar_1317_);
v_toTopVar_1318_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v_toTopVar_1318_, 0, v_toVar_1317_);
lean_closure_set(v_toTopVar_1318_, 1, v_toBind_1312_);
lean_closure_set(v_toTopVar_1318_, 2, v___f_1314_);
lean_inc_ref(v_toTopVar_1318_);
v_asTopVar_1319_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v_asTopVar_1319_, 0, v_toTopVar_1318_);
lean_closure_set(v_asTopVar_1319_, 1, v_inst_1303_);
lean_closure_set(v_asTopVar_1319_, 2, v_toBind_1312_);
lean_inc(v_inst_1304_);
lean_inc_ref(v_e_1310_);
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_1320_, 0, v_toTopVar_1318_);
lean_closure_set(v___f_1320_, 1, v_e_1310_);
lean_closure_set(v___f_1320_, 2, v_toPure_1313_);
lean_closure_set(v___f_1320_, 3, v_inst_1304_);
lean_closure_set(v___f_1320_, 4, v_inst_1305_);
lean_closure_set(v___f_1320_, 5, v_inst_1306_);
lean_closure_set(v___f_1320_, 6, v_inst_1307_);
lean_closure_set(v___f_1320_, 7, v_inst_1308_);
lean_closure_set(v___f_1320_, 8, v_toVar_1317_);
lean_closure_set(v___f_1320_, 9, v_asVar_1316_);
lean_closure_set(v___f_1320_, 10, v_toBind_1312_);
lean_closure_set(v___f_1320_, 11, v_asTopVar_1319_);
v___x_1321_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_1321_, 0, v_e_1310_);
v___x_1322_ = lean_apply_2(v_inst_1304_, lean_box(0), v___x_1321_);
v___x_1323_ = lean_apply_4(v_toBind_1312_, lean_box(0), lean_box(0), v___x_1322_, v___f_1320_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_reifySemiring_x3f(lean_object* v_m_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_e_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Meta_Sym_Arith_reifySemiring_x3f___redArg(v_inst_1325_, v_inst_1326_, v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_inst_1331_, v_e_1332_);
return v___x_1333_;
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
