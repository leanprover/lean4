// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Reify
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.Linear.Var
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
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSubInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSubInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isNegInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isNegInst___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`grind linarith` term with unexpected instance"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "natCast_nonneg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(182, 238, 184, 21, 62, 177, 92, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object* v_struct_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v_addFn_3_; lean_object* v___x_4_; size_t v___x_5_; size_t v___x_6_; uint8_t v___x_7_; 
v_addFn_3_ = lean_ctor_get(v_struct_1_, 22);
v___x_4_ = l_Lean_Expr_appArg_x21(v_addFn_3_);
v___x_5_ = lean_ptr_addr(v___x_4_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_ptr_addr(v_inst_2_);
v___x_7_ = lean_usize_dec_eq(v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object* v_struct_8_, lean_object* v_inst_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_struct_8_, v_inst_9_);
lean_dec_ref(v_inst_9_);
lean_dec_ref(v_struct_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object* v_struct_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_zero_14_; lean_object* v___x_15_; size_t v___x_16_; size_t v___x_17_; uint8_t v___x_18_; 
v_zero_14_ = lean_ctor_get(v_struct_12_, 17);
v___x_15_ = l_Lean_Expr_appArg_x21(v_zero_14_);
v___x_16_ = lean_ptr_addr(v___x_15_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_ptr_addr(v_inst_13_);
v___x_18_ = lean_usize_dec_eq(v___x_16_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object* v_struct_19_, lean_object* v_inst_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_struct_19_, v_inst_20_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_struct_19_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(lean_object* v_struct_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v_zsmulFn_25_; lean_object* v___x_26_; size_t v___x_27_; size_t v___x_28_; uint8_t v___x_29_; 
v_zsmulFn_25_ = lean_ctor_get(v_struct_23_, 23);
v___x_26_ = l_Lean_Expr_appArg_x21(v_zsmulFn_25_);
v___x_27_ = lean_ptr_addr(v___x_26_);
lean_dec_ref(v___x_26_);
v___x_28_ = lean_ptr_addr(v_inst_24_);
v___x_29_ = lean_usize_dec_eq(v___x_27_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst___boxed(lean_object* v_struct_30_, lean_object* v_inst_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_struct_30_, v_inst_31_);
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_struct_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(lean_object* v_struct_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v_nsmulFn_36_; lean_object* v___x_37_; size_t v___x_38_; size_t v___x_39_; uint8_t v___x_40_; 
v_nsmulFn_36_ = lean_ctor_get(v_struct_34_, 24);
v___x_37_ = l_Lean_Expr_appArg_x21(v_nsmulFn_36_);
v___x_38_ = lean_ptr_addr(v___x_37_);
lean_dec_ref(v___x_37_);
v___x_39_ = lean_ptr_addr(v_inst_35_);
v___x_40_ = lean_usize_dec_eq(v___x_38_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst___boxed(lean_object* v_struct_41_, lean_object* v_inst_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_struct_41_, v_inst_42_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_struct_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(lean_object* v_struct_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v_homomulFn_x3f_47_; 
v_homomulFn_x3f_47_ = lean_ctor_get(v_struct_45_, 27);
if (lean_obj_tag(v_homomulFn_x3f_47_) == 1)
{
lean_object* v_val_48_; size_t v___x_49_; size_t v___x_50_; uint8_t v___x_51_; 
v_val_48_ = lean_ctor_get(v_homomulFn_x3f_47_, 0);
v___x_49_ = lean_ptr_addr(v_val_48_);
v___x_50_ = lean_ptr_addr(v_inst_46_);
v___x_51_ = lean_usize_dec_eq(v___x_49_, v___x_50_);
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst___boxed(lean_object* v_struct_53_, lean_object* v_inst_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_struct_53_, v_inst_54_);
lean_dec_ref(v_inst_54_);
lean_dec_ref(v_struct_53_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(lean_object* v_struct_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v_zsmulFn_x3f_59_; 
v_zsmulFn_x3f_59_ = lean_ctor_get(v_struct_57_, 25);
if (lean_obj_tag(v_zsmulFn_x3f_59_) == 1)
{
lean_object* v_val_60_; lean_object* v___x_61_; size_t v___x_62_; size_t v___x_63_; uint8_t v___x_64_; 
v_val_60_ = lean_ctor_get(v_zsmulFn_x3f_59_, 0);
v___x_61_ = l_Lean_Expr_appArg_x21(v_val_60_);
v___x_62_ = lean_ptr_addr(v___x_61_);
lean_dec_ref(v___x_61_);
v___x_63_ = lean_ptr_addr(v_inst_58_);
v___x_64_ = lean_usize_dec_eq(v___x_62_, v___x_63_);
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst___boxed(lean_object* v_struct_66_, lean_object* v_inst_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(v_struct_66_, v_inst_67_);
lean_dec_ref(v_inst_67_);
lean_dec_ref(v_struct_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(lean_object* v_struct_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v_nsmulFn_x3f_72_; 
v_nsmulFn_x3f_72_ = lean_ctor_get(v_struct_70_, 26);
if (lean_obj_tag(v_nsmulFn_x3f_72_) == 1)
{
lean_object* v_val_73_; lean_object* v___x_74_; size_t v___x_75_; size_t v___x_76_; uint8_t v___x_77_; 
v_val_73_ = lean_ctor_get(v_nsmulFn_x3f_72_, 0);
v___x_74_ = l_Lean_Expr_appArg_x21(v_val_73_);
v___x_75_ = lean_ptr_addr(v___x_74_);
lean_dec_ref(v___x_74_);
v___x_76_ = lean_ptr_addr(v_inst_71_);
v___x_77_ = lean_usize_dec_eq(v___x_75_, v___x_76_);
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst___boxed(lean_object* v_struct_79_, lean_object* v_inst_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(v_struct_79_, v_inst_80_);
lean_dec_ref(v_inst_80_);
lean_dec_ref(v_struct_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSubInst(lean_object* v_struct_83_, lean_object* v_inst_84_){
_start:
{
lean_object* v_subFn_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; uint8_t v___x_89_; 
v_subFn_85_ = lean_ctor_get(v_struct_83_, 28);
v___x_86_ = l_Lean_Expr_appArg_x21(v_subFn_85_);
v___x_87_ = lean_ptr_addr(v___x_86_);
lean_dec_ref(v___x_86_);
v___x_88_ = lean_ptr_addr(v_inst_84_);
v___x_89_ = lean_usize_dec_eq(v___x_87_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSubInst___boxed(lean_object* v_struct_90_, lean_object* v_inst_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_struct_90_, v_inst_91_);
lean_dec_ref(v_inst_91_);
lean_dec_ref(v_struct_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isNegInst(lean_object* v_struct_94_, lean_object* v_inst_95_){
_start:
{
lean_object* v_negFn_96_; lean_object* v___x_97_; size_t v___x_98_; size_t v___x_99_; uint8_t v___x_100_; 
v_negFn_96_ = lean_ctor_get(v_struct_94_, 29);
v___x_97_ = l_Lean_Expr_appArg_x21(v_negFn_96_);
v___x_98_ = lean_ptr_addr(v___x_97_);
lean_dec_ref(v___x_97_);
v___x_99_ = lean_ptr_addr(v_inst_95_);
v___x_100_ = lean_usize_dec_eq(v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isNegInst___boxed(lean_object* v_struct_101_, lean_object* v_inst_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_struct_101_, v_inst_102_);
lean_dec_ref(v_inst_102_);
lean_dec_ref(v_struct_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0));
v___x_107_ = l_Lean_stringToMessageData(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(lean_object* v_e_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_109_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_130_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_130_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_130_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_130_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
uint8_t v_verbose_121_; 
v_verbose_121_ = lean_ctor_get_uint8(v_a_117_, 0);
lean_dec(v_a_117_);
if (v_verbose_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_124_; 
lean_dec_ref(v_e_108_);
v___x_122_ = lean_box(0);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_122_);
v___x_124_ = v___x_119_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
lean_del_object(v___x_119_);
v___x_126_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1);
v___x_127_ = l_Lean_indentExpr(v_e_108_);
v___x_128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = l_Lean_Meta_Sym_reportIssue(v___x_128_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
return v___x_129_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v_e_108_);
v_a_131_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_116_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_116_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___boxed(lean_object* v_e_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(lean_object* v_e_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_148_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___boxed(lean_object* v_e_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(v_e_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec(v_a_162_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(lean_object* v_msg_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_Lean_instInhabitedExpr;
v___x_176_ = lean_panic_fn_borrowed(v___x_175_, v_msg_174_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9));
v___x_194_ = lean_unsigned_to_nat(14u);
v___x_195_ = lean_unsigned_to_nat(22u);
v___x_196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8));
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7));
v___x_198_ = l_mkPanicMessageWithDecl(v___x_197_, v___x_196_, v___x_195_, v___x_194_, v___x_193_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_type_214_; lean_object* v_u_215_; lean_object* v_leInst_x3f_216_; lean_object* v_ltInst_x3f_217_; lean_object* v_lawfulOrderLTInst_x3f_218_; lean_object* v_isPreorderInst_x3f_219_; lean_object* v_ringInst_x3f_220_; lean_object* v_orderedRingInst_x3f_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_288_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
v_type_214_ = lean_ctor_get(v_a_213_, 2);
lean_inc_ref(v_type_214_);
v_u_215_ = lean_ctor_get(v_a_213_, 3);
lean_inc(v_u_215_);
v_leInst_x3f_216_ = lean_ctor_get(v_a_213_, 5);
lean_inc(v_leInst_x3f_216_);
v_ltInst_x3f_217_ = lean_ctor_get(v_a_213_, 6);
lean_inc(v_ltInst_x3f_217_);
v_lawfulOrderLTInst_x3f_218_ = lean_ctor_get(v_a_213_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_218_);
v_isPreorderInst_x3f_219_ = lean_ctor_get(v_a_213_, 8);
lean_inc(v_isPreorderInst_x3f_219_);
v_ringInst_x3f_220_ = lean_ctor_get(v_a_213_, 12);
lean_inc(v_ringInst_x3f_220_);
v_orderedRingInst_x3f_221_ = lean_ctor_get(v_a_213_, 14);
lean_inc(v_orderedRingInst_x3f_221_);
lean_dec(v_a_213_);
v___x_222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4));
v___x_223_ = lean_box(0);
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v_u_215_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = l_Lean_mkConst(v___x_222_, v___x_224_);
if (lean_obj_tag(v_ringInst_x3f_220_) == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_293_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_292_);
v___y_288_ = v___x_293_;
goto v___jp_287_;
}
else
{
lean_object* v_val_294_; 
v_val_294_ = lean_ctor_get(v_ringInst_x3f_220_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v_ringInst_x3f_220_, 1);
v___y_288_ = v_val_294_;
goto v___jp_287_;
}
v___jp_226_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_inc_ref(v_a_199_);
v___x_233_ = l_Lean_mkApp8(v___x_225_, v_type_214_, v___y_231_, v___y_228_, v___y_229_, v___y_227_, v___y_230_, v___y_232_, v_a_199_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc_ref(v___x_233_);
v___x_234_ = lean_infer_type(v___x_233_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_236_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v___x_236_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_199_, v_a_201_);
lean_dec_ref(v_a_199_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6));
v___x_239_ = lean_box(1);
v___x_240_ = l_Lean_Meta_Grind_addNewRawFact(v___x_233_, v_a_235_, v_a_237_, v___x_238_, v___x_239_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_240_;
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_a_235_);
lean_dec_ref(v___x_233_);
v_a_241_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_236_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_236_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v___x_233_);
lean_dec_ref(v_a_199_);
v_a_249_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_234_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_234_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
v___jp_257_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_221_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_264_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_263_);
v___y_227_ = v___y_258_;
v___y_228_ = v___y_259_;
v___y_229_ = v___y_260_;
v___y_230_ = v___y_262_;
v___y_231_ = v___y_261_;
v___y_232_ = v___x_264_;
goto v___jp_226_;
}
else
{
lean_object* v_val_265_; 
v_val_265_ = lean_ctor_get(v_orderedRingInst_x3f_221_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v_orderedRingInst_x3f_221_, 1);
v___y_227_ = v___y_258_;
v___y_228_ = v___y_259_;
v___y_229_ = v___y_260_;
v___y_230_ = v___y_262_;
v___y_231_ = v___y_261_;
v___y_232_ = v_val_265_;
goto v___jp_226_;
}
}
v___jp_266_:
{
if (lean_obj_tag(v_isPreorderInst_x3f_219_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_272_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_271_);
v___y_258_ = v___y_270_;
v___y_259_ = v___y_267_;
v___y_260_ = v___y_268_;
v___y_261_ = v___y_269_;
v___y_262_ = v___x_272_;
goto v___jp_257_;
}
else
{
lean_object* v_val_273_; 
v_val_273_ = lean_ctor_get(v_isPreorderInst_x3f_219_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v_isPreorderInst_x3f_219_, 1);
v___y_258_ = v___y_270_;
v___y_259_ = v___y_267_;
v___y_260_ = v___y_268_;
v___y_261_ = v___y_269_;
v___y_262_ = v_val_273_;
goto v___jp_257_;
}
}
v___jp_274_:
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_218_) == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_279_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_278_);
v___y_267_ = v___y_275_;
v___y_268_ = v___y_277_;
v___y_269_ = v___y_276_;
v___y_270_ = v___x_279_;
goto v___jp_266_;
}
else
{
lean_object* v_val_280_; 
v_val_280_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_218_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_218_, 1);
v___y_267_ = v___y_275_;
v___y_268_ = v___y_277_;
v___y_269_ = v___y_276_;
v___y_270_ = v_val_280_;
goto v___jp_266_;
}
}
v___jp_281_:
{
if (lean_obj_tag(v_ltInst_x3f_217_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_285_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_284_);
v___y_275_ = v___y_283_;
v___y_276_ = v___y_282_;
v___y_277_ = v___x_285_;
goto v___jp_274_;
}
else
{
lean_object* v_val_286_; 
v_val_286_ = lean_ctor_get(v_ltInst_x3f_217_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v_ltInst_x3f_217_, 1);
v___y_275_ = v___y_283_;
v___y_276_ = v___y_282_;
v___y_277_ = v_val_286_;
goto v___jp_274_;
}
}
v___jp_287_:
{
if (lean_obj_tag(v_leInst_x3f_216_) == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_290_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_289_);
v___y_282_ = v___y_288_;
v___y_283_ = v___x_290_;
goto v___jp_281_;
}
else
{
lean_object* v_val_291_; 
v_val_291_ = lean_ctor_get(v_leInst_x3f_216_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v_leInst_x3f_216_, 1);
v___y_282_ = v___y_288_;
v___y_283_ = v_val_291_;
goto v___jp_281_;
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v_a_199_);
v_a_295_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_212_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_212_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___boxed(lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(lean_object* v_generation_317_, lean_object* v_e_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_318_, v_a_320_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; uint8_t v___x_333_; uint8_t v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = 1;
v___x_334_ = lean_unbox(v_a_332_);
lean_dec(v_a_332_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_box(0);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc(v_a_323_);
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_e_318_);
v___x_336_ = lean_grind_internalize(v_e_318_, v_generation_317_, v___x_335_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_337_; 
lean_dec_ref_known(v___x_336_, 1);
v___x_337_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_318_, v___x_333_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_346_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_346_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v_a_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_337_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_337_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_e_318_);
v_a_355_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_336_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_336_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v___x_363_; 
lean_dec(v_generation_317_);
v___x_363_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_318_, v___x_333_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_372_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_372_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v_a_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v_a_373_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_363_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_363_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v_e_318_);
lean_dec(v_generation_317_);
v_a_381_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_331_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_331_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___boxed(lean_object* v_generation_389_, lean_object* v_e_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_389_, v_e_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec(v_a_392_);
lean_dec(v_a_391_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(lean_object* v_generation_404_, lean_object* v_e_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; 
lean_inc_ref(v_e_405_);
v___x_418_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_405_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_419_; 
lean_dec_ref_known(v___x_418_, 1);
v___x_419_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_404_, v_e_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
return v___x_419_;
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec_ref(v_e_405_);
lean_dec(v_generation_404_);
v_a_420_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_418_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar___boxed(lean_object* v_generation_428_, lean_object* v_e_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_428_, v_e_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec(v_a_431_);
lean_dec(v_a_430_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(uint8_t v_skipVar_443_, lean_object* v_generation_444_, lean_object* v_e_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
if (v_skipVar_443_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_444_, v_e_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_467_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_a_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
v_a_468_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_458_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_458_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec_ref(v_e_445_);
lean_dec(v_generation_444_);
v___x_476_ = lean_box(0);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar___boxed(lean_object* v_skipVar_478_, lean_object* v_generation_479_, lean_object* v_e_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
uint8_t v_skipVar_boxed_493_; lean_object* v_res_494_; 
v_skipVar_boxed_493_ = lean_unbox(v_skipVar_478_);
v_res_494_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_boxed_493_, v_generation_479_, v_e_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec(v_a_482_);
lean_dec(v_a_481_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(uint8_t v_skipVar_495_, lean_object* v_generation_496_, lean_object* v_e_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; 
lean_inc_ref(v_e_497_);
v___x_510_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_497_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_536_; 
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v___x_510_, 0);
lean_dec(v_unused_537_);
v___x_512_ = v___x_510_;
v_isShared_513_ = v_isSharedCheck_536_;
goto v_resetjp_511_;
}
else
{
lean_dec(v___x_510_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_536_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
if (v_skipVar_495_ == 0)
{
lean_object* v___x_514_; 
lean_del_object(v___x_512_);
v___x_514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_496_, v_e_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_514_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_514_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
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
else
{
lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec_ref(v_e_497_);
lean_dec(v_generation_496_);
v___x_532_ = lean_box(0);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_532_);
v___x_534_ = v___x_512_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_e_497_);
lean_dec(v_generation_496_);
v_a_538_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_510_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_510_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar___boxed(lean_object* v_skipVar_546_, lean_object* v_generation_547_, lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
uint8_t v_skipVar_boxed_561_; lean_object* v_res_562_; 
v_skipVar_boxed_561_ = lean_unbox(v_skipVar_546_);
v_res_562_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_boxed_561_, v_generation_547_, v_e_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec(v_a_550_);
lean_dec(v_a_549_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(lean_object* v_e_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v_ofNatZero_578_; lean_object* v___x_579_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v_ofNatZero_578_ = lean_ctor_get(v_a_577_, 18);
lean_inc_ref(v_ofNatZero_578_);
lean_dec(v_a_577_);
v___x_579_ = l_Lean_Meta_isDefEqD(v_e_563_, v_ofNatZero_578_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_579_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_e_563_);
v_a_580_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_576_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_576_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero___boxed(lean_object* v_e_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec(v_a_590_);
lean_dec(v_a_589_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(lean_object* v_generation_637_, lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_651_; 
lean_inc_ref(v_e_638_);
v___x_651_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_638_, v_a_647_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = l_Lean_Expr_cleanupAnnotations(v_a_652_);
v___x_654_ = l_Lean_Expr_isApp(v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v___x_653_);
v___x_655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_655_;
}
else
{
lean_object* v_arg_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_arg_656_ = lean_ctor_get(v___x_653_, 1);
lean_inc_ref(v_arg_656_);
v___x_657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_653_);
v___x_658_ = l_Lean_Expr_isApp(v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec_ref(v___x_657_);
lean_dec_ref(v_arg_656_);
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_659_;
}
else
{
lean_object* v_arg_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_arg_660_ = lean_ctor_get(v___x_657_, 1);
lean_inc_ref(v_arg_660_);
v___x_661_ = l_Lean_Expr_appFnCleanup___redArg(v___x_657_);
v___x_662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2));
v___x_663_ = l_Lean_Expr_isConstOf(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
v___x_664_ = l_Lean_Expr_isApp(v___x_661_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v___x_661_);
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_665_;
}
else
{
lean_object* v_arg_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_arg_666_ = lean_ctor_get(v___x_661_, 1);
lean_inc_ref(v_arg_666_);
v___x_667_ = l_Lean_Expr_appFnCleanup___redArg(v___x_661_);
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5));
v___x_669_ = l_Lean_Expr_isConstOf(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8));
v___x_671_ = l_Lean_Expr_isConstOf(v___x_667_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11));
v___x_673_ = l_Lean_Expr_isConstOf(v___x_667_, v___x_672_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_Expr_isApp(v___x_667_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v___x_667_);
lean_dec_ref(v_arg_666_);
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
v___x_675_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = l_Lean_Expr_appFnCleanup___redArg(v___x_667_);
v___x_677_ = l_Lean_Expr_isApp(v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
lean_dec_ref(v___x_676_);
lean_dec_ref(v_arg_666_);
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
v___x_678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_676_);
v___x_680_ = l_Lean_Expr_isApp(v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
lean_dec_ref(v___x_679_);
lean_dec_ref(v_arg_666_);
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
v___x_681_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_679_);
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14));
v___x_684_ = l_Lean_Expr_isConstOf(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17));
v___x_686_ = l_Lean_Expr_isConstOf(v___x_682_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20));
v___x_688_ = l_Lean_Expr_isConstOf(v___x_682_, v___x_687_);
lean_dec_ref(v___x_682_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec_ref(v_arg_666_);
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
v___x_689_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; uint8_t v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_691_, v_arg_666_);
lean_dec_ref(v_arg_666_);
lean_dec(v_a_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
v___x_693_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; 
lean_dec_ref(v_e_638_);
lean_inc(v_generation_637_);
v___x_694_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_637_, v_arg_660_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_637_, v_arg_656_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_705_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_701_, 0, v_a_695_);
lean_ctor_set(v___x_701_, 1, v_a_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
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
else
{
lean_dec(v_a_695_);
return v___x_696_;
}
}
else
{
lean_dec_ref(v_arg_656_);
lean_dec(v_generation_637_);
return v___x_694_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v_arg_666_);
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_706_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_690_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_690_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_object* v___x_714_; 
lean_dec_ref(v___x_682_);
v___x_714_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; uint8_t v___x_716_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_715_, v_arg_666_);
lean_dec_ref(v_arg_666_);
lean_dec(v_a_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
v___x_717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; 
lean_dec_ref(v_e_638_);
lean_inc(v_generation_637_);
v___x_718_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_637_, v_arg_660_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_637_, v_arg_656_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_729_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_729_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_725_, 0, v_a_719_);
lean_ctor_set(v___x_725_, 1, v_a_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_dec(v_a_719_);
return v___x_720_;
}
}
else
{
lean_dec_ref(v_arg_656_);
lean_dec(v_generation_637_);
return v___x_718_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_arg_666_);
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_730_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_714_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_714_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
else
{
lean_object* v___x_738_; 
lean_dec_ref(v___x_682_);
lean_inc(v_generation_637_);
v___x_738_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_637_, v_arg_666_, v_arg_660_, v_arg_656_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec_ref(v_arg_666_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_748_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_748_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
if (lean_obj_tag(v_a_739_) == 1)
{
lean_object* v_val_743_; lean_object* v___x_745_; 
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_val_743_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v_a_739_, 1);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v_val_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_val_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
else
{
lean_object* v___x_747_; 
lean_del_object(v___x_741_);
lean_dec(v_a_739_);
v___x_747_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_747_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_749_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_738_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_738_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
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
lean_object* v___x_757_; 
lean_dec_ref(v___x_667_);
lean_dec_ref(v_arg_666_);
v___x_757_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; uint8_t v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_a_758_, v_arg_660_);
lean_dec_ref(v_arg_660_);
lean_dec(v_a_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec_ref(v_arg_656_);
v___x_760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; 
lean_dec_ref(v_e_638_);
v___x_761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_637_, v_arg_656_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_770_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_762_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
return v___x_761_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_771_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_757_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_757_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
else
{
lean_object* v___x_779_; 
lean_dec_ref(v___x_667_);
lean_dec_ref(v_arg_666_);
lean_dec_ref(v_arg_660_);
lean_dec_ref(v_arg_656_);
lean_inc_ref(v_e_638_);
v___x_779_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_790_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_790_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
uint8_t v___x_784_; 
v___x_784_ = lean_unbox(v_a_780_);
lean_dec(v_a_780_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_del_object(v___x_782_);
v___x_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v___x_786_ = lean_box(0);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_786_);
v___x_788_ = v___x_782_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_791_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_779_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_779_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
else
{
lean_object* v___x_799_; 
lean_dec_ref(v___x_667_);
lean_dec_ref(v_arg_666_);
lean_dec_ref(v_arg_660_);
v___x_799_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; uint8_t v___y_802_; lean_object* v_orderedRingInst_x3f_814_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v_orderedRingInst_x3f_814_ = lean_ctor_get(v_a_800_, 14);
lean_inc(v_orderedRingInst_x3f_814_);
lean_dec(v_a_800_);
if (lean_obj_tag(v_orderedRingInst_x3f_814_) == 0)
{
v___y_802_ = v___x_663_;
goto v___jp_801_;
}
else
{
lean_dec_ref_known(v_orderedRingInst_x3f_814_, 1);
v___y_802_ = v___x_669_;
goto v___jp_801_;
}
v___jp_801_:
{
if (v___y_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v_arg_656_);
v___x_803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_656_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v___x_805_; 
lean_dec_ref_known(v___x_804_, 1);
v___x_805_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_805_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_806_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_804_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_815_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_799_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_799_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
else
{
lean_object* v___x_823_; 
lean_dec_ref(v___x_661_);
lean_dec_ref(v_arg_660_);
v___x_823_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_834_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_834_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint8_t v___x_828_; 
v___x_828_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_824_, v_arg_656_);
lean_dec_ref(v_arg_656_);
lean_dec(v_a_824_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_del_object(v___x_826_);
v___x_829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_832_; 
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v___x_830_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_830_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_835_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_823_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_823_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v_e_638_);
lean_dec(v_generation_637_);
v_a_843_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_651_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_651_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(lean_object* v_generation_851_, lean_object* v_i_852_, lean_object* v_a_853_, lean_object* v_b_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; uint8_t v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_868_, v_i_852_);
lean_dec(v_a_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_924_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_924_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_924_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_924_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_a_871_, v_i_852_);
lean_dec(v_a_871_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec_ref(v_b_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_generation_851_);
v___x_876_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_object* v___x_880_; 
lean_del_object(v___x_873_);
v___x_880_ = l_Lean_Meta_getNatValue_x3f(v_a_853_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec_ref(v_a_853_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_915_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_915_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_915_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_915_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
if (lean_obj_tag(v_a_881_) == 1)
{
lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_883_);
v_val_885_ = lean_ctor_get(v_a_881_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_910_ == 0)
{
v___x_887_ = v_a_881_;
v_isShared_888_ = v_isSharedCheck_910_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v_a_881_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_910_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_851_, v_b_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_901_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_901_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v_val_885_);
lean_ctor_set(v___x_894_, 1, v_a_890_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_894_);
v___x_896_ = v___x_887_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_900_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_898_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_896_);
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_del_object(v___x_887_);
lean_dec(v_val_885_);
v_a_902_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_889_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_889_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec(v_a_881_);
lean_dec_ref(v_b_854_);
lean_dec(v_generation_851_);
v___x_911_ = lean_box(0);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_911_);
v___x_913_ = v___x_883_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_b_854_);
lean_dec(v_generation_851_);
v_a_916_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_880_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_880_);
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
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_b_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_generation_851_);
v_a_925_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_870_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_870_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Meta_getIntValue_x3f(v_a_853_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_968_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_968_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_968_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_968_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
if (lean_obj_tag(v_a_934_) == 1)
{
lean_object* v_val_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_963_; 
lean_del_object(v___x_936_);
v_val_938_ = lean_ctor_get(v_a_934_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_934_);
if (v_isSharedCheck_963_ == 0)
{
v___x_940_ = v_a_934_;
v_isShared_941_ = v_isSharedCheck_963_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_val_938_);
lean_dec(v_a_934_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_963_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; 
v___x_942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_851_, v_b_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_954_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_954_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_947_, 0, v_val_938_);
lean_ctor_set(v___x_947_, 1, v_a_943_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_947_);
v___x_949_ = v___x_940_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_949_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_940_);
lean_dec(v_val_938_);
v_a_955_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_942_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_942_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v_a_934_);
lean_dec_ref(v_b_854_);
lean_dec(v_generation_851_);
v___x_964_ = lean_box(0);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_964_);
v___x_966_ = v___x_936_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_b_854_);
lean_dec(v_generation_851_);
v_a_969_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_933_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_933_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref(v_b_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_generation_851_);
v_a_977_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_867_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_867_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul___boxed(lean_object* v_generation_985_, lean_object* v_i_986_, lean_object* v_a_987_, lean_object* v_b_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_985_, v_i_986_, v_a_987_, v_b_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_i_986_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___boxed(lean_object* v_generation_1002_, lean_object* v_e_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1002_, v_e_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec(v_a_1004_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object* v_e_1019_, uint8_t v_skipVar_1020_, lean_object* v_generation_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
lean_inc_ref(v_e_1019_);
v___x_1034_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1019_, v_a_1030_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = l_Lean_Expr_cleanupAnnotations(v_a_1035_);
v___x_1037_ = l_Lean_Expr_isApp(v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v___x_1036_);
v___x_1038_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1038_;
}
else
{
lean_object* v_arg_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_arg_1039_ = lean_ctor_get(v___x_1036_, 1);
lean_inc_ref(v_arg_1039_);
v___x_1040_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1036_);
v___x_1041_ = l_Lean_Expr_isApp(v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec_ref(v___x_1040_);
lean_dec_ref(v_arg_1039_);
v___x_1042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1042_;
}
else
{
lean_object* v_arg_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_arg_1043_ = lean_ctor_get(v___x_1040_, 1);
lean_inc_ref(v_arg_1043_);
v___x_1044_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1040_);
v___x_1045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2));
v___x_1046_ = l_Lean_Expr_isConstOf(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
uint8_t v___x_1047_; 
v___x_1047_ = l_Lean_Expr_isApp(v___x_1044_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
v___x_1048_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1048_;
}
else
{
lean_object* v_arg_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_arg_1049_ = lean_ctor_get(v___x_1044_, 1);
lean_inc_ref(v_arg_1049_);
v___x_1050_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1044_);
v___x_1051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5));
v___x_1052_ = l_Lean_Expr_isConstOf(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8));
v___x_1054_ = l_Lean_Expr_isConstOf(v___x_1050_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11));
v___x_1056_ = l_Lean_Expr_isConstOf(v___x_1050_, v___x_1055_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; 
v___x_1057_ = l_Lean_Expr_isApp(v___x_1050_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
v___x_1058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1050_);
v___x_1060_ = l_Lean_Expr_isApp(v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec_ref(v___x_1059_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
v___x_1061_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1059_);
v___x_1063_ = l_Lean_Expr_isApp(v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec_ref(v___x_1062_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1062_);
v___x_1066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14));
v___x_1067_ = l_Lean_Expr_isConstOf(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17));
v___x_1069_ = l_Lean_Expr_isConstOf(v___x_1065_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20));
v___x_1071_ = l_Lean_Expr_isConstOf(v___x_1065_, v___x_1070_);
lean_dec_ref(v___x_1065_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
v___x_1072_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; uint8_t v___x_1075_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1075_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1074_, v_arg_1049_);
lean_dec_ref(v_arg_1049_);
lean_dec(v_a_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
v___x_1076_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; 
lean_dec_ref(v_e_1019_);
lean_inc(v_generation_1021_);
v___x_1077_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1021_, v_arg_1043_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1021_, v_arg_1039_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1089_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_a_1078_);
lean_ctor_set(v___x_1084_, 1, v_a_1080_);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1085_);
v___x_1087_ = v___x_1082_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_1078_);
v_a_1090_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1079_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1079_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_arg_1039_);
lean_dec(v_generation_1021_);
v_a_1098_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1077_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1077_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v_a_1106_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1073_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1073_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
else
{
lean_object* v___x_1114_; 
lean_dec_ref(v___x_1065_);
v___x_1114_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; uint8_t v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_1115_, v_arg_1049_);
lean_dec_ref(v_arg_1049_);
lean_dec(v_a_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
v___x_1117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; 
lean_dec_ref(v_e_1019_);
lean_inc(v_generation_1021_);
v___x_1118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1021_, v_arg_1043_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1021_, v_arg_1039_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1130_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1125_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1119_);
lean_ctor_set(v___x_1125_, 1, v_a_1121_);
v___x_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1126_);
v___x_1128_ = v___x_1123_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_a_1119_);
v_a_1131_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1120_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1120_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v_arg_1039_);
lean_dec(v_generation_1021_);
v_a_1139_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1118_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1118_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v_a_1147_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1114_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1114_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
else
{
lean_object* v___x_1155_; 
lean_dec_ref(v___x_1065_);
lean_inc(v_generation_1021_);
v___x_1155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_1021_, v_arg_1049_, v_arg_1043_, v_arg_1039_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
lean_dec_ref(v_arg_1049_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
if (lean_obj_tag(v_a_1156_) == 1)
{
lean_dec_ref_known(v_a_1156_, 1);
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
return v___x_1155_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1157_;
}
}
else
{
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
return v___x_1155_;
}
}
}
}
}
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_arg_1049_);
v___x_1158_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; uint8_t v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_a_1159_, v_arg_1043_);
lean_dec_ref(v_arg_1043_);
lean_dec(v_a_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref(v_arg_1039_);
v___x_1161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; 
lean_dec_ref(v_e_1019_);
v___x_1162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1021_, v_arg_1039_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1172_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1172_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1172_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1167_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1163_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1168_);
v___x_1170_ = v___x_1165_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1162_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1162_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v_a_1181_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1158_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1158_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
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
}
else
{
lean_object* v___x_1189_; 
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1043_);
lean_dec_ref(v_arg_1039_);
lean_inc_ref(v_e_1019_);
v___x_1189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1200_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1200_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1200_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_unbox(v_a_1190_);
lean_dec(v_a_1190_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_del_object(v___x_1192_);
v___x_1195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v___x_1196_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0));
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1196_);
v___x_1198_ = v___x_1192_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v_a_1201_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1189_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1189_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
else
{
lean_object* v___x_1209_; 
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1043_);
v___x_1209_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; uint8_t v___y_1212_; lean_object* v_orderedRingInst_x3f_1224_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v_orderedRingInst_x3f_1224_ = lean_ctor_get(v_a_1210_, 14);
lean_inc(v_orderedRingInst_x3f_1224_);
lean_dec(v_a_1210_);
if (lean_obj_tag(v_orderedRingInst_x3f_1224_) == 0)
{
v___y_1212_ = v___x_1046_;
goto v___jp_1211_;
}
else
{
lean_dec_ref_known(v_orderedRingInst_x3f_1224_, 1);
v___y_1212_ = v___x_1052_;
goto v___jp_1211_;
}
v___jp_1211_:
{
if (v___y_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v_arg_1039_);
v___x_1213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_1039_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1215_; 
lean_dec_ref_known(v___x_1214_, 1);
v___x_1215_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1215_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v_a_1216_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1214_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v_arg_1039_);
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v_a_1225_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1209_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1209_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
}
else
{
lean_object* v___x_1233_; 
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_arg_1043_);
v___x_1233_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1244_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
uint8_t v___x_1238_; 
v___x_1238_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1234_, v_arg_1039_);
lean_dec_ref(v_arg_1039_);
lean_dec(v_a_1234_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_del_object(v___x_1236_);
v___x_1239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1020_, v_generation_1021_, v_e_1019_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v___x_1240_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0));
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1240_);
v___x_1242_ = v___x_1236_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_arg_1039_);
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v_a_1245_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1233_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1233_);
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
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_generation_1021_);
lean_dec_ref(v_e_1019_);
v_a_1253_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1034_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1034_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f___boxed(lean_object* v_e_1261_, lean_object* v_skipVar_1262_, lean_object* v_generation_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
uint8_t v_skipVar_boxed_1276_; lean_object* v_res_1277_; 
v_skipVar_boxed_1276_ = lean_unbox(v_skipVar_1262_);
v_res_1277_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_e_1261_, v_skipVar_boxed_1276_, v_generation_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec(v_a_1264_);
return v_res_1277_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
}
#ifdef __cplusplus
}
#endif
