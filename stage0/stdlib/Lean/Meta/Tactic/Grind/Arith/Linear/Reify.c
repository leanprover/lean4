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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_addFn_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v_addFn_3_ = lean_ctor_get(v_struct_1_, 22);
v___x_4_ = l_Lean_Expr_appArg_x21(v_addFn_3_);
v___x_5_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_4_, v_inst_2_);
lean_dec_ref(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object* v_struct_6_, lean_object* v_inst_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_struct_6_, v_inst_7_);
lean_dec_ref(v_inst_7_);
lean_dec_ref(v_struct_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object* v_struct_10_, lean_object* v_inst_11_){
_start:
{
lean_object* v_zero_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v_zero_12_ = lean_ctor_get(v_struct_10_, 17);
v___x_13_ = l_Lean_Expr_appArg_x21(v_zero_12_);
v___x_14_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_13_, v_inst_11_);
lean_dec_ref(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object* v_struct_15_, lean_object* v_inst_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_struct_15_, v_inst_16_);
lean_dec_ref(v_inst_16_);
lean_dec_ref(v_struct_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(lean_object* v_struct_19_, lean_object* v_inst_20_){
_start:
{
lean_object* v_zsmulFn_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_zsmulFn_21_ = lean_ctor_get(v_struct_19_, 23);
v___x_22_ = l_Lean_Expr_appArg_x21(v_zsmulFn_21_);
v___x_23_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_22_, v_inst_20_);
lean_dec_ref(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst___boxed(lean_object* v_struct_24_, lean_object* v_inst_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_struct_24_, v_inst_25_);
lean_dec_ref(v_inst_25_);
lean_dec_ref(v_struct_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(lean_object* v_struct_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v_nsmulFn_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_nsmulFn_30_ = lean_ctor_get(v_struct_28_, 24);
v___x_31_ = l_Lean_Expr_appArg_x21(v_nsmulFn_30_);
v___x_32_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_31_, v_inst_29_);
lean_dec_ref(v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst___boxed(lean_object* v_struct_33_, lean_object* v_inst_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_struct_33_, v_inst_34_);
lean_dec_ref(v_inst_34_);
lean_dec_ref(v_struct_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(lean_object* v_struct_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v_homomulFn_x3f_39_; 
v_homomulFn_x3f_39_ = lean_ctor_get(v_struct_37_, 27);
if (lean_obj_tag(v_homomulFn_x3f_39_) == 1)
{
lean_object* v_val_40_; uint8_t v___x_41_; 
v_val_40_ = lean_ctor_get(v_homomulFn_x3f_39_, 0);
v___x_41_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_val_40_, v_inst_38_);
return v___x_41_;
}
else
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst___boxed(lean_object* v_struct_43_, lean_object* v_inst_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_struct_43_, v_inst_44_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_struct_43_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(lean_object* v_struct_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v_zsmulFn_x3f_49_; 
v_zsmulFn_x3f_49_ = lean_ctor_get(v_struct_47_, 25);
if (lean_obj_tag(v_zsmulFn_x3f_49_) == 1)
{
lean_object* v_val_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v_val_50_ = lean_ctor_get(v_zsmulFn_x3f_49_, 0);
v___x_51_ = l_Lean_Expr_appArg_x21(v_val_50_);
v___x_52_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_51_, v_inst_48_);
lean_dec_ref(v___x_51_);
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst___boxed(lean_object* v_struct_54_, lean_object* v_inst_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(v_struct_54_, v_inst_55_);
lean_dec_ref(v_inst_55_);
lean_dec_ref(v_struct_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(lean_object* v_struct_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v_nsmulFn_x3f_60_; 
v_nsmulFn_x3f_60_ = lean_ctor_get(v_struct_58_, 26);
if (lean_obj_tag(v_nsmulFn_x3f_60_) == 1)
{
lean_object* v_val_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v_val_61_ = lean_ctor_get(v_nsmulFn_x3f_60_, 0);
v___x_62_ = l_Lean_Expr_appArg_x21(v_val_61_);
v___x_63_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_62_, v_inst_59_);
lean_dec_ref(v___x_62_);
return v___x_63_;
}
else
{
uint8_t v___x_64_; 
v___x_64_ = 0;
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst___boxed(lean_object* v_struct_65_, lean_object* v_inst_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(v_struct_65_, v_inst_66_);
lean_dec_ref(v_inst_66_);
lean_dec_ref(v_struct_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isSubInst(lean_object* v_struct_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v_subFn_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_subFn_71_ = lean_ctor_get(v_struct_69_, 28);
v___x_72_ = l_Lean_Expr_appArg_x21(v_subFn_71_);
v___x_73_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_72_, v_inst_70_);
lean_dec_ref(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isSubInst___boxed(lean_object* v_struct_74_, lean_object* v_inst_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_struct_74_, v_inst_75_);
lean_dec_ref(v_inst_75_);
lean_dec_ref(v_struct_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_isNegInst(lean_object* v_struct_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v_negFn_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_negFn_80_ = lean_ctor_get(v_struct_78_, 29);
v___x_81_ = l_Lean_Expr_appArg_x21(v_negFn_80_);
v___x_82_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_81_, v_inst_79_);
lean_dec_ref(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isNegInst___boxed(lean_object* v_struct_83_, lean_object* v_inst_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_struct_83_, v_inst_84_);
lean_dec_ref(v_inst_84_);
lean_dec_ref(v_struct_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0));
v___x_89_ = l_Lean_stringToMessageData(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(lean_object* v_e_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_92_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_115_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_115_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_115_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_115_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint8_t v_verbose_106_; 
v_verbose_106_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*11 + 15);
lean_dec(v_a_102_);
if (v_verbose_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_109_; 
lean_dec_ref(v_e_90_);
v___x_107_ = lean_box(0);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
lean_del_object(v___x_104_);
v___x_111_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1);
v___x_112_ = l_Lean_indentExpr(v_e_90_);
v___x_113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = l_Lean_Meta_Grind_reportIssue(v___x_113_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
return v___x_114_;
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec_ref(v_e_90_);
v_a_116_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_101_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_101_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___boxed(lean_object* v_e_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(lean_object* v_e_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_136_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___boxed(lean_object* v_e_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(v_e_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec(v_a_150_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(lean_object* v_msg_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = l_Lean_instInhabitedExpr;
v___x_164_ = lean_panic_fn(v___x_163_, v_msg_162_);
return v___x_164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9));
v___x_182_ = lean_unsigned_to_nat(14u);
v___x_183_ = lean_unsigned_to_nat(22u);
v___x_184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8));
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7));
v___x_186_ = l_mkPanicMessageWithDecl(v___x_185_, v___x_184_, v___x_183_, v___x_182_, v___x_181_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_type_202_; lean_object* v_u_203_; lean_object* v_leInst_x3f_204_; lean_object* v_ltInst_x3f_205_; lean_object* v_lawfulOrderLTInst_x3f_206_; lean_object* v_isPreorderInst_x3f_207_; lean_object* v_ringInst_x3f_208_; lean_object* v_orderedRingInst_x3f_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_275_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref(v___x_200_);
v_type_202_ = lean_ctor_get(v_a_201_, 2);
lean_inc_ref(v_type_202_);
v_u_203_ = lean_ctor_get(v_a_201_, 3);
lean_inc(v_u_203_);
v_leInst_x3f_204_ = lean_ctor_get(v_a_201_, 5);
lean_inc(v_leInst_x3f_204_);
v_ltInst_x3f_205_ = lean_ctor_get(v_a_201_, 6);
lean_inc(v_ltInst_x3f_205_);
v_lawfulOrderLTInst_x3f_206_ = lean_ctor_get(v_a_201_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_206_);
v_isPreorderInst_x3f_207_ = lean_ctor_get(v_a_201_, 8);
lean_inc(v_isPreorderInst_x3f_207_);
v_ringInst_x3f_208_ = lean_ctor_get(v_a_201_, 12);
lean_inc(v_ringInst_x3f_208_);
v_orderedRingInst_x3f_209_ = lean_ctor_get(v_a_201_, 14);
lean_inc(v_orderedRingInst_x3f_209_);
lean_dec(v_a_201_);
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4));
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v_u_203_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = l_Lean_mkConst(v___x_210_, v___x_212_);
if (lean_obj_tag(v_ringInst_x3f_208_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_280_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_279_);
v___y_275_ = v___x_280_;
goto v___jp_274_;
}
else
{
lean_object* v_val_281_; 
v_val_281_ = lean_ctor_get(v_ringInst_x3f_208_, 0);
lean_inc(v_val_281_);
lean_dec_ref(v_ringInst_x3f_208_);
v___y_275_ = v_val_281_;
goto v___jp_274_;
}
v___jp_214_:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_inc_ref(v_a_187_);
v___x_221_ = l_Lean_mkApp8(v___x_213_, v_type_202_, v___y_217_, v___y_216_, v___y_219_, v___y_218_, v___y_215_, v___y_220_, v_a_187_);
lean_inc(v_a_198_);
lean_inc_ref(v_a_197_);
lean_inc(v_a_196_);
lean_inc_ref(v_a_195_);
lean_inc_ref(v___x_221_);
v___x_222_ = lean_infer_type(v___x_221_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref(v___x_222_);
v___x_224_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_187_, v_a_189_);
lean_dec_ref(v_a_187_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref(v___x_224_);
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6));
v___x_227_ = l_Lean_Meta_Grind_addNewRawFact(v___x_221_, v_a_223_, v_a_225_, v___x_226_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
return v___x_227_;
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_a_223_);
lean_dec_ref(v___x_221_);
v_a_228_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_224_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_224_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec_ref(v___x_221_);
lean_dec_ref(v_a_187_);
v_a_236_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_222_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_222_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
v___jp_244_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_209_) == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_251_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_250_);
v___y_215_ = v___y_249_;
v___y_216_ = v___y_246_;
v___y_217_ = v___y_245_;
v___y_218_ = v___y_248_;
v___y_219_ = v___y_247_;
v___y_220_ = v___x_251_;
goto v___jp_214_;
}
else
{
lean_object* v_val_252_; 
v_val_252_ = lean_ctor_get(v_orderedRingInst_x3f_209_, 0);
lean_inc(v_val_252_);
lean_dec_ref(v_orderedRingInst_x3f_209_);
v___y_215_ = v___y_249_;
v___y_216_ = v___y_246_;
v___y_217_ = v___y_245_;
v___y_218_ = v___y_248_;
v___y_219_ = v___y_247_;
v___y_220_ = v_val_252_;
goto v___jp_214_;
}
}
v___jp_253_:
{
if (lean_obj_tag(v_isPreorderInst_x3f_207_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_259_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_258_);
v___y_245_ = v___y_255_;
v___y_246_ = v___y_254_;
v___y_247_ = v___y_256_;
v___y_248_ = v___y_257_;
v___y_249_ = v___x_259_;
goto v___jp_244_;
}
else
{
lean_object* v_val_260_; 
v_val_260_ = lean_ctor_get(v_isPreorderInst_x3f_207_, 0);
lean_inc(v_val_260_);
lean_dec_ref(v_isPreorderInst_x3f_207_);
v___y_245_ = v___y_255_;
v___y_246_ = v___y_254_;
v___y_247_ = v___y_256_;
v___y_248_ = v___y_257_;
v___y_249_ = v_val_260_;
goto v___jp_244_;
}
}
v___jp_261_:
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_206_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_266_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_265_);
v___y_254_ = v___y_263_;
v___y_255_ = v___y_262_;
v___y_256_ = v___y_264_;
v___y_257_ = v___x_266_;
goto v___jp_253_;
}
else
{
lean_object* v_val_267_; 
v_val_267_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_206_, 0);
lean_inc(v_val_267_);
lean_dec_ref(v_lawfulOrderLTInst_x3f_206_);
v___y_254_ = v___y_263_;
v___y_255_ = v___y_262_;
v___y_256_ = v___y_264_;
v___y_257_ = v_val_267_;
goto v___jp_253_;
}
}
v___jp_268_:
{
if (lean_obj_tag(v_ltInst_x3f_205_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_272_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_271_);
v___y_262_ = v___y_269_;
v___y_263_ = v___y_270_;
v___y_264_ = v___x_272_;
goto v___jp_261_;
}
else
{
lean_object* v_val_273_; 
v_val_273_ = lean_ctor_get(v_ltInst_x3f_205_, 0);
lean_inc(v_val_273_);
lean_dec_ref(v_ltInst_x3f_205_);
v___y_262_ = v___y_269_;
v___y_263_ = v___y_270_;
v___y_264_ = v_val_273_;
goto v___jp_261_;
}
}
v___jp_274_:
{
if (lean_obj_tag(v_leInst_x3f_204_) == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_277_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_276_);
v___y_269_ = v___y_275_;
v___y_270_ = v___x_277_;
goto v___jp_268_;
}
else
{
lean_object* v_val_278_; 
v_val_278_ = lean_ctor_get(v_leInst_x3f_204_, 0);
lean_inc(v_val_278_);
lean_dec_ref(v_leInst_x3f_204_);
v___y_269_ = v___y_275_;
v___y_270_ = v_val_278_;
goto v___jp_268_;
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec_ref(v_a_187_);
v_a_282_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_200_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_200_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___boxed(lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec(v_a_292_);
lean_dec(v_a_291_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(lean_object* v_generation_304_, lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_305_, v_a_307_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; uint8_t v___x_320_; uint8_t v___x_321_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
v___x_320_ = 1;
v___x_321_ = lean_unbox(v_a_319_);
lean_dec(v_a_319_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_box(0);
lean_inc(v_a_316_);
lean_inc_ref(v_a_315_);
lean_inc(v_a_314_);
lean_inc_ref(v_a_313_);
lean_inc(v_a_312_);
lean_inc_ref(v_a_311_);
lean_inc(v_a_310_);
lean_inc_ref(v_a_309_);
lean_inc(v_a_308_);
lean_inc(v_a_307_);
lean_inc_ref(v_e_305_);
v___x_323_ = lean_grind_internalize(v_e_305_, v_generation_304_, v___x_322_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v___x_324_; 
lean_dec_ref(v___x_323_);
v___x_324_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_305_, v___x_320_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_333_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_a_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_329_);
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_334_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_324_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref(v_e_305_);
v_a_342_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_323_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_323_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v___x_350_; 
lean_dec(v_generation_304_);
v___x_350_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_305_, v___x_320_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_359_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_a_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_350_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_350_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_e_305_);
lean_dec(v_generation_304_);
v_a_368_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_318_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_318_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___boxed(lean_object* v_generation_376_, lean_object* v_e_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_376_, v_e_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec(v_a_379_);
lean_dec(v_a_378_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(lean_object* v_generation_391_, lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; 
lean_inc_ref(v_e_392_);
v___x_405_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_392_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; 
lean_dec_ref(v___x_405_);
v___x_406_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_391_, v_e_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_406_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v_e_392_);
lean_dec(v_generation_391_);
v_a_407_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar___boxed(lean_object* v_generation_415_, lean_object* v_e_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_415_, v_e_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(uint8_t v_skipVar_430_, lean_object* v_generation_431_, lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
if (v_skipVar_430_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_431_, v_e_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_a_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_445_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_445_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec_ref(v_e_432_);
lean_dec(v_generation_431_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar___boxed(lean_object* v_skipVar_465_, lean_object* v_generation_466_, lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
uint8_t v_skipVar_boxed_480_; lean_object* v_res_481_; 
v_skipVar_boxed_480_ = lean_unbox(v_skipVar_465_);
v_res_481_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_boxed_480_, v_generation_466_, v_e_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec(v_a_469_);
lean_dec(v_a_468_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(uint8_t v_skipVar_482_, lean_object* v_generation_483_, lean_object* v_e_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; 
lean_inc_ref(v_e_484_);
v___x_497_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_484_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_497_, 0);
lean_dec(v_unused_524_);
v___x_499_ = v___x_497_;
v_isShared_500_ = v_isSharedCheck_523_;
goto v_resetjp_498_;
}
else
{
lean_dec(v___x_497_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_523_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
if (v_skipVar_482_ == 0)
{
lean_object* v___x_501_; 
lean_del_object(v___x_499_);
v___x_501_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_483_, v_e_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v_a_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_501_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_501_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec_ref(v_e_484_);
lean_dec(v_generation_483_);
v___x_519_ = lean_box(0);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_519_);
v___x_521_ = v___x_499_;
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
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec_ref(v_e_484_);
lean_dec(v_generation_483_);
v_a_525_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_497_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_497_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar___boxed(lean_object* v_skipVar_533_, lean_object* v_generation_534_, lean_object* v_e_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
uint8_t v_skipVar_boxed_548_; lean_object* v_res_549_; 
v_skipVar_boxed_548_ = lean_unbox(v_skipVar_533_);
v_res_549_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_boxed_548_, v_generation_534_, v_e_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec(v_a_537_);
lean_dec(v_a_536_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(lean_object* v_e_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v_ofNatZero_565_; lean_object* v___x_566_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
v_ofNatZero_565_ = lean_ctor_get(v_a_564_, 18);
lean_inc_ref(v_ofNatZero_565_);
lean_dec(v_a_564_);
v___x_566_ = l_Lean_Meta_isDefEqD(v_e_550_, v_ofNatZero_565_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
return v___x_566_;
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v_e_550_);
v_a_567_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_563_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_563_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero___boxed(lean_object* v_e_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec(v_a_577_);
lean_dec(v_a_576_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(lean_object* v_generation_624_, lean_object* v_e_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; 
lean_inc_ref(v_e_625_);
v___x_638_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_625_, v_a_634_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v___x_640_ = l_Lean_Expr_cleanupAnnotations(v_a_639_);
v___x_641_ = l_Lean_Expr_isApp(v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec_ref(v___x_640_);
v___x_642_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_642_;
}
else
{
lean_object* v_arg_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_arg_643_ = lean_ctor_get(v___x_640_, 1);
lean_inc_ref(v_arg_643_);
v___x_644_ = l_Lean_Expr_appFnCleanup___redArg(v___x_640_);
v___x_645_ = l_Lean_Expr_isApp(v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec_ref(v___x_644_);
lean_dec_ref(v_arg_643_);
v___x_646_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_646_;
}
else
{
lean_object* v_arg_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_arg_647_ = lean_ctor_get(v___x_644_, 1);
lean_inc_ref(v_arg_647_);
v___x_648_ = l_Lean_Expr_appFnCleanup___redArg(v___x_644_);
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2));
v___x_650_ = l_Lean_Expr_isConstOf(v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_Expr_isApp(v___x_648_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec_ref(v___x_648_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
v___x_652_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_652_;
}
else
{
lean_object* v_arg_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_arg_653_ = lean_ctor_get(v___x_648_, 1);
lean_inc_ref(v_arg_653_);
v___x_654_ = l_Lean_Expr_appFnCleanup___redArg(v___x_648_);
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5));
v___x_656_ = l_Lean_Expr_isConstOf(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8));
v___x_658_ = l_Lean_Expr_isConstOf(v___x_654_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11));
v___x_660_ = l_Lean_Expr_isConstOf(v___x_654_, v___x_659_);
if (v___x_660_ == 0)
{
uint8_t v___x_661_; 
v___x_661_ = l_Lean_Expr_isApp(v___x_654_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v___x_654_);
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
v___x_662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_654_);
v___x_664_ = l_Lean_Expr_isApp(v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v___x_663_);
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = l_Lean_Expr_appFnCleanup___redArg(v___x_663_);
v___x_667_ = l_Lean_Expr_isApp(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec_ref(v___x_666_);
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
v___x_668_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = l_Lean_Expr_appFnCleanup___redArg(v___x_666_);
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14));
v___x_671_ = l_Lean_Expr_isConstOf(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17));
v___x_673_ = l_Lean_Expr_isConstOf(v___x_669_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20));
v___x_675_ = l_Lean_Expr_isConstOf(v___x_669_, v___x_674_);
lean_dec_ref(v___x_669_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
v___x_676_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; uint8_t v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref(v___x_677_);
v___x_679_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_678_, v_arg_653_);
lean_dec_ref(v_arg_653_);
lean_dec(v_a_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
v___x_680_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; 
lean_dec_ref(v_e_625_);
lean_inc(v_generation_624_);
v___x_681_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_624_, v_arg_647_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v___x_681_);
v___x_683_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_624_, v_arg_643_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_688_, 0, v_a_682_);
lean_ctor_set(v___x_688_, 1, v_a_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_dec(v_a_682_);
return v___x_683_;
}
}
else
{
lean_dec_ref(v_arg_643_);
lean_dec(v_generation_624_);
return v___x_681_;
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_693_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_677_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_677_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
else
{
lean_object* v___x_701_; 
lean_dec_ref(v___x_669_);
v___x_701_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; uint8_t v___x_703_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref(v___x_701_);
v___x_703_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_702_, v_arg_653_);
lean_dec_ref(v_arg_653_);
lean_dec(v_a_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
v___x_704_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; 
lean_dec_ref(v_e_625_);
lean_inc(v_generation_624_);
v___x_705_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_624_, v_arg_647_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref(v___x_705_);
v___x_707_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_624_, v_arg_643_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_716_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_712_, 0, v_a_706_);
lean_ctor_set(v___x_712_, 1, v_a_708_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_dec(v_a_706_);
return v___x_707_;
}
}
else
{
lean_dec_ref(v_arg_643_);
lean_dec(v_generation_624_);
return v___x_705_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_717_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_701_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_701_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
else
{
lean_object* v___x_725_; 
lean_dec_ref(v___x_669_);
lean_inc(v_generation_624_);
v___x_725_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_624_, v_arg_653_, v_arg_647_, v_arg_643_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec_ref(v_arg_653_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_735_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_735_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
if (lean_obj_tag(v_a_726_) == 1)
{
lean_object* v_val_730_; lean_object* v___x_732_; 
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_val_730_ = lean_ctor_get(v_a_726_, 0);
lean_inc(v_val_730_);
lean_dec_ref(v_a_726_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_val_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_val_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
lean_object* v___x_734_; 
lean_del_object(v___x_728_);
lean_dec(v_a_726_);
v___x_734_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_734_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_736_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_725_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_725_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
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
lean_object* v___x_744_; 
lean_dec_ref(v___x_654_);
lean_dec_ref(v_arg_653_);
v___x_744_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; uint8_t v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref(v___x_744_);
v___x_746_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_a_745_, v_arg_647_);
lean_dec_ref(v_arg_647_);
lean_dec(v_a_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec_ref(v_arg_643_);
v___x_747_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; 
lean_dec_ref(v_e_625_);
v___x_748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_624_, v_arg_643_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_757_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_757_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_753_, 0, v_a_749_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
return v___x_748_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_758_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_744_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_744_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
else
{
lean_object* v___x_766_; 
lean_dec_ref(v___x_654_);
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
lean_inc_ref(v_e_625_);
v___x_766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_777_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_777_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_777_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_777_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
uint8_t v___x_771_; 
v___x_771_ = lean_unbox(v_a_767_);
lean_dec(v_a_767_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_del_object(v___x_769_);
v___x_772_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_772_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v___x_773_ = lean_box(0);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_773_);
v___x_775_ = v___x_769_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_778_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_766_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_766_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
else
{
lean_object* v___x_786_; 
lean_dec_ref(v___x_654_);
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_arg_647_);
v___x_786_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; uint8_t v___y_789_; lean_object* v_orderedRingInst_x3f_801_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_786_);
v_orderedRingInst_x3f_801_ = lean_ctor_get(v_a_787_, 14);
lean_inc(v_orderedRingInst_x3f_801_);
lean_dec(v_a_787_);
if (lean_obj_tag(v_orderedRingInst_x3f_801_) == 0)
{
v___y_789_ = v___x_650_;
goto v___jp_788_;
}
else
{
lean_dec_ref(v_orderedRingInst_x3f_801_);
v___y_789_ = v___x_656_;
goto v___jp_788_;
}
v___jp_788_:
{
if (v___y_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec_ref(v_arg_643_);
v___x_790_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_790_;
}
else
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_643_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v___x_792_; 
lean_dec_ref(v___x_791_);
v___x_792_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_792_;
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_793_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_802_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_786_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_786_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
else
{
lean_object* v___x_810_; 
lean_dec_ref(v___x_648_);
lean_dec_ref(v_arg_647_);
v___x_810_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_821_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_821_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v___x_815_; 
v___x_815_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_811_, v_arg_643_);
lean_dec_ref(v_arg_643_);
lean_dec(v_a_811_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_del_object(v___x_813_);
v___x_816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_624_, v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_816_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v___x_817_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_822_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_810_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_810_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_e_625_);
lean_dec(v_generation_624_);
v_a_830_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_638_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_638_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(lean_object* v_generation_838_, lean_object* v_i_839_, lean_object* v_a_840_, lean_object* v_b_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; uint8_t v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref(v___x_854_);
v___x_856_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_855_, v_i_839_);
lean_dec(v_a_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_911_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_911_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_911_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_911_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
uint8_t v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_a_858_, v_i_839_);
lean_dec(v_a_858_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_865_; 
lean_dec_ref(v_b_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_generation_838_);
v___x_863_ = lean_box(0);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_863_);
v___x_865_ = v___x_860_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
else
{
lean_object* v___x_867_; 
lean_del_object(v___x_860_);
v___x_867_ = l_Lean_Meta_getNatValue_x3f(v_a_840_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec_ref(v_a_840_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_902_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_902_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_902_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_902_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
if (lean_obj_tag(v_a_868_) == 1)
{
lean_object* v_val_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_897_; 
lean_del_object(v___x_870_);
v_val_872_ = lean_ctor_get(v_a_868_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_868_);
if (v_isSharedCheck_897_ == 0)
{
v___x_874_ = v_a_868_;
v_isShared_875_ = v_isSharedCheck_897_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_val_872_);
lean_dec(v_a_868_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_897_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_838_, v_b_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_888_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v_val_872_);
lean_ctor_set(v___x_881_, 1, v_a_877_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_881_);
v___x_883_ = v___x_874_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_883_);
v___x_885_ = v___x_879_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_874_);
lean_dec(v_val_872_);
v_a_889_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_876_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_876_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
else
{
lean_object* v___x_898_; lean_object* v___x_900_; 
lean_dec(v_a_868_);
lean_dec_ref(v_b_841_);
lean_dec(v_generation_838_);
v___x_898_ = lean_box(0);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_898_);
v___x_900_ = v___x_870_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_b_841_);
lean_dec(v_generation_838_);
v_a_903_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_867_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_867_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v_b_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_generation_838_);
v_a_912_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_857_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_857_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Meta_getIntValue_x3f(v_a_840_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_955_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_955_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_955_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_955_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
if (lean_obj_tag(v_a_921_) == 1)
{
lean_object* v_val_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_950_; 
lean_del_object(v___x_923_);
v_val_925_ = lean_ctor_get(v_a_921_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_921_);
if (v_isSharedCheck_950_ == 0)
{
v___x_927_ = v_a_921_;
v_isShared_928_ = v_isSharedCheck_950_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_val_925_);
lean_dec(v_a_921_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_950_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; 
v___x_929_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_838_, v_b_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_941_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_941_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_941_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_941_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_934_, 0, v_val_925_);
lean_ctor_set(v___x_934_, 1, v_a_930_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_934_);
v___x_936_ = v___x_927_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_940_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_938_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_936_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_del_object(v___x_927_);
lean_dec(v_val_925_);
v_a_942_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_929_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_929_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_a_921_);
lean_dec_ref(v_b_841_);
lean_dec(v_generation_838_);
v___x_951_ = lean_box(0);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_951_);
v___x_953_ = v___x_923_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_b_841_);
lean_dec(v_generation_838_);
v_a_956_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_920_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_920_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec_ref(v_b_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_generation_838_);
v_a_964_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_854_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_854_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul___boxed(lean_object* v_generation_972_, lean_object* v_i_973_, lean_object* v_a_974_, lean_object* v_b_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_972_, v_i_973_, v_a_974_, v_b_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_i_973_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___boxed(lean_object* v_generation_989_, lean_object* v_e_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_989_, v_e_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec(v_a_992_);
lean_dec(v_a_991_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object* v_e_1006_, uint8_t v_skipVar_1007_, lean_object* v_generation_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; 
lean_inc_ref(v_e_1006_);
v___x_1021_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1006_, v_a_1017_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = l_Lean_Expr_cleanupAnnotations(v_a_1022_);
v___x_1024_ = l_Lean_Expr_isApp(v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec_ref(v___x_1023_);
v___x_1025_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1025_;
}
else
{
lean_object* v_arg_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_arg_1026_ = lean_ctor_get(v___x_1023_, 1);
lean_inc_ref(v_arg_1026_);
v___x_1027_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1023_);
v___x_1028_ = l_Lean_Expr_isApp(v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v___x_1027_);
lean_dec_ref(v_arg_1026_);
v___x_1029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1029_;
}
else
{
lean_object* v_arg_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_arg_1030_ = lean_ctor_get(v___x_1027_, 1);
lean_inc_ref(v_arg_1030_);
v___x_1031_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1027_);
v___x_1032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2));
v___x_1033_ = l_Lean_Expr_isConstOf(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Expr_isApp(v___x_1031_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v___x_1031_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
v___x_1035_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1035_;
}
else
{
lean_object* v_arg_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_arg_1036_ = lean_ctor_get(v___x_1031_, 1);
lean_inc_ref(v_arg_1036_);
v___x_1037_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1031_);
v___x_1038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5));
v___x_1039_ = l_Lean_Expr_isConstOf(v___x_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8));
v___x_1041_ = l_Lean_Expr_isConstOf(v___x_1037_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11));
v___x_1043_ = l_Lean_Expr_isConstOf(v___x_1037_, v___x_1042_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; 
v___x_1044_ = l_Lean_Expr_isApp(v___x_1037_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_dec_ref(v___x_1037_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
v___x_1045_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1037_);
v___x_1047_ = l_Lean_Expr_isApp(v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
lean_dec_ref(v___x_1046_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
v___x_1048_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1046_);
v___x_1050_ = l_Lean_Expr_isApp(v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
lean_dec_ref(v___x_1049_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
v___x_1051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1049_);
v___x_1053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14));
v___x_1054_ = l_Lean_Expr_isConstOf(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17));
v___x_1056_ = l_Lean_Expr_isConstOf(v___x_1052_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20));
v___x_1058_ = l_Lean_Expr_isConstOf(v___x_1052_, v___x_1057_);
lean_dec_ref(v___x_1052_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
v___x_1059_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; uint8_t v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1061_, v_arg_1036_);
lean_dec_ref(v_arg_1036_);
lean_dec(v_a_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
v___x_1063_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; 
lean_dec_ref(v_e_1006_);
lean_inc(v_generation_1008_);
v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1008_, v_arg_1030_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1008_, v_arg_1026_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1076_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1076_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1076_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_a_1065_);
lean_ctor_set(v___x_1071_, 1, v_a_1067_);
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1072_);
v___x_1074_ = v___x_1069_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec(v_a_1065_);
v_a_1077_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1066_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1066_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v_arg_1026_);
lean_dec(v_generation_1008_);
v_a_1085_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1064_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1064_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v_a_1093_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1060_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1060_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
else
{
lean_object* v___x_1101_; 
lean_dec_ref(v___x_1052_);
v___x_1101_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; uint8_t v___x_1103_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_1102_, v_arg_1036_);
lean_dec_ref(v_arg_1036_);
lean_dec(v_a_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
v___x_1104_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; 
lean_dec_ref(v_e_1006_);
lean_inc(v_generation_1008_);
v___x_1105_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1008_, v_arg_1030_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1008_, v_arg_1026_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1117_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1112_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_a_1106_);
lean_ctor_set(v___x_1112_, 1, v_a_1108_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1113_);
v___x_1115_ = v___x_1110_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_a_1106_);
v_a_1118_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1107_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1107_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v_arg_1026_);
lean_dec(v_generation_1008_);
v_a_1126_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1105_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1105_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v_a_1134_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1101_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1101_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
else
{
lean_object* v___x_1142_; 
lean_dec_ref(v___x_1052_);
lean_inc(v_generation_1008_);
v___x_1142_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_1008_, v_arg_1036_, v_arg_1030_, v_arg_1026_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec_ref(v_arg_1036_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
if (lean_obj_tag(v_a_1143_) == 1)
{
lean_dec_ref(v_a_1143_);
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
return v___x_1142_;
}
else
{
lean_object* v___x_1144_; 
lean_dec(v_a_1143_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1144_;
}
}
else
{
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
return v___x_1142_;
}
}
}
}
}
}
else
{
lean_object* v___x_1145_; 
lean_dec_ref(v___x_1037_);
lean_dec_ref(v_arg_1036_);
v___x_1145_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; uint8_t v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_a_1146_, v_arg_1030_);
lean_dec_ref(v_arg_1030_);
lean_dec(v_a_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec_ref(v_arg_1026_);
v___x_1148_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref(v_e_1006_);
v___x_1149_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1008_, v_arg_1026_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1159_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_a_1150_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1149_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1149_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v_a_1168_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1145_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1145_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
else
{
lean_object* v___x_1176_; 
lean_dec_ref(v___x_1037_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_arg_1026_);
lean_inc_ref(v_e_1006_);
v___x_1176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1187_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1187_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1187_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_unbox(v_a_1177_);
lean_dec(v_a_1177_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_del_object(v___x_1179_);
v___x_1182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v___x_1183_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0));
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1183_);
v___x_1185_ = v___x_1179_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v_a_1188_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1176_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1176_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
else
{
lean_object* v___x_1196_; 
lean_dec_ref(v___x_1037_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1030_);
v___x_1196_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; uint8_t v___y_1199_; lean_object* v_orderedRingInst_x3f_1211_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
v_orderedRingInst_x3f_1211_ = lean_ctor_get(v_a_1197_, 14);
lean_inc(v_orderedRingInst_x3f_1211_);
lean_dec(v_a_1197_);
if (lean_obj_tag(v_orderedRingInst_x3f_1211_) == 0)
{
v___y_1199_ = v___x_1033_;
goto v___jp_1198_;
}
else
{
lean_dec_ref(v_orderedRingInst_x3f_1211_);
v___y_1199_ = v___x_1039_;
goto v___jp_1198_;
}
v___jp_1198_:
{
if (v___y_1199_ == 0)
{
lean_object* v___x_1200_; 
lean_dec_ref(v_arg_1026_);
v___x_1200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1200_;
}
else
{
lean_object* v___x_1201_; 
v___x_1201_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_1026_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1202_; 
lean_dec_ref(v___x_1201_);
v___x_1202_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1202_;
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v_a_1203_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1201_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_arg_1026_);
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v_a_1212_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1196_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1196_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
else
{
lean_object* v___x_1220_; 
lean_dec_ref(v___x_1031_);
lean_dec_ref(v_arg_1030_);
v___x_1220_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1231_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1231_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1231_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
uint8_t v___x_1225_; 
v___x_1225_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1221_, v_arg_1026_);
lean_dec_ref(v_arg_1026_);
lean_dec(v_a_1221_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_del_object(v___x_1223_);
v___x_1226_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1007_, v_generation_1008_, v_e_1006_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v___x_1227_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0));
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1227_);
v___x_1229_ = v___x_1223_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v_arg_1026_);
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v_a_1232_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1220_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1220_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_generation_1008_);
lean_dec_ref(v_e_1006_);
v_a_1240_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1021_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1021_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f___boxed(lean_object* v_e_1248_, lean_object* v_skipVar_1249_, lean_object* v_generation_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
uint8_t v_skipVar_boxed_1263_; lean_object* v_res_1264_; 
v_skipVar_boxed_1263_ = lean_unbox(v_skipVar_1249_);
v_res_1264_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_e_1248_, v_skipVar_boxed_1263_, v_generation_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec(v_a_1251_);
return v_res_1264_;
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
