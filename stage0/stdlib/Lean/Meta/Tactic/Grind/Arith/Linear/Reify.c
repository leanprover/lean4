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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "`grind` internal error, linarith term has not been internalized"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1);
v___x_117_ = l_Lean_indentExpr(v_e_108_);
v___x_118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_109_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
uint8_t v_verbose_124_; 
v_verbose_124_ = lean_ctor_get_uint8(v_a_120_, 0);
lean_dec(v_a_120_);
if (v_verbose_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_dec_ref_known(v___x_118_, 2);
v___x_125_ = lean_box(0);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_125_);
v___x_127_ = v___x_122_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
else
{
lean_object* v___x_129_; 
lean_del_object(v___x_122_);
v___x_129_ = l_Lean_Meta_Sym_reportIssue(v___x_118_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
return v___x_129_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref_known(v___x_118_, 2);
v_a_131_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_119_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_119_);
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
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_293_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_293_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_293_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_293_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_lawfulOrderLTInst_x3f_217_; 
v_lawfulOrderLTInst_x3f_217_ = lean_ctor_get(v_a_213_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_217_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_217_) == 1)
{
lean_object* v_type_218_; lean_object* v_u_219_; lean_object* v_leInst_x3f_220_; lean_object* v_ltInst_x3f_221_; lean_object* v_isPreorderInst_x3f_222_; lean_object* v_ringInst_x3f_223_; lean_object* v_orderedRingInst_x3f_224_; lean_object* v_val_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_282_; 
lean_del_object(v___x_215_);
v_type_218_ = lean_ctor_get(v_a_213_, 2);
lean_inc_ref(v_type_218_);
v_u_219_ = lean_ctor_get(v_a_213_, 3);
lean_inc(v_u_219_);
v_leInst_x3f_220_ = lean_ctor_get(v_a_213_, 5);
lean_inc(v_leInst_x3f_220_);
v_ltInst_x3f_221_ = lean_ctor_get(v_a_213_, 6);
lean_inc(v_ltInst_x3f_221_);
v_isPreorderInst_x3f_222_ = lean_ctor_get(v_a_213_, 8);
lean_inc(v_isPreorderInst_x3f_222_);
v_ringInst_x3f_223_ = lean_ctor_get(v_a_213_, 12);
lean_inc(v_ringInst_x3f_223_);
v_orderedRingInst_x3f_224_ = lean_ctor_get(v_a_213_, 14);
lean_inc(v_orderedRingInst_x3f_224_);
lean_dec(v_a_213_);
v_val_225_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_217_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_217_, 1);
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4));
v___x_227_ = lean_box(0);
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v_u_219_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = l_Lean_mkConst(v___x_226_, v___x_228_);
if (lean_obj_tag(v_ringInst_x3f_223_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_287_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_286_);
v___y_282_ = v___x_287_;
goto v___jp_281_;
}
else
{
lean_object* v_val_288_; 
v_val_288_ = lean_ctor_get(v_ringInst_x3f_223_, 0);
lean_inc(v_val_288_);
lean_dec_ref_known(v_ringInst_x3f_223_, 1);
v___y_282_ = v_val_288_;
goto v___jp_281_;
}
v___jp_230_:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_inc_ref(v_a_199_);
v___x_236_ = l_Lean_mkApp8(v___x_229_, v_type_218_, v___y_233_, v___y_232_, v___y_231_, v_val_225_, v___y_234_, v___y_235_, v_a_199_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc_ref(v___x_236_);
v___x_237_ = lean_infer_type(v___x_236_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_199_, v_a_201_);
lean_dec_ref(v_a_199_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6));
v___x_242_ = lean_box(1);
v___x_243_ = l_Lean_Meta_Grind_addNewRawFact(v___x_236_, v_a_238_, v_a_240_, v___x_241_, v___x_242_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_243_;
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_a_238_);
lean_dec_ref(v___x_236_);
v_a_244_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_239_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_239_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec_ref(v___x_236_);
lean_dec_ref(v_a_199_);
v_a_252_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_237_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_237_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
v___jp_260_:
{
if (lean_obj_tag(v_orderedRingInst_x3f_224_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_266_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_265_);
v___y_231_ = v___y_261_;
v___y_232_ = v___y_262_;
v___y_233_ = v___y_263_;
v___y_234_ = v___y_264_;
v___y_235_ = v___x_266_;
goto v___jp_230_;
}
else
{
lean_object* v_val_267_; 
v_val_267_ = lean_ctor_get(v_orderedRingInst_x3f_224_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v_orderedRingInst_x3f_224_, 1);
v___y_231_ = v___y_261_;
v___y_232_ = v___y_262_;
v___y_233_ = v___y_263_;
v___y_234_ = v___y_264_;
v___y_235_ = v_val_267_;
goto v___jp_230_;
}
}
v___jp_268_:
{
if (lean_obj_tag(v_isPreorderInst_x3f_222_) == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_273_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_272_);
v___y_261_ = v___y_271_;
v___y_262_ = v___y_269_;
v___y_263_ = v___y_270_;
v___y_264_ = v___x_273_;
goto v___jp_260_;
}
else
{
lean_object* v_val_274_; 
v_val_274_ = lean_ctor_get(v_isPreorderInst_x3f_222_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v_isPreorderInst_x3f_222_, 1);
v___y_261_ = v___y_271_;
v___y_262_ = v___y_269_;
v___y_263_ = v___y_270_;
v___y_264_ = v_val_274_;
goto v___jp_260_;
}
}
v___jp_275_:
{
if (lean_obj_tag(v_ltInst_x3f_221_) == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_279_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_278_);
v___y_269_ = v___y_277_;
v___y_270_ = v___y_276_;
v___y_271_ = v___x_279_;
goto v___jp_268_;
}
else
{
lean_object* v_val_280_; 
v_val_280_ = lean_ctor_get(v_ltInst_x3f_221_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v_ltInst_x3f_221_, 1);
v___y_269_ = v___y_277_;
v___y_270_ = v___y_276_;
v___y_271_ = v_val_280_;
goto v___jp_268_;
}
}
v___jp_281_:
{
if (lean_obj_tag(v_leInst_x3f_220_) == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
v___x_284_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_283_);
v___y_276_ = v___y_282_;
v___y_277_ = v___x_284_;
goto v___jp_275_;
}
else
{
lean_object* v_val_285_; 
v_val_285_ = lean_ctor_get(v_leInst_x3f_220_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v_leInst_x3f_220_, 1);
v___y_276_ = v___y_282_;
v___y_277_ = v_val_285_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v___x_289_; lean_object* v___x_291_; 
lean_dec(v_lawfulOrderLTInst_x3f_217_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_199_);
v___x_289_ = lean_box(0);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_289_);
v___x_291_ = v___x_215_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_a_199_);
v_a_294_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_212_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_212_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___boxed(lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
lean_dec(v_a_303_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0_spec__0(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; lean_object* v_env_323_; uint8_t v___x_324_; lean_object* v_env_325_; lean_object* v___x_326_; lean_object* v_toCold_327_; lean_object* v_mctx_328_; lean_object* v_lctx_329_; lean_object* v_options_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_322_ = lean_st_ref_get(v___y_320_);
v_env_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc_ref(v_env_323_);
lean_dec(v___x_322_);
v___x_324_ = 0;
v_env_325_ = l_Lean_Environment_setRecordingDeps(v_env_323_, v___x_324_);
v___x_326_ = lean_st_ref_get(v___y_318_);
v_toCold_327_ = lean_ctor_get(v___y_319_, 0);
v_mctx_328_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_mctx_328_);
lean_dec(v___x_326_);
v_lctx_329_ = lean_ctor_get(v___y_317_, 2);
v_options_330_ = lean_ctor_get(v_toCold_327_, 2);
lean_inc_ref(v_options_330_);
lean_inc_ref(v_lctx_329_);
v___x_331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_331_, 0, v_env_325_);
lean_ctor_set(v___x_331_, 1, v_mctx_328_);
lean_ctor_set(v___x_331_, 2, v_lctx_329_);
lean_ctor_set(v___x_331_, 3, v_options_330_);
v___x_332_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_msgData_316_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0_spec__0___boxed(lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0_spec__0(v_msgData_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___redArg(lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_ref_347_; lean_object* v___x_348_; lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_357_; 
v_ref_347_ = lean_ctor_get(v___y_344_, 2);
v___x_348_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0_spec__0(v_msg_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_357_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
lean_inc(v_ref_347_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_ref_347_);
lean_ctor_set(v___x_353_, 1, v_a_349_);
if (v_isShared_352_ == 0)
{
lean_ctor_set_tag(v___x_351_, 1);
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___redArg___boxed(lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___redArg(v_msg_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__0));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_368_, v_a_370_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; uint8_t v___x_414_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = lean_unbox(v_a_413_);
lean_dec(v_a_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
v___x_415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___closed__1);
v___x_416_ = l_Lean_indentExpr(v_e_368_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___redArg(v___x_417_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
v___y_382_ = v_a_369_;
v___y_383_ = v_a_370_;
v___y_384_ = v_a_371_;
v___y_385_ = v_a_372_;
v___y_386_ = v_a_373_;
v___y_387_ = v_a_374_;
v___y_388_ = v_a_375_;
v___y_389_ = v_a_376_;
v___y_390_ = v_a_377_;
v___y_391_ = v_a_378_;
v___y_392_ = v_a_379_;
goto v___jp_381_;
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v_e_368_);
v_a_427_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_412_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_412_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
v___jp_381_:
{
uint8_t v___x_393_; lean_object* v___x_394_; 
v___x_393_ = 1;
v___x_394_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_368_, v___x_393_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_a_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v_a_404_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_394_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_394_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___boxed(lean_object* v_e_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec(v_a_437_);
lean_dec(v_a_436_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0(lean_object* v_00_u03b1_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___redArg(v_msg_450_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0___boxed(lean_object* v_00_u03b1_464_, lean_object* v_msg_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar_spec__0(v_00_u03b1_464_, v_msg_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec(v___y_467_);
lean_dec(v___y_466_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(lean_object* v_e_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_492_; 
lean_inc_ref(v_e_479_);
v___x_492_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_479_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v___x_493_; 
lean_dec_ref_known(v___x_492_, 1);
v___x_493_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
return v___x_493_;
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v_e_479_);
v_a_494_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_492_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_492_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar___boxed(lean_object* v_e_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_e_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec(v_a_504_);
lean_dec(v_a_503_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(uint8_t v_skipVar_516_, lean_object* v_e_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
if (v_skipVar_516_ == 0)
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_539_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
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
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_530_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v_e_517_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar___boxed(lean_object* v_skipVar_550_, lean_object* v_e_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
uint8_t v_skipVar_boxed_564_; lean_object* v_res_565_; 
v_skipVar_boxed_564_ = lean_unbox(v_skipVar_550_);
v_res_565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_boxed_564_, v_e_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec(v_a_553_);
lean_dec(v_a_552_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(uint8_t v_skipVar_566_, lean_object* v_e_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; 
lean_inc_ref(v_e_567_);
v___x_580_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(v_e_567_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_606_; 
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_607_);
v___x_582_ = v___x_580_;
v_isShared_583_ = v_isSharedCheck_606_;
goto v_resetjp_581_;
}
else
{
lean_dec(v___x_580_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_606_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
if (v_skipVar_566_ == 0)
{
lean_object* v___x_584_; 
lean_del_object(v___x_582_);
v___x_584_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_e_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_593_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_589_, 0, v_a_585_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_589_);
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_584_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec_ref(v_e_567_);
v___x_602_ = lean_box(0);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_602_);
v___x_604_ = v___x_582_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_e_567_);
v_a_608_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_580_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_580_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar___boxed(lean_object* v_skipVar_616_, lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
uint8_t v_skipVar_boxed_630_; lean_object* v_res_631_; 
v_skipVar_boxed_630_ = lean_unbox(v_skipVar_616_);
v_res_631_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_boxed_630_, v_e_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec(v_a_619_);
lean_dec(v_a_618_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(lean_object* v_e_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v_ofNatZero_647_; lean_object* v___x_648_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v_ofNatZero_647_ = lean_ctor_get(v_a_646_, 18);
lean_inc_ref(v_ofNatZero_647_);
lean_dec(v_a_646_);
v___x_648_ = l_Lean_Meta_isDefEqD(v_e_632_, v_ofNatZero_647_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
return v___x_648_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_e_632_);
v_a_649_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_645_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero___boxed(lean_object* v_e_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec(v_a_659_);
lean_dec(v_a_658_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(lean_object* v_e_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; 
lean_inc_ref(v_e_706_);
v___x_719_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_706_, v_a_715_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = l_Lean_Expr_cleanupAnnotations(v_a_720_);
v___x_722_ = l_Lean_Expr_isApp(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec_ref(v___x_721_);
v___x_723_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_723_;
}
else
{
lean_object* v_arg_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_arg_724_ = lean_ctor_get(v___x_721_, 1);
lean_inc_ref(v_arg_724_);
v___x_725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_721_);
v___x_726_ = l_Lean_Expr_isApp(v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v___x_725_);
lean_dec_ref(v_arg_724_);
v___x_727_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_727_;
}
else
{
lean_object* v_arg_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_arg_728_ = lean_ctor_get(v___x_725_, 1);
lean_inc_ref(v_arg_728_);
v___x_729_ = l_Lean_Expr_appFnCleanup___redArg(v___x_725_);
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2));
v___x_731_ = l_Lean_Expr_isConstOf(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_Expr_isApp(v___x_729_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec_ref(v___x_729_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
v___x_733_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_733_;
}
else
{
lean_object* v_arg_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_arg_734_ = lean_ctor_get(v___x_729_, 1);
lean_inc_ref(v_arg_734_);
v___x_735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_729_);
v___x_736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5));
v___x_737_ = l_Lean_Expr_isConstOf(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8));
v___x_739_ = l_Lean_Expr_isConstOf(v___x_735_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11));
v___x_741_ = l_Lean_Expr_isConstOf(v___x_735_, v___x_740_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; 
v___x_742_ = l_Lean_Expr_isApp(v___x_735_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
v___x_743_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = l_Lean_Expr_appFnCleanup___redArg(v___x_735_);
v___x_745_ = l_Lean_Expr_isApp(v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref(v___x_744_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
v___x_746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_746_;
}
else
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = l_Lean_Expr_appFnCleanup___redArg(v___x_744_);
v___x_748_ = l_Lean_Expr_isApp(v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
v___x_749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_749_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_747_);
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14));
v___x_752_ = l_Lean_Expr_isConstOf(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17));
v___x_754_ = l_Lean_Expr_isConstOf(v___x_750_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20));
v___x_756_ = l_Lean_Expr_isConstOf(v___x_750_, v___x_755_);
lean_dec_ref(v___x_750_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
v___x_757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; uint8_t v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_759_, v_arg_734_);
lean_dec_ref(v_arg_734_);
lean_dec(v_a_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
v___x_761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; 
lean_dec_ref(v_e_706_);
v___x_762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_728_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v___x_764_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_724_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_773_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v_a_763_);
lean_ctor_set(v___x_769_, 1, v_a_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_dec(v_a_763_);
return v___x_764_;
}
}
else
{
lean_dec_ref(v_arg_724_);
return v___x_762_;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
lean_dec_ref(v_e_706_);
v_a_774_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_758_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_758_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
else
{
lean_object* v___x_782_; 
lean_dec_ref(v___x_750_);
v___x_782_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; uint8_t v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_783_, v_arg_734_);
lean_dec_ref(v_arg_734_);
lean_dec(v_a_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
v___x_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; 
lean_dec_ref(v_e_706_);
v___x_786_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_728_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_724_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_793_, 0, v_a_787_);
lean_ctor_set(v___x_793_, 1, v_a_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_dec(v_a_787_);
return v___x_788_;
}
}
else
{
lean_dec_ref(v_arg_724_);
return v___x_786_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
lean_dec_ref(v_e_706_);
v_a_798_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_782_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_782_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec_ref(v___x_750_);
v___x_806_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_arg_734_, v_arg_728_, v_arg_724_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec_ref(v_arg_734_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_816_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_816_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
if (lean_obj_tag(v_a_807_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_813_; 
lean_dec_ref(v_e_706_);
v_val_811_ = lean_ctor_get(v_a_807_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v_a_807_, 1);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v_val_811_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_val_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v___x_815_; 
lean_del_object(v___x_809_);
lean_dec(v_a_807_);
v___x_815_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_815_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_e_706_);
v_a_817_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_806_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_806_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
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
lean_object* v___x_825_; 
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_734_);
v___x_825_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; uint8_t v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_a_826_, v_arg_728_);
lean_dec_ref(v_arg_728_);
lean_dec(v_a_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec_ref(v_arg_724_);
v___x_828_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; 
lean_dec_ref(v_e_706_);
v___x_829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_724_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_838_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_834_, 0, v_a_830_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
lean_dec_ref(v_e_706_);
v_a_839_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_825_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_825_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
else
{
lean_object* v___x_847_; 
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_724_);
lean_inc_ref(v_e_706_);
v___x_847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_858_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_858_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; 
v___x_852_ = lean_unbox(v_a_848_);
lean_dec(v_a_848_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_del_object(v___x_850_);
v___x_853_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec_ref(v_e_706_);
v___x_854_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_854_);
v___x_856_ = v___x_850_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec_ref(v_e_706_);
v_a_859_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_847_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_847_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
else
{
lean_object* v___x_867_; 
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_728_);
v___x_867_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_orderedRingInst_x3f_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_orderedRingInst_x3f_869_ = lean_ctor_get(v_a_868_, 14);
lean_inc(v_orderedRingInst_x3f_869_);
lean_dec(v_a_868_);
if (lean_obj_tag(v_orderedRingInst_x3f_869_) == 0)
{
lean_object* v___x_870_; 
lean_dec_ref(v_arg_724_);
v___x_870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
lean_dec_ref_known(v_orderedRingInst_x3f_869_, 1);
v___x_871_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_724_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v___x_872_; 
lean_dec_ref_known(v___x_871_, 1);
v___x_872_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_872_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v_e_706_);
v_a_873_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_871_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v_arg_724_);
lean_dec_ref(v_e_706_);
v_a_881_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_867_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_867_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
else
{
lean_object* v___x_889_; 
lean_dec_ref(v___x_729_);
lean_dec_ref(v_arg_728_);
v___x_889_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_900_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_900_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_900_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_900_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_890_, v_arg_724_);
lean_dec_ref(v_arg_724_);
lean_dec(v_a_890_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_del_object(v___x_892_);
v___x_895_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_e_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec_ref(v_e_706_);
v___x_896_ = lean_box(0);
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
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_arg_724_);
lean_dec_ref(v_e_706_);
v_a_901_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_889_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_889_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_e_706_);
v_a_909_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_719_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_719_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(lean_object* v_i_917_, lean_object* v_a_918_, lean_object* v_b_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; uint8_t v___x_934_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_933_, v_i_917_);
lean_dec(v_a_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_989_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_989_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_989_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_989_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint8_t v___x_940_; 
v___x_940_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_a_936_, v_i_917_);
lean_dec(v_a_936_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec_ref(v_b_919_);
lean_dec_ref(v_a_918_);
v___x_941_ = lean_box(0);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
else
{
lean_object* v___x_945_; 
lean_del_object(v___x_938_);
v___x_945_ = l_Lean_Meta_getNatValue_x3f(v_a_918_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec_ref(v_a_918_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_980_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_980_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_980_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_980_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
if (lean_obj_tag(v_a_946_) == 1)
{
lean_object* v_val_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_975_; 
lean_del_object(v___x_948_);
v_val_950_ = lean_ctor_get(v_a_946_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_a_946_);
if (v_isSharedCheck_975_ == 0)
{
v___x_952_ = v_a_946_;
v_isShared_953_ = v_isSharedCheck_975_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_val_950_);
lean_dec(v_a_946_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_975_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; 
v___x_954_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_b_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_966_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_966_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v_val_950_);
lean_ctor_set(v___x_959_, 1, v_a_955_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_959_);
v___x_961_ = v___x_952_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_961_);
v___x_963_ = v___x_957_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_del_object(v___x_952_);
lean_dec(v_val_950_);
v_a_967_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_954_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_954_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec(v_a_946_);
lean_dec_ref(v_b_919_);
v___x_976_ = lean_box(0);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_976_);
v___x_978_ = v___x_948_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_b_919_);
v_a_981_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_945_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_945_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_b_919_);
lean_dec_ref(v_a_918_);
v_a_990_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_935_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_935_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_getIntValue_x3f(v_a_918_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1033_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1033_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1033_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
if (lean_obj_tag(v_a_999_) == 1)
{
lean_object* v_val_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1028_; 
lean_del_object(v___x_1001_);
v_val_1003_ = lean_ctor_get(v_a_999_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_999_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1005_ = v_a_999_;
v_isShared_1006_ = v_isSharedCheck_1028_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_val_1003_);
lean_dec(v_a_999_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1028_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; 
v___x_1007_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_b_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1019_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1019_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1019_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_val_1003_);
lean_ctor_set(v___x_1012_, 1, v_a_1008_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1012_);
v___x_1014_ = v___x_1005_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1014_);
v___x_1016_ = v___x_1010_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_del_object(v___x_1005_);
lean_dec(v_val_1003_);
v_a_1020_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1007_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1007_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_dec(v_a_999_);
lean_dec_ref(v_b_919_);
v___x_1029_ = lean_box(0);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1029_);
v___x_1031_ = v___x_1001_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_b_919_);
v_a_1034_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_998_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_998_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_b_919_);
lean_dec_ref(v_a_918_);
v_a_1042_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_932_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_932_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul___boxed(lean_object* v_i_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_i_1050_, v_a_1051_, v_b_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_i_1050_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___boxed(lean_object* v_e_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_e_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec(v_a_1067_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object* v_e_1082_, uint8_t v_skipVar_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; 
lean_inc_ref(v_e_1082_);
v___x_1096_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1082_, v_a_1092_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = l_Lean_Expr_cleanupAnnotations(v_a_1097_);
v___x_1099_ = l_Lean_Expr_isApp(v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v___x_1098_);
v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1100_;
}
else
{
lean_object* v_arg_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_arg_1101_ = lean_ctor_get(v___x_1098_, 1);
lean_inc_ref(v_arg_1101_);
v___x_1102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1098_);
v___x_1103_ = l_Lean_Expr_isApp(v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_dec_ref(v___x_1102_);
lean_dec_ref(v_arg_1101_);
v___x_1104_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1104_;
}
else
{
lean_object* v_arg_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_arg_1105_ = lean_ctor_get(v___x_1102_, 1);
lean_inc_ref(v_arg_1105_);
v___x_1106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1102_);
v___x_1107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2));
v___x_1108_ = l_Lean_Expr_isConstOf(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
uint8_t v___x_1109_; 
v___x_1109_ = l_Lean_Expr_isApp(v___x_1106_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
v___x_1110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1110_;
}
else
{
lean_object* v_arg_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_arg_1111_ = lean_ctor_get(v___x_1106_, 1);
lean_inc_ref(v_arg_1111_);
v___x_1112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1106_);
v___x_1113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5));
v___x_1114_ = l_Lean_Expr_isConstOf(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8));
v___x_1116_ = l_Lean_Expr_isConstOf(v___x_1112_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11));
v___x_1118_ = l_Lean_Expr_isConstOf(v___x_1112_, v___x_1117_);
if (v___x_1118_ == 0)
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Lean_Expr_isApp(v___x_1112_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
v___x_1120_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1112_);
v___x_1122_ = l_Lean_Expr_isApp(v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1121_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1121_);
v___x_1125_ = l_Lean_Expr_isApp(v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v___x_1124_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
v___x_1126_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1124_);
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14));
v___x_1129_ = l_Lean_Expr_isConstOf(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17));
v___x_1131_ = l_Lean_Expr_isConstOf(v___x_1127_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20));
v___x_1133_ = l_Lean_Expr_isConstOf(v___x_1127_, v___x_1132_);
lean_dec_ref(v___x_1127_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
v___x_1134_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; uint8_t v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1136_, v_arg_1111_);
lean_dec_ref(v_arg_1111_);
lean_dec(v_a_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
v___x_1138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; 
lean_dec_ref(v_e_1082_);
v___x_1139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_1105_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_1101_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1151_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_a_1140_);
lean_ctor_set(v___x_1146_, 1, v_a_1142_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1147_);
v___x_1149_ = v___x_1144_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_a_1140_);
v_a_1152_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1141_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1141_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_arg_1101_);
v_a_1160_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1139_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1139_);
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
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_e_1082_);
v_a_1168_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1135_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1135_);
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
lean_dec_ref(v___x_1127_);
v___x_1176_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; uint8_t v___x_1178_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_1177_, v_arg_1111_);
lean_dec_ref(v_arg_1111_);
lean_dec(v_a_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
v___x_1179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; 
lean_dec_ref(v_e_1082_);
v___x_1180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_1105_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_1101_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1192_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1192_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1192_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_a_1181_);
lean_ctor_set(v___x_1187_, 1, v_a_1183_);
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_a_1181_);
v_a_1193_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1182_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1182_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
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
lean_dec_ref(v_arg_1101_);
v_a_1201_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1180_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1180_);
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
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_e_1082_);
v_a_1209_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1176_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1176_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
else
{
lean_object* v___x_1217_; 
lean_dec_ref(v___x_1127_);
v___x_1217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_arg_1111_, v_arg_1105_, v_arg_1101_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
lean_dec_ref(v_arg_1111_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
if (lean_obj_tag(v_a_1218_) == 1)
{
lean_dec_ref(v_e_1082_);
return v___x_1217_;
}
else
{
lean_object* v___x_1219_; 
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1219_;
}
}
else
{
lean_dec_ref(v_e_1082_);
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
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_arg_1111_);
v___x_1220_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; uint8_t v___x_1222_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_a_1221_, v_arg_1105_);
lean_dec_ref(v_arg_1105_);
lean_dec(v_a_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
lean_dec_ref(v_arg_1101_);
v___x_1223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; 
lean_dec_ref(v_e_1082_);
v___x_1224_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_arg_1101_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1234_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1234_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1234_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1229_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1225_);
v___x_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1230_);
v___x_1232_ = v___x_1227_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_a_1235_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1224_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1224_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_e_1082_);
v_a_1243_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1220_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1220_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
else
{
lean_object* v___x_1251_; 
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1101_);
lean_inc_ref(v_e_1082_);
v___x_1251_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1262_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1262_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1262_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_unbox(v_a_1252_);
lean_dec(v_a_1252_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_del_object(v___x_1254_);
v___x_1257_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec_ref(v_e_1082_);
v___x_1258_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0));
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1258_);
v___x_1260_ = v___x_1254_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v_e_1082_);
v_a_1263_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1251_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1251_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
else
{
lean_object* v___x_1271_; 
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1105_);
v___x_1271_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v_orderedRingInst_x3f_1273_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v_orderedRingInst_x3f_1273_ = lean_ctor_get(v_a_1272_, 14);
lean_inc(v_orderedRingInst_x3f_1273_);
lean_dec(v_a_1272_);
if (lean_obj_tag(v_orderedRingInst_x3f_1273_) == 0)
{
lean_object* v___x_1274_; 
lean_dec_ref(v_arg_1101_);
v___x_1274_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; 
lean_dec_ref_known(v_orderedRingInst_x3f_1273_, 1);
v___x_1275_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_1101_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref_known(v___x_1275_, 1);
v___x_1276_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1276_;
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_e_1082_);
v_a_1277_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1275_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1275_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_e_1082_);
v_a_1285_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1271_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1271_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
else
{
lean_object* v___x_1293_; 
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_arg_1105_);
v___x_1293_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1304_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1294_, v_arg_1101_);
lean_dec_ref(v_arg_1101_);
lean_dec(v_a_1294_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_del_object(v___x_1296_);
v___x_1299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_1083_, v_e_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec_ref(v_e_1082_);
v___x_1300_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0));
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1300_);
v___x_1302_ = v___x_1296_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_e_1082_);
v_a_1305_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1293_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1293_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_e_1082_);
v_a_1313_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1096_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1096_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f___boxed(lean_object* v_e_1321_, lean_object* v_skipVar_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
uint8_t v_skipVar_boxed_1335_; lean_object* v_res_1336_; 
v_skipVar_boxed_1335_ = lean_unbox(v_skipVar_1322_);
v_res_1336_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_e_1321_, v_skipVar_boxed_1335_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec(v_a_1323_);
return v_res_1336_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
