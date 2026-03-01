// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Search
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.SearchM import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr import Lean.Meta.Tactic.Grind.Arith.Linear.Proof
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
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`grind linarith` internal error, structure is not an ordered module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind linarith` internal error, structure is not an ordered int module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`grind linarith` internal error, unexpected"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1_value;
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "`grind linarith` internal error, assigning variable out of order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assign"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 219, 209, 154, 141, 10, 194, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10_value;
lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__0(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
uint8_t l_Rat_blt(lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inDiseqValues___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0;
lean_object* l_Rat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0_spec__0(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_leAvoiding(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_leAvoiding___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "conflict"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 96, 199, 219, 74, 81, 53, 61)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Rat_floor(lean_object*);
lean_object* l_Rat_ceil(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findInt_x3f(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 40, 205, 216, 38, 159, 186, 145)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", reusing "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0;
lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", diseqs: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "v: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", upper: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ", lower, upper: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ", **ignore diseq**, diseqs: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", lower: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "backtrack"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 181, 179, 222, 180, 216, 89, 61)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "skipping "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`grind linarith` internal cases, cases stack is empty"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__5;
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Meta.Tactic.Grind.Arith.Linear.Search"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Search.0.Lean.Meta.Grind.Arith.Linear.findCase"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "resolved diseq split: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "backtracking "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dec vars: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "resolve conflict, decision stack: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_toExprProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_collectDecVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "`grind` internal error, eliminated variable must have equation associated with it"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "next var: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "found assignment"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__5;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "main loop"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__6_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_check___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_check___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_check___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_check___lam__0___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_check___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_check___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_25; 
x_14 = lean_ctor_get(x_13, 0);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
x_15 = x_13;
x_16 = x_25;
goto block_24;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 21);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_del_object(x_15);
x_22 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1);
x_23 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_22, x_8, x_9, x_10, x_11);
return x_23;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
x_26 = lean_ctor_get(x_13, 0);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
x_27 = x_13;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0);
x_16 = lean_int_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_38; 
x_20 = lean_ctor_get(x_19, 0);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
x_21 = x_19;
x_22 = x_38;
goto block_37;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; uint8_t x_34; 
x_23 = lean_ctor_get(x_20, 30);
lean_inc_ref(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_18, 23);
lean_inc_ref(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_23, 2);
x_26 = l_Lean_mkIntLit(x_1);
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_nat_dec_lt(x_2, x_25);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_23);
x_35 = l_outOfBounds___redArg(x_33);
x_27 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_PersistentArray_get_x21___redArg(x_33, x_23, x_2);
x_27 = x_36;
goto block_32;
}
block_32:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_mkAppB(x_24, x_26, x_27);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_28);
x_29 = x_21;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_18);
x_39 = lean_ctor_get(x_19, 0);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
x_40 = x_19;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
x_47 = lean_ctor_get(x_17, 0);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
x_48 = x_17;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_17);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_72; 
x_56 = lean_ctor_get(x_55, 0);
x_72 = !lean_is_exclusive(x_55);
if (x_72 == 0)
{
x_57 = x_55;
x_58 = x_72;
goto block_71;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_56, 30);
lean_inc_ref(x_59);
lean_dec(x_56);
x_60 = lean_ctor_get(x_59, 2);
x_61 = l_Lean_instInhabitedExpr;
x_62 = lean_nat_dec_lt(x_2, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_59);
x_63 = l_outOfBounds___redArg(x_61);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_63);
x_64 = x_57;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_PersistentArray_get_x21___redArg(x_61, x_59, x_2);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_67);
x_68 = x_57;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_73 = lean_ctor_get(x_55, 0);
x_80 = !lean_is_exclusive(x_55);
if (x_80 == 0)
{
x_74 = x_55;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_55);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_20, 22);
lean_inc_ref(x_23);
lean_dec(x_20);
x_24 = l_Lean_mkAppB(x_23, x_2, x_22);
x_1 = x_18;
x_2 = x_24;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec_ref(x_2);
return x_21;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_2);
x_26 = lean_ctor_get(x_19, 0);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
x_27 = x_19;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_14, 0);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
x_16 = x_14;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 17);
lean_inc_ref(x_18);
lean_dec(x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_24 = lean_ctor_get(x_14, 0);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
x_25 = x_14;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(x_32, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6(x_34, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_37;
}
else
{
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_25; 
x_14 = lean_ctor_get(x_13, 0);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
x_15 = x_13;
x_16 = x_25;
goto block_24;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 20);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_del_object(x_15);
x_22 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1);
x_23 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_22, x_8, x_9, x_10, x_11);
return x_23;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
x_26 = lean_ctor_get(x_13, 0);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
x_27 = x_13;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_2 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_29; 
x_20 = lean_ctor_get(x_19, 0);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
x_21 = x_19;
x_22 = x_29;
goto block_28;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 18);
lean_inc_ref(x_23);
lean_dec(x_20);
x_24 = l_Lean_mkAppB(x_16, x_18, x_23);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_24);
x_25 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_16);
x_30 = lean_ctor_get(x_19, 0);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
x_31 = x_19;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
lean_dec(x_16);
return x_17;
}
}
else
{
return x_15;
}
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_52; 
x_43 = lean_ctor_get(x_42, 0);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
x_44 = x_42;
x_45 = x_52;
goto block_51;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 18);
lean_inc_ref(x_46);
lean_dec(x_43);
x_47 = l_Lean_mkAppB(x_39, x_41, x_46);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_47);
x_48 = x_44;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_41);
lean_dec(x_39);
x_53 = lean_ctor_get(x_42, 0);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
x_54 = x_42;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_42);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_dec(x_39);
return x_40;
}
}
else
{
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1);
x_17 = l_Lean_MessageData_ofExpr(x_15);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_19, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_22 = x_14;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_31; 
x_16 = lean_ctor_get(x_15, 0);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
x_17 = x_15;
x_18 = x_31;
goto block_30;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 3);
lean_inc(x_20);
lean_dec(x_16);
x_21 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1));
x_22 = l_Lean_Level_succ___override(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_mkConst(x_21, x_24);
x_26 = l_Lean_mkApp3(x_25, x_19, x_1, x_2);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_26);
x_27 = x_17;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_15, 0);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
x_33 = x_15;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 18);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(x_16, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
x_22 = x_20;
x_23 = x_29;
goto block_28;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_mkNot(x_21);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_24);
x_25 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
return x_20;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_16);
x_30 = lean_ctor_get(x_17, 0);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
x_31 = x_17;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1);
x_17 = l_Lean_MessageData_ofExpr(x_15);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_19, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_22 = x_14;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 18);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(x_16, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
x_22 = x_17;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1);
x_17 = l_Lean_MessageData_ofExpr(x_15);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_19, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_22 = x_14;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_28; 
x_15 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_16 = x_14;
x_17 = x_28;
goto block_27;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 35);
lean_inc_ref(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_nat_dec_eq(x_1, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_del_object(x_16);
x_21 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1);
x_22 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_21, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_29 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_30 = x_14;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(x_1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_81; 
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5));
x_16 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(x_15, x_12);
x_17 = lean_ctor_get(x_16, 0);
x_81 = !lean_is_exclusive(x_16);
if (x_81 == 0)
{
x_18 = x_16;
x_19 = x_81;
goto block_80;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_81;
goto block_80;
}
block_80:
{
uint8_t x_20; 
x_20 = lean_unbox(x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_2);
x_21 = lean_box(0);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_21);
x_22 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; 
lean_del_object(x_18);
x_25 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_71; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
x_29 = x_2;
x_30 = x_71;
goto block_70;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_26);
x_32 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7);
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_32);
lean_ctor_set(x_29, 0, x_31);
x_33 = x_29;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_31);
lean_ctor_set(x_69, 1, x_32);
x_33 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_34; lean_object* x_40; lean_object* x_46; uint8_t x_47; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_dec_eq(x_28, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_49 = lean_int_dec_lt(x_27, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_nat_abs(x_27);
lean_dec(x_27);
x_51 = l_Nat_reprFast(x_50);
x_40 = x_51;
goto block_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_nat_abs(x_27);
lean_dec(x_27);
x_53 = lean_nat_sub(x_52, x_46);
lean_dec(x_52);
x_54 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_55 = lean_nat_add(x_53, x_46);
lean_dec(x_53);
x_56 = l_Nat_reprFast(x_55);
x_57 = lean_string_append(x_54, x_56);
lean_dec_ref(x_56);
x_40 = x_57;
goto block_45;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_28);
x_58 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_59 = lean_int_dec_lt(x_27, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_nat_abs(x_27);
lean_dec(x_27);
x_61 = l_Nat_reprFast(x_60);
x_34 = x_61;
goto block_39;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_nat_abs(x_27);
lean_dec(x_27);
x_63 = lean_nat_sub(x_62, x_46);
lean_dec(x_62);
x_64 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_65 = lean_nat_add(x_63, x_46);
lean_dec(x_63);
x_66 = l_Nat_reprFast(x_65);
x_67 = lean_string_append(x_64, x_66);
lean_dec_ref(x_66);
x_34 = x_67;
goto block_39;
}
}
block_39:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_15, x_37, x_10, x_11, x_12, x_13);
return x_38;
}
block_45:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_42 = lean_string_append(x_40, x_41);
x_43 = l_Nat_reprFast(x_28);
x_44 = lean_string_append(x_42, x_43);
lean_dec_ref(x_43);
x_34 = x_44;
goto block_39;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec_ref(x_2);
x_72 = lean_ctor_get(x_25, 0);
x_79 = !lean_is_exclusive(x_25);
if (x_79 == 0)
{
x_73 = x_25;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_25);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_1, x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_75; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_75 = !lean_is_exclusive(x_3);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_3, 7);
lean_dec(x_76);
x_77 = lean_ctor_get(x_3, 6);
lean_dec(x_77);
x_78 = lean_ctor_get(x_3, 5);
lean_dec(x_78);
x_79 = lean_ctor_get(x_3, 4);
lean_dec(x_79);
x_80 = lean_ctor_get(x_3, 3);
lean_dec(x_80);
x_81 = lean_ctor_get(x_3, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_3, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_3, 0);
lean_dec(x_83);
x_14 = x_3;
x_15 = x_75;
goto block_74;
}
else
{
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_73; 
x_16 = lean_array_fget(x_4, x_1);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 2);
x_20 = lean_ctor_get(x_16, 3);
x_21 = lean_ctor_get(x_16, 4);
x_22 = lean_ctor_get(x_16, 5);
x_23 = lean_ctor_get(x_16, 6);
x_24 = lean_ctor_get(x_16, 7);
x_25 = lean_ctor_get(x_16, 8);
x_26 = lean_ctor_get(x_16, 9);
x_27 = lean_ctor_get(x_16, 10);
x_28 = lean_ctor_get(x_16, 11);
x_29 = lean_ctor_get(x_16, 12);
x_30 = lean_ctor_get(x_16, 13);
x_31 = lean_ctor_get(x_16, 14);
x_32 = lean_ctor_get(x_16, 15);
x_33 = lean_ctor_get(x_16, 16);
x_34 = lean_ctor_get(x_16, 17);
x_35 = lean_ctor_get(x_16, 18);
x_36 = lean_ctor_get(x_16, 19);
x_37 = lean_ctor_get(x_16, 20);
x_38 = lean_ctor_get(x_16, 21);
x_39 = lean_ctor_get(x_16, 22);
x_40 = lean_ctor_get(x_16, 23);
x_41 = lean_ctor_get(x_16, 24);
x_42 = lean_ctor_get(x_16, 25);
x_43 = lean_ctor_get(x_16, 26);
x_44 = lean_ctor_get(x_16, 27);
x_45 = lean_ctor_get(x_16, 28);
x_46 = lean_ctor_get(x_16, 29);
x_47 = lean_ctor_get(x_16, 30);
x_48 = lean_ctor_get(x_16, 31);
x_49 = lean_ctor_get(x_16, 32);
x_50 = lean_ctor_get(x_16, 33);
x_51 = lean_ctor_get(x_16, 34);
x_52 = lean_ctor_get(x_16, 35);
x_53 = lean_ctor_get_uint8(x_16, sizeof(void*)*42);
x_54 = lean_ctor_get(x_16, 36);
x_55 = lean_ctor_get(x_16, 37);
x_56 = lean_ctor_get(x_16, 38);
x_57 = lean_ctor_get(x_16, 39);
x_58 = lean_ctor_get(x_16, 40);
x_59 = lean_ctor_get(x_16, 41);
x_73 = !lean_is_exclusive(x_16);
if (x_73 == 0)
{
x_60 = x_16;
x_61 = x_73;
goto block_72;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_16);
x_60 = lean_box(0);
x_61 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_box(0);
x_63 = lean_array_fset(x_4, x_1, x_62);
x_64 = l_Lean_PersistentArray_push___redArg(x_52, x_2);
if (x_61 == 0)
{
lean_ctor_set(x_60, 35, x_64);
x_65 = x_60;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_71, 0, x_17);
lean_ctor_set(x_71, 1, x_18);
lean_ctor_set(x_71, 2, x_19);
lean_ctor_set(x_71, 3, x_20);
lean_ctor_set(x_71, 4, x_21);
lean_ctor_set(x_71, 5, x_22);
lean_ctor_set(x_71, 6, x_23);
lean_ctor_set(x_71, 7, x_24);
lean_ctor_set(x_71, 8, x_25);
lean_ctor_set(x_71, 9, x_26);
lean_ctor_set(x_71, 10, x_27);
lean_ctor_set(x_71, 11, x_28);
lean_ctor_set(x_71, 12, x_29);
lean_ctor_set(x_71, 13, x_30);
lean_ctor_set(x_71, 14, x_31);
lean_ctor_set(x_71, 15, x_32);
lean_ctor_set(x_71, 16, x_33);
lean_ctor_set(x_71, 17, x_34);
lean_ctor_set(x_71, 18, x_35);
lean_ctor_set(x_71, 19, x_36);
lean_ctor_set(x_71, 20, x_37);
lean_ctor_set(x_71, 21, x_38);
lean_ctor_set(x_71, 22, x_39);
lean_ctor_set(x_71, 23, x_40);
lean_ctor_set(x_71, 24, x_41);
lean_ctor_set(x_71, 25, x_42);
lean_ctor_set(x_71, 26, x_43);
lean_ctor_set(x_71, 27, x_44);
lean_ctor_set(x_71, 28, x_45);
lean_ctor_set(x_71, 29, x_46);
lean_ctor_set(x_71, 30, x_47);
lean_ctor_set(x_71, 31, x_48);
lean_ctor_set(x_71, 32, x_49);
lean_ctor_set(x_71, 33, x_50);
lean_ctor_set(x_71, 34, x_51);
lean_ctor_set(x_71, 35, x_64);
lean_ctor_set(x_71, 36, x_54);
lean_ctor_set(x_71, 37, x_55);
lean_ctor_set(x_71, 38, x_56);
lean_ctor_set(x_71, 39, x_57);
lean_ctor_set(x_71, 40, x_58);
lean_ctor_set(x_71, 41, x_59);
lean_ctor_set_uint8(x_71, sizeof(void*)*42, x_53);
x_65 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_array_fset(x_63, x_1, x_65);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_66);
x_67 = x_14;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_5);
lean_ctor_set(x_69, 2, x_6);
lean_ctor_set(x_69, 3, x_7);
lean_ctor_set(x_69, 4, x_8);
lean_ctor_set(x_69, 5, x_9);
lean_ctor_set(x_69, 6, x_10);
lean_ctor_set(x_69, 7, x_11);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
lean_inc_ref(x_2);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_16);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0___boxed), 3, 2);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_2);
x_18 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_19 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_18, x_17, x_4);
return x_19;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Rat_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_91; 
x_19 = lean_ctor_get(x_4, 1);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_20 = x_4;
x_21 = x_91;
goto block_90;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; 
lean_inc(x_35);
x_42 = l_Rat_ofInt(x_35);
x_43 = l_Rat_neg(x_42);
x_44 = l_Rat_div(x_39, x_43);
lean_dec(x_39);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_44);
lean_inc(x_53);
x_55 = l_Rat_blt(x_53, x_44);
if (x_55 == 0)
{
uint8_t x_59; 
x_59 = l_instDecidableEqRat_decEq(x_44, x_53);
if (x_59 == 0)
{
x_56 = x_59;
goto block_58;
}
else
{
x_56 = x_24;
goto block_58;
}
}
else
{
x_50 = x_55;
goto block_51;
}
block_58:
{
if (x_56 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
if (x_57 == 0)
{
lean_dec_ref(x_19);
goto block_49;
}
else
{
x_50 = x_55;
goto block_51;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_del_object(x_40);
lean_dec(x_19);
lean_inc(x_22);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_26 = x_61;
x_27 = lean_box(0);
goto block_34;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_45);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_26 = x_46;
x_27 = lean_box(0);
goto block_34;
}
}
block_51:
{
if (x_50 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_19);
goto block_49;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_38);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_20);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_del_object(x_20);
lean_dec(x_19);
x_73 = lean_ctor_get(x_37, 0);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
x_74 = x_37;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_20);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_25);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_4 = x_28;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_91; 
x_19 = lean_ctor_get(x_4, 1);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_20 = x_4;
x_21 = x_91;
goto block_90;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; 
lean_inc(x_35);
x_42 = l_Rat_ofInt(x_35);
x_43 = l_Rat_neg(x_42);
x_44 = l_Rat_div(x_39, x_43);
lean_dec(x_39);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_44);
lean_inc(x_53);
x_55 = l_Rat_blt(x_53, x_44);
if (x_55 == 0)
{
uint8_t x_59; 
x_59 = l_instDecidableEqRat_decEq(x_44, x_53);
if (x_59 == 0)
{
x_56 = x_59;
goto block_58;
}
else
{
x_56 = x_24;
goto block_58;
}
}
else
{
x_50 = x_55;
goto block_51;
}
block_58:
{
if (x_56 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
if (x_57 == 0)
{
lean_dec_ref(x_19);
goto block_49;
}
else
{
x_50 = x_55;
goto block_51;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_del_object(x_40);
lean_dec(x_19);
lean_inc(x_22);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_26 = x_61;
x_27 = lean_box(0);
goto block_34;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_45);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_26 = x_46;
x_27 = lean_box(0);
goto block_34;
}
}
block_51:
{
if (x_50 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_19);
goto block_49;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_38);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_20);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_del_object(x_20);
lean_dec(x_19);
x_73 = lean_ctor_get(x_37, 0);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
x_74 = x_37;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_20);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_25);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5(x_1, x_2, x_30, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_91; 
x_19 = lean_ctor_get(x_4, 1);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_20 = x_4;
x_21 = x_91;
goto block_90;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; 
lean_inc(x_35);
x_42 = l_Rat_ofInt(x_35);
x_43 = l_Rat_neg(x_42);
x_44 = l_Rat_div(x_39, x_43);
lean_dec(x_39);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_44);
lean_inc(x_53);
x_55 = l_Rat_blt(x_53, x_44);
if (x_55 == 0)
{
uint8_t x_59; 
x_59 = l_instDecidableEqRat_decEq(x_44, x_53);
if (x_59 == 0)
{
x_56 = x_59;
goto block_58;
}
else
{
x_56 = x_24;
goto block_58;
}
}
else
{
x_50 = x_55;
goto block_51;
}
block_58:
{
if (x_56 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
if (x_57 == 0)
{
lean_dec_ref(x_19);
goto block_49;
}
else
{
x_50 = x_55;
goto block_51;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_del_object(x_40);
lean_dec(x_19);
lean_inc(x_22);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_26 = x_61;
x_27 = lean_box(0);
goto block_34;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_45);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_26 = x_46;
x_27 = lean_box(0);
goto block_34;
}
}
block_51:
{
if (x_50 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_19);
goto block_49;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_38);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_20);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_del_object(x_20);
lean_dec(x_19);
x_73 = lean_ctor_get(x_37, 0);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
x_74 = x_37;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_20);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_25);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_4 = x_28;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_91; 
x_19 = lean_ctor_get(x_4, 1);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_20 = x_4;
x_21 = x_91;
goto block_90;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; 
lean_inc(x_35);
x_42 = l_Rat_ofInt(x_35);
x_43 = l_Rat_neg(x_42);
x_44 = l_Rat_div(x_39, x_43);
lean_dec(x_39);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_44);
lean_inc(x_53);
x_55 = l_Rat_blt(x_53, x_44);
if (x_55 == 0)
{
uint8_t x_59; 
x_59 = l_instDecidableEqRat_decEq(x_44, x_53);
if (x_59 == 0)
{
x_56 = x_59;
goto block_58;
}
else
{
x_56 = x_24;
goto block_58;
}
}
else
{
x_50 = x_55;
goto block_51;
}
block_58:
{
if (x_56 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
if (x_57 == 0)
{
lean_dec_ref(x_19);
goto block_49;
}
else
{
x_50 = x_55;
goto block_51;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_del_object(x_40);
lean_dec(x_19);
lean_inc(x_22);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_26 = x_61;
x_27 = lean_box(0);
goto block_34;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_45);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_26 = x_46;
x_27 = lean_box(0);
goto block_34;
}
}
block_51:
{
if (x_50 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_19);
goto block_49;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_38);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_20);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_del_object(x_20);
lean_dec(x_19);
x_73 = lean_ctor_get(x_37, 0);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
x_74 = x_37;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_20);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_25);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4(x_1, x_2, x_30, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_50; 
x_16 = lean_ctor_get(x_2, 0);
x_50 = !lean_is_exclusive(x_2);
if (x_50 == 0)
{
x_17 = x_2;
x_18 = x_50;
goto block_49;
}
else
{
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_array_size(x_16);
x_22 = 0;
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(x_1, x_16, x_21, x_22, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_40; 
x_24 = lean_ctor_get(x_23, 0);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
x_25 = x_23;
x_26 = x_40;
goto block_39;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_28);
x_29 = x_17;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_29);
x_30 = x_25;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_27);
lean_dec(x_24);
lean_del_object(x_17);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec_ref(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_35);
x_36 = x_25;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_del_object(x_17);
x_41 = lean_ctor_get(x_23, 0);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
x_42 = x_23;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_85; 
x_51 = lean_ctor_get(x_2, 0);
x_85 = !lean_is_exclusive(x_2);
if (x_85 == 0)
{
x_52 = x_2;
x_53 = x_85;
goto block_84;
}
else
{
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
x_56 = lean_array_size(x_51);
x_57 = 0;
x_58 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(x_51, x_56, x_57, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_75; 
x_59 = lean_ctor_get(x_58, 0);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
x_60 = x_58;
x_61 = x_75;
goto block_74;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 0);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_63);
x_64 = x_52;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_64);
x_65 = x_60;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_inc_ref(x_62);
lean_dec(x_59);
lean_del_object(x_52);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
lean_dec_ref(x_62);
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_70);
x_71 = x_60;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_del_object(x_52);
x_76 = lean_ctor_get(x_58, 0);
x_83 = !lean_is_exclusive(x_58);
if (x_83 == 0)
{
x_77 = x_58;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_58);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_54; 
x_20 = lean_ctor_get(x_5, 1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_5, 0);
lean_dec(x_55);
x_21 = x_5;
x_22 = x_54;
goto block_53;
}
else
{
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_20);
lean_inc(x_23);
x_24 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(x_1, x_23, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_44; 
x_25 = lean_ctor_get(x_24, 0);
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
x_26 = x_24;
x_27 = x_44;
goto block_43;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_44;
goto block_43;
}
block_43:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_28);
x_29 = x_21;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_20);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_del_object(x_26);
lean_dec(x_20);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec_ref(x_25);
x_36 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_35);
lean_ctor_set(x_21, 0, x_36);
x_37 = x_21;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_35);
x_37 = x_42;
goto block_41;
}
block_41:
{
size_t x_38; size_t x_39; 
x_38 = 1;
x_39 = lean_usize_add(x_4, x_38);
x_4 = x_39;
x_5 = x_37;
goto _start;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_21);
lean_dec(x_20);
x_45 = lean_ctor_get(x_24, 0);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
x_46 = x_24;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(x_1, x_2, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
lean_inc(x_2);
x_17 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(x_2, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_54; 
x_18 = lean_ctor_get(x_17, 0);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
x_19 = x_17;
x_20 = x_54;
goto block_53;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_54;
goto block_53;
}
block_53:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_16);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
lean_del_object(x_19);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec_ref(x_18);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_array_size(x_16);
x_29 = 0;
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(x_16, x_28, x_29, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_44; 
x_31 = lean_ctor_get(x_30, 0);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
x_32 = x_30;
x_33 = x_44;
goto block_43;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_inc_ref(x_34);
lean_dec(x_31);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec_ref(x_34);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_39);
x_40 = x_32;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
x_45 = lean_ctor_get(x_30, 0);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
x_46 = x_30;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_16);
x_55 = lean_ctor_get(x_17, 0);
x_62 = !lean_is_exclusive(x_17);
if (x_62 == 0)
{
x_56 = x_17;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_17);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 32);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 2);
x_18 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0, &l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0);
x_19 = lean_box(0);
x_20 = lean_nat_dec_lt(x_1, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_16);
x_21 = l_outOfBounds___redArg(x_18);
x_22 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(x_21, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_PersistentArray_get_x21___redArg(x_18, x_16, x_1);
x_24 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_14, 0);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
x_26 = x_14;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_91; 
x_19 = lean_ctor_get(x_4, 1);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_20 = x_4;
x_21 = x_91;
goto block_90;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; 
x_42 = l_Rat_neg(x_39);
lean_inc(x_35);
x_43 = l_Rat_ofInt(x_35);
x_44 = l_Rat_div(x_42, x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_inc_ref(x_44);
x_55 = l_Rat_blt(x_44, x_53);
if (x_55 == 0)
{
uint8_t x_59; 
x_59 = l_instDecidableEqRat_decEq(x_44, x_53);
if (x_59 == 0)
{
x_56 = x_59;
goto block_58;
}
else
{
x_56 = x_24;
goto block_58;
}
}
else
{
x_50 = x_55;
goto block_51;
}
block_58:
{
if (x_56 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
if (x_57 == 0)
{
lean_dec_ref(x_19);
goto block_49;
}
else
{
x_50 = x_55;
goto block_51;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_del_object(x_40);
lean_dec(x_19);
lean_inc(x_22);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_26 = x_61;
x_27 = lean_box(0);
goto block_34;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_45);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_26 = x_46;
x_27 = lean_box(0);
goto block_34;
}
}
block_51:
{
if (x_50 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_19);
goto block_49;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_38);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_20);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_del_object(x_20);
lean_dec(x_19);
x_73 = lean_ctor_get(x_37, 0);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
x_74 = x_37;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_20);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_25);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_4 = x_28;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_91; 
x_19 = lean_ctor_get(x_4, 1);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_20 = x_4;
x_21 = x_91;
goto block_90;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; 
x_42 = l_Rat_neg(x_39);
lean_inc(x_35);
x_43 = l_Rat_ofInt(x_35);
x_44 = l_Rat_div(x_42, x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_inc_ref(x_44);
x_55 = l_Rat_blt(x_44, x_53);
if (x_55 == 0)
{
uint8_t x_59; 
x_59 = l_instDecidableEqRat_decEq(x_44, x_53);
if (x_59 == 0)
{
x_56 = x_59;
goto block_58;
}
else
{
x_56 = x_24;
goto block_58;
}
}
else
{
x_50 = x_55;
goto block_51;
}
block_58:
{
if (x_56 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
if (x_57 == 0)
{
lean_dec_ref(x_19);
goto block_49;
}
else
{
x_50 = x_55;
goto block_51;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_del_object(x_40);
lean_dec(x_19);
lean_inc(x_22);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_26 = x_61;
x_27 = lean_box(0);
goto block_34;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_45);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_26 = x_46;
x_27 = lean_box(0);
goto block_34;
}
}
block_51:
{
if (x_50 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_19);
goto block_49;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_38);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_20);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_del_object(x_20);
lean_dec(x_19);
x_73 = lean_ctor_get(x_37, 0);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
x_74 = x_37;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_20);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_25);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_30, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_50; 
x_16 = lean_ctor_get(x_2, 0);
x_50 = !lean_is_exclusive(x_2);
if (x_50 == 0)
{
x_17 = x_2;
x_18 = x_50;
goto block_49;
}
else
{
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_array_size(x_16);
x_22 = 0;
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(x_1, x_16, x_21, x_22, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_40; 
x_24 = lean_ctor_get(x_23, 0);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
x_25 = x_23;
x_26 = x_40;
goto block_39;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_28);
x_29 = x_17;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_29);
x_30 = x_25;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_27);
lean_dec(x_24);
lean_del_object(x_17);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec_ref(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_35);
x_36 = x_25;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_del_object(x_17);
x_41 = lean_ctor_get(x_23, 0);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
x_42 = x_23;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_85; 
x_51 = lean_ctor_get(x_2, 0);
x_85 = !lean_is_exclusive(x_2);
if (x_85 == 0)
{
x_52 = x_2;
x_53 = x_85;
goto block_84;
}
else
{
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
x_56 = lean_array_size(x_51);
x_57 = 0;
x_58 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(x_51, x_56, x_57, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_75; 
x_59 = lean_ctor_get(x_58, 0);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
x_60 = x_58;
x_61 = x_75;
goto block_74;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 0);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_63);
x_64 = x_52;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_64);
x_65 = x_60;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_inc_ref(x_62);
lean_dec(x_59);
lean_del_object(x_52);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
lean_dec_ref(x_62);
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_70);
x_71 = x_60;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_del_object(x_52);
x_76 = lean_ctor_get(x_58, 0);
x_83 = !lean_is_exclusive(x_58);
if (x_83 == 0)
{
x_77 = x_58;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_58);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_54; 
x_20 = lean_ctor_get(x_5, 1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_5, 0);
lean_dec(x_55);
x_21 = x_5;
x_22 = x_54;
goto block_53;
}
else
{
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_20);
lean_inc(x_23);
x_24 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(x_1, x_23, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_44; 
x_25 = lean_ctor_get(x_24, 0);
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
x_26 = x_24;
x_27 = x_44;
goto block_43;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_44;
goto block_43;
}
block_43:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_28);
x_29 = x_21;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_20);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_del_object(x_26);
lean_dec(x_20);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec_ref(x_25);
x_36 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_35);
lean_ctor_set(x_21, 0, x_36);
x_37 = x_21;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_35);
x_37 = x_42;
goto block_41;
}
block_41:
{
size_t x_38; size_t x_39; 
x_38 = 1;
x_39 = lean_usize_add(x_4, x_38);
x_4 = x_39;
x_5 = x_37;
goto _start;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_21);
lean_dec(x_20);
x_45 = lean_ctor_get(x_24, 0);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
x_46 = x_24;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_91; 
x_19 = lean_ctor_get(x_4, 1);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_20 = x_4;
x_21 = x_91;
goto block_90;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; 
x_42 = l_Rat_neg(x_39);
lean_inc(x_35);
x_43 = l_Rat_ofInt(x_35);
x_44 = l_Rat_div(x_42, x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_inc_ref(x_44);
x_55 = l_Rat_blt(x_44, x_53);
if (x_55 == 0)
{
uint8_t x_59; 
x_59 = l_instDecidableEqRat_decEq(x_44, x_53);
if (x_59 == 0)
{
x_56 = x_59;
goto block_58;
}
else
{
x_56 = x_24;
goto block_58;
}
}
else
{
x_50 = x_55;
goto block_51;
}
block_58:
{
if (x_56 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
if (x_57 == 0)
{
lean_dec_ref(x_19);
goto block_49;
}
else
{
x_50 = x_55;
goto block_51;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_del_object(x_40);
lean_dec(x_19);
lean_inc(x_22);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_26 = x_61;
x_27 = lean_box(0);
goto block_34;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_45);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_26 = x_46;
x_27 = lean_box(0);
goto block_34;
}
}
block_51:
{
if (x_50 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_19);
goto block_49;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_38);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_20);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_del_object(x_20);
lean_dec(x_19);
x_73 = lean_ctor_get(x_37, 0);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
x_74 = x_37;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_20);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_25);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_4 = x_28;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_91; 
x_19 = lean_ctor_get(x_4, 1);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_20 = x_4;
x_21 = x_91;
goto block_90;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; 
x_42 = l_Rat_neg(x_39);
lean_inc(x_35);
x_43 = l_Rat_ofInt(x_35);
x_44 = l_Rat_div(x_42, x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_inc_ref(x_44);
x_55 = l_Rat_blt(x_44, x_53);
if (x_55 == 0)
{
uint8_t x_59; 
x_59 = l_instDecidableEqRat_decEq(x_44, x_53);
if (x_59 == 0)
{
x_56 = x_59;
goto block_58;
}
else
{
x_56 = x_24;
goto block_58;
}
}
else
{
x_50 = x_55;
goto block_51;
}
block_58:
{
if (x_56 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
if (x_57 == 0)
{
lean_dec_ref(x_19);
goto block_49;
}
else
{
x_50 = x_55;
goto block_51;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_del_object(x_40);
lean_dec(x_19);
lean_inc(x_22);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_26 = x_61;
x_27 = lean_box(0);
goto block_34;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_45);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_26 = x_46;
x_27 = lean_box(0);
goto block_34;
}
}
block_51:
{
if (x_50 == 0)
{
lean_dec_ref(x_44);
lean_del_object(x_40);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_19);
goto block_49;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_38);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_20);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_del_object(x_20);
lean_dec(x_19);
x_73 = lean_ctor_get(x_37, 0);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
x_74 = x_37;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_26 = x_19;
x_27 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_20);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_25);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4(x_1, x_2, x_30, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
lean_inc(x_2);
x_17 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(x_2, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_54; 
x_18 = lean_ctor_get(x_17, 0);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
x_19 = x_17;
x_20 = x_54;
goto block_53;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_54;
goto block_53;
}
block_53:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_16);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
lean_del_object(x_19);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec_ref(x_18);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_array_size(x_16);
x_29 = 0;
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(x_16, x_28, x_29, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_44; 
x_31 = lean_ctor_get(x_30, 0);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
x_32 = x_30;
x_33 = x_44;
goto block_43;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_inc_ref(x_34);
lean_dec(x_31);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec_ref(x_34);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_39);
x_40 = x_32;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
x_45 = lean_ctor_get(x_30, 0);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
x_46 = x_30;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_16);
x_55 = lean_ctor_get(x_17, 0);
x_62 = !lean_is_exclusive(x_17);
if (x_62 == 0)
{
x_56 = x_17;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_17);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 33);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 2);
x_18 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0, &l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0);
x_19 = lean_box(0);
x_20 = lean_nat_dec_lt(x_1, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_16);
x_21 = l_outOfBounds___redArg(x_18);
x_22 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(x_21, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_PersistentArray_get_x21___redArg(x_18, x_16, x_1);
x_24 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_14, 0);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
x_26 = x_14;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_71; 
x_19 = lean_ctor_get(x_4, 1);
x_71 = !lean_is_exclusive(x_4);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_4, 0);
lean_dec(x_72);
x_20 = x_4;
x_21 = x_71;
goto block_70;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 2);
lean_inc(x_35);
x_36 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Rat_neg(x_38);
lean_inc(x_34);
x_40 = l_Rat_ofInt(x_34);
x_41 = l_Rat_div(x_39, x_40);
lean_dec_ref(x_39);
lean_inc(x_22);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_22);
x_43 = lean_array_push(x_19, x_42);
x_25 = x_43;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_44; 
lean_dec(x_37);
x_44 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
x_25 = x_19;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_20);
lean_dec(x_19);
x_45 = lean_ctor_get(x_44, 0);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
x_46 = x_44;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_del_object(x_20);
lean_dec(x_19);
x_53 = lean_ctor_get(x_36, 0);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
x_54 = x_36;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_25 = x_19;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_del_object(x_20);
lean_dec(x_19);
x_62 = lean_ctor_get(x_61, 0);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
x_63 = x_61;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
block_33:
{
lean_object* x_27; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_27 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
x_27 = x_32;
goto block_31;
}
block_31:
{
size_t x_28; size_t x_29; 
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_3 = x_29;
x_4 = x_27;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_71; 
x_19 = lean_ctor_get(x_4, 1);
x_71 = !lean_is_exclusive(x_4);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_4, 0);
lean_dec(x_72);
x_20 = x_4;
x_21 = x_71;
goto block_70;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 2);
lean_inc(x_35);
x_36 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Rat_neg(x_38);
lean_inc(x_34);
x_40 = l_Rat_ofInt(x_34);
x_41 = l_Rat_div(x_39, x_40);
lean_dec_ref(x_39);
lean_inc(x_22);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_22);
x_43 = lean_array_push(x_19, x_42);
x_25 = x_43;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_44; 
lean_dec(x_37);
x_44 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
x_25 = x_19;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_20);
lean_dec(x_19);
x_45 = lean_ctor_get(x_44, 0);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
x_46 = x_44;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_del_object(x_20);
lean_dec(x_19);
x_53 = lean_ctor_get(x_36, 0);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
x_54 = x_36;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_25 = x_19;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_del_object(x_20);
lean_dec(x_19);
x_62 = lean_ctor_get(x_61, 0);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
x_63 = x_61;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
block_33:
{
lean_object* x_27; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_27 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
x_27 = x_32;
goto block_31;
}
block_31:
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4(x_1, x_2, x_29, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_71; 
x_19 = lean_ctor_get(x_4, 1);
x_71 = !lean_is_exclusive(x_4);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_4, 0);
lean_dec(x_72);
x_20 = x_4;
x_21 = x_71;
goto block_70;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 2);
lean_inc(x_35);
x_36 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Rat_neg(x_38);
lean_inc(x_34);
x_40 = l_Rat_ofInt(x_34);
x_41 = l_Rat_div(x_39, x_40);
lean_dec_ref(x_39);
lean_inc(x_22);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_22);
x_43 = lean_array_push(x_19, x_42);
x_25 = x_43;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_44; 
lean_dec(x_37);
x_44 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
x_25 = x_19;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_20);
lean_dec(x_19);
x_45 = lean_ctor_get(x_44, 0);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
x_46 = x_44;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_del_object(x_20);
lean_dec(x_19);
x_53 = lean_ctor_get(x_36, 0);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
x_54 = x_36;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_25 = x_19;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_del_object(x_20);
lean_dec(x_19);
x_62 = lean_ctor_get(x_61, 0);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
x_63 = x_61;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
block_33:
{
lean_object* x_27; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_27 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
x_27 = x_32;
goto block_31;
}
block_31:
{
size_t x_28; size_t x_29; 
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_3 = x_29;
x_4 = x_27;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_71; 
x_19 = lean_ctor_get(x_4, 1);
x_71 = !lean_is_exclusive(x_4);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_4, 0);
lean_dec(x_72);
x_20 = x_4;
x_21 = x_71;
goto block_70;
}
else
{
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_box(0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 2);
lean_inc(x_35);
x_36 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Rat_neg(x_38);
lean_inc(x_34);
x_40 = l_Rat_ofInt(x_34);
x_41 = l_Rat_div(x_39, x_40);
lean_dec_ref(x_39);
lean_inc(x_22);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_22);
x_43 = lean_array_push(x_19, x_42);
x_25 = x_43;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_44; 
lean_dec(x_37);
x_44 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
x_25 = x_19;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_20);
lean_dec(x_19);
x_45 = lean_ctor_get(x_44, 0);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
x_46 = x_44;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_del_object(x_20);
lean_dec(x_19);
x_53 = lean_ctor_get(x_36, 0);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
x_54 = x_36;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_25 = x_19;
x_26 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_del_object(x_20);
lean_dec(x_19);
x_62 = lean_ctor_get(x_61, 0);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
x_63 = x_61;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
block_33:
{
lean_object* x_27; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_27 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
x_27 = x_32;
goto block_31;
}
block_31:
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_29, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_50; 
x_16 = lean_ctor_get(x_2, 0);
x_50 = !lean_is_exclusive(x_2);
if (x_50 == 0)
{
x_17 = x_2;
x_18 = x_50;
goto block_49;
}
else
{
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_array_size(x_16);
x_22 = 0;
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(x_1, x_16, x_21, x_22, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_40; 
x_24 = lean_ctor_get(x_23, 0);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
x_25 = x_23;
x_26 = x_40;
goto block_39;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_28);
x_29 = x_17;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_29);
x_30 = x_25;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_27);
lean_dec(x_24);
lean_del_object(x_17);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec_ref(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_35);
x_36 = x_25;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_del_object(x_17);
x_41 = lean_ctor_get(x_23, 0);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
x_42 = x_23;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_85; 
x_51 = lean_ctor_get(x_2, 0);
x_85 = !lean_is_exclusive(x_2);
if (x_85 == 0)
{
x_52 = x_2;
x_53 = x_85;
goto block_84;
}
else
{
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
x_56 = lean_array_size(x_51);
x_57 = 0;
x_58 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(x_51, x_56, x_57, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_75; 
x_59 = lean_ctor_get(x_58, 0);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
x_60 = x_58;
x_61 = x_75;
goto block_74;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 0);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_63);
x_64 = x_52;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_64);
x_65 = x_60;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_inc_ref(x_62);
lean_dec(x_59);
lean_del_object(x_52);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
lean_dec_ref(x_62);
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_70);
x_71 = x_60;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_del_object(x_52);
x_76 = lean_ctor_get(x_58, 0);
x_83 = !lean_is_exclusive(x_58);
if (x_83 == 0)
{
x_77 = x_58;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_58);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_54; 
x_20 = lean_ctor_get(x_5, 1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_5, 0);
lean_dec(x_55);
x_21 = x_5;
x_22 = x_54;
goto block_53;
}
else
{
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_20);
lean_inc(x_23);
x_24 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(x_1, x_23, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_44; 
x_25 = lean_ctor_get(x_24, 0);
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
x_26 = x_24;
x_27 = x_44;
goto block_43;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_44;
goto block_43;
}
block_43:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_28);
x_29 = x_21;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_20);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_del_object(x_26);
lean_dec(x_20);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec_ref(x_25);
x_36 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_35);
lean_ctor_set(x_21, 0, x_36);
x_37 = x_21;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_35);
x_37 = x_42;
goto block_41;
}
block_41:
{
size_t x_38; size_t x_39; 
x_38 = 1;
x_39 = lean_usize_add(x_4, x_38);
x_4 = x_39;
x_5 = x_37;
goto _start;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_21);
lean_dec(x_20);
x_45 = lean_ctor_get(x_24, 0);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
x_46 = x_24;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(x_1, x_2, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_17 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(x_2, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_54; 
x_18 = lean_ctor_get(x_17, 0);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
x_19 = x_17;
x_20 = x_54;
goto block_53;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_54;
goto block_53;
}
block_53:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_16);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
lean_del_object(x_19);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec_ref(x_18);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_array_size(x_16);
x_29 = 0;
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(x_16, x_28, x_29, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_44; 
x_31 = lean_ctor_get(x_30, 0);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
x_32 = x_30;
x_33 = x_44;
goto block_43;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_inc_ref(x_34);
lean_dec(x_31);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec_ref(x_34);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_39);
x_40 = x_32;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
x_45 = lean_ctor_get(x_30, 0);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
x_46 = x_30;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_16);
x_55 = lean_ctor_get(x_17, 0);
x_62 = !lean_is_exclusive(x_17);
if (x_62 == 0)
{
x_56 = x_17;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_17);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 34);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 2);
x_18 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0, &l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0);
x_19 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0));
x_20 = lean_nat_dec_lt(x_1, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_16);
x_21 = l_outOfBounds___redArg(x_18);
x_22 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(x_21, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_PersistentArray_get_x21___redArg(x_18, x_16, x_1);
x_24 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_14, 0);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
x_26 = x_14;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getDiseqValues(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec_ref(x_5);
x_7 = lean_array_uget_borrowed(x_2, x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_box(0);
x_10 = l_instDecidableEqRat_decEq(x_8, x_1);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___closed__0));
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___closed__0));
x_5 = lean_array_size(x_2);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0(x_1, x_2, x_5, x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 0)
{
return x_3;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 0);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
x_11 = x_9;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inDiseqValues___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_Rat_ofInt(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0, &l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0);
x_5 = l_Rat_add(x_1, x_4);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_leAvoiding(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0, &l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0);
x_5 = l_Rat_sub(x_1, x_4);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_leAvoiding___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_leAvoiding(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1));
x_64 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(x_63, x_12);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_67; 
x_67 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_MessageData_ofExpr(x_68);
x_72 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3, &l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_MessageData_ofExpr(x_70);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_63, x_75, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_dec_ref(x_76);
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = lean_box(0);
goto block_62;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_68);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = lean_ctor_get(x_69, 0);
x_84 = !lean_is_exclusive(x_69);
if (x_84 == 0)
{
x_78 = x_69;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_67, 0);
x_92 = !lean_is_exclusive(x_67);
if (x_92 == 0)
{
x_86 = x_67;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_67);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
block_32:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_28);
x_31 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_30, x_16, x_27, x_17, x_26, x_22, x_23, x_25, x_24, x_21, x_19, x_18);
return x_31;
}
block_62:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_46) == 1)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 2);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 2);
x_53 = lean_nat_abs(x_51);
x_54 = lean_nat_to_int(x_53);
lean_inc(x_49);
x_55 = l_Lean_Grind_Linarith_Poly_mul(x_49, x_54);
lean_dec(x_54);
x_56 = lean_nat_abs(x_48);
x_57 = lean_nat_to_int(x_56);
lean_inc(x_52);
x_58 = l_Lean_Grind_Linarith_Poly_mul(x_52, x_57);
lean_dec(x_57);
x_59 = l_Lean_Grind_Linarith_Poly_combine(x_55, x_58);
if (x_47 == 0)
{
x_15 = x_59;
x_16 = x_33;
x_17 = x_35;
x_18 = x_43;
x_19 = x_42;
x_20 = lean_box(0);
x_21 = x_41;
x_22 = x_37;
x_23 = x_38;
x_24 = x_40;
x_25 = x_39;
x_26 = x_36;
x_27 = x_34;
x_28 = x_50;
goto block_32;
}
else
{
x_15 = x_59;
x_16 = x_33;
x_17 = x_35;
x_18 = x_43;
x_19 = x_42;
x_20 = lean_box(0);
x_21 = x_41;
x_22 = x_37;
x_23 = x_38;
x_24 = x_40;
x_25 = x_39;
x_26 = x_36;
x_27 = x_34;
x_28 = x_47;
goto block_32;
}
}
else
{
lean_object* x_60; 
lean_dec_ref(x_1);
x_60 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_2, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_2);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec_ref(x_2);
x_61 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_1, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_1);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_int_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = l_Rat_ofInt(x_2);
x_6 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_5);
x_8 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0);
x_9 = lean_int_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findInt_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_14; lean_object* x_19; uint8_t x_20; lean_object* x_24; uint8_t x_25; 
lean_inc_ref(x_1);
x_19 = l_Rat_ceil(x_1);
lean_inc(x_19);
x_24 = l_Rat_ofInt(x_19);
x_25 = l_instDecidableEqRat_decEq(x_24, x_1);
lean_dec_ref(x_1);
lean_dec_ref(x_24);
if (x_25 == 0)
{
x_20 = x_25;
goto block_23;
}
else
{
x_20 = x_2;
goto block_23;
}
block_13:
{
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(x_5, x_7, x_6);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0);
x_11 = lean_int_sub(x_6, x_10);
lean_dec(x_6);
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(x_5, x_7, x_11);
lean_dec(x_11);
return x_12;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc_ref(x_3);
x_15 = l_Rat_floor(x_3);
lean_inc(x_15);
x_16 = l_Rat_ofInt(x_15);
x_17 = l_instDecidableEqRat_decEq(x_16, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_16);
if (x_17 == 0)
{
x_6 = x_15;
x_7 = x_14;
x_8 = x_17;
goto block_13;
}
else
{
x_6 = x_15;
x_7 = x_14;
x_8 = x_4;
goto block_13;
}
}
block_23:
{
if (x_20 == 0)
{
x_14 = x_19;
goto block_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_19);
x_14 = x_22;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findInt_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_4);
x_8 = l_Lean_Meta_Grind_Arith_Linear_findInt_x3f(x_1, x_6, x_3, x_7, x_5);
lean_dec_ref(x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc_ref(x_2);
x_4 = l_Rat_add(x_1, x_2);
x_5 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0, &l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0);
x_6 = l_Rat_div(x_4, x_5);
lean_dec_ref(x_4);
x_7 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_6, x_3);
if (x_7 == 0)
{
lean_dec_ref(x_2);
return x_6;
}
else
{
x_1 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_findRat(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_1, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_15; uint8_t x_16; uint8_t x_76; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_76 = !lean_is_exclusive(x_4);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_4, 7);
lean_dec(x_77);
x_78 = lean_ctor_get(x_4, 6);
lean_dec(x_78);
x_79 = lean_ctor_get(x_4, 5);
lean_dec(x_79);
x_80 = lean_ctor_get(x_4, 4);
lean_dec(x_80);
x_81 = lean_ctor_get(x_4, 3);
lean_dec(x_81);
x_82 = lean_ctor_get(x_4, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_4, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_4, 0);
lean_dec(x_84);
x_15 = x_4;
x_16 = x_76;
goto block_75;
}
else
{
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_17 = lean_array_fget(x_5, x_1);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 2);
x_21 = lean_ctor_get(x_17, 3);
x_22 = lean_ctor_get(x_17, 4);
x_23 = lean_ctor_get(x_17, 5);
x_24 = lean_ctor_get(x_17, 6);
x_25 = lean_ctor_get(x_17, 7);
x_26 = lean_ctor_get(x_17, 8);
x_27 = lean_ctor_get(x_17, 9);
x_28 = lean_ctor_get(x_17, 10);
x_29 = lean_ctor_get(x_17, 11);
x_30 = lean_ctor_get(x_17, 12);
x_31 = lean_ctor_get(x_17, 13);
x_32 = lean_ctor_get(x_17, 14);
x_33 = lean_ctor_get(x_17, 15);
x_34 = lean_ctor_get(x_17, 16);
x_35 = lean_ctor_get(x_17, 17);
x_36 = lean_ctor_get(x_17, 18);
x_37 = lean_ctor_get(x_17, 19);
x_38 = lean_ctor_get(x_17, 20);
x_39 = lean_ctor_get(x_17, 21);
x_40 = lean_ctor_get(x_17, 22);
x_41 = lean_ctor_get(x_17, 23);
x_42 = lean_ctor_get(x_17, 24);
x_43 = lean_ctor_get(x_17, 25);
x_44 = lean_ctor_get(x_17, 26);
x_45 = lean_ctor_get(x_17, 27);
x_46 = lean_ctor_get(x_17, 28);
x_47 = lean_ctor_get(x_17, 29);
x_48 = lean_ctor_get(x_17, 30);
x_49 = lean_ctor_get(x_17, 31);
x_50 = lean_ctor_get(x_17, 32);
x_51 = lean_ctor_get(x_17, 33);
x_52 = lean_ctor_get(x_17, 34);
x_53 = lean_ctor_get(x_17, 35);
x_54 = lean_ctor_get_uint8(x_17, sizeof(void*)*42);
x_55 = lean_ctor_get(x_17, 36);
x_56 = lean_ctor_get(x_17, 37);
x_57 = lean_ctor_get(x_17, 38);
x_58 = lean_ctor_get(x_17, 39);
x_59 = lean_ctor_get(x_17, 40);
x_60 = lean_ctor_get(x_17, 41);
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
x_61 = x_17;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_17);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_5, x_1, x_63);
x_65 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(x_56, x_2, x_3);
if (x_62 == 0)
{
lean_ctor_set(x_61, 37, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_72, 0, x_18);
lean_ctor_set(x_72, 1, x_19);
lean_ctor_set(x_72, 2, x_20);
lean_ctor_set(x_72, 3, x_21);
lean_ctor_set(x_72, 4, x_22);
lean_ctor_set(x_72, 5, x_23);
lean_ctor_set(x_72, 6, x_24);
lean_ctor_set(x_72, 7, x_25);
lean_ctor_set(x_72, 8, x_26);
lean_ctor_set(x_72, 9, x_27);
lean_ctor_set(x_72, 10, x_28);
lean_ctor_set(x_72, 11, x_29);
lean_ctor_set(x_72, 12, x_30);
lean_ctor_set(x_72, 13, x_31);
lean_ctor_set(x_72, 14, x_32);
lean_ctor_set(x_72, 15, x_33);
lean_ctor_set(x_72, 16, x_34);
lean_ctor_set(x_72, 17, x_35);
lean_ctor_set(x_72, 18, x_36);
lean_ctor_set(x_72, 19, x_37);
lean_ctor_set(x_72, 20, x_38);
lean_ctor_set(x_72, 21, x_39);
lean_ctor_set(x_72, 22, x_40);
lean_ctor_set(x_72, 23, x_41);
lean_ctor_set(x_72, 24, x_42);
lean_ctor_set(x_72, 25, x_43);
lean_ctor_set(x_72, 26, x_44);
lean_ctor_set(x_72, 27, x_45);
lean_ctor_set(x_72, 28, x_46);
lean_ctor_set(x_72, 29, x_47);
lean_ctor_set(x_72, 30, x_48);
lean_ctor_set(x_72, 31, x_49);
lean_ctor_set(x_72, 32, x_50);
lean_ctor_set(x_72, 33, x_51);
lean_ctor_set(x_72, 34, x_52);
lean_ctor_set(x_72, 35, x_53);
lean_ctor_set(x_72, 36, x_55);
lean_ctor_set(x_72, 37, x_65);
lean_ctor_set(x_72, 38, x_57);
lean_ctor_set(x_72, 39, x_58);
lean_ctor_set(x_72, 40, x_59);
lean_ctor_set(x_72, 41, x_60);
lean_ctor_set_uint8(x_72, sizeof(void*)*42, x_54);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_1, x_66);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_67);
x_68 = x_15;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_6);
lean_ctor_set(x_70, 2, x_7);
lean_ctor_set(x_70, 3, x_8);
lean_ctor_set(x_70, 4, x_9);
lean_ctor_set(x_70, 5, x_10);
lean_ctor_set(x_70, 6, x_11);
lean_ctor_set(x_70, 7, x_12);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_del_object(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_del_object(x_5);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(x_26, x_27, x_28, x_3);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_31; 
x_16 = lean_ctor_get(x_15, 0);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
x_17 = x_15;
x_18 = x_31;
goto block_30;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 3);
lean_inc(x_20);
lean_dec(x_16);
x_21 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1));
x_22 = l_Lean_Level_succ___override(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_mkConst(x_21, x_24);
x_26 = l_Lean_mkApp3(x_25, x_19, x_1, x_2);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_26);
x_27 = x_17;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_15, 0);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
x_33 = x_15;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0);
x_16 = lean_int_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_38; 
x_20 = lean_ctor_get(x_19, 0);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
x_21 = x_19;
x_22 = x_38;
goto block_37;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; uint8_t x_34; 
x_23 = lean_ctor_get(x_20, 30);
lean_inc_ref(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_18, 23);
lean_inc_ref(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_23, 2);
x_26 = l_Lean_mkIntLit(x_1);
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_nat_dec_lt(x_2, x_25);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_23);
x_35 = l_outOfBounds___redArg(x_33);
x_27 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_PersistentArray_get_x21___redArg(x_33, x_23, x_2);
x_27 = x_36;
goto block_32;
}
block_32:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_mkAppB(x_24, x_26, x_27);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_28);
x_29 = x_21;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_18);
x_39 = lean_ctor_get(x_19, 0);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
x_40 = x_19;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
x_47 = lean_ctor_get(x_17, 0);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
x_48 = x_17;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_17);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_72; 
x_56 = lean_ctor_get(x_55, 0);
x_72 = !lean_is_exclusive(x_55);
if (x_72 == 0)
{
x_57 = x_55;
x_58 = x_72;
goto block_71;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_56, 30);
lean_inc_ref(x_59);
lean_dec(x_56);
x_60 = lean_ctor_get(x_59, 2);
x_61 = l_Lean_instInhabitedExpr;
x_62 = lean_nat_dec_lt(x_2, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_59);
x_63 = l_outOfBounds___redArg(x_61);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_63);
x_64 = x_57;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_PersistentArray_get_x21___redArg(x_61, x_59, x_2);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_67);
x_68 = x_57;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_73 = lean_ctor_get(x_55, 0);
x_80 = !lean_is_exclusive(x_55);
if (x_80 == 0)
{
x_74 = x_55;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_55);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_21, 22);
lean_inc_ref(x_24);
lean_dec(x_21);
x_25 = l_Lean_mkAppB(x_24, x_2, x_23);
x_1 = x_19;
x_2 = x_25;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_2);
return x_22;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec_ref(x_2);
x_27 = lean_ctor_get(x_20, 0);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_28 = x_20;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
x_17 = x_15;
x_18 = x_24;
goto block_23;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 17);
lean_inc_ref(x_19);
lean_dec(x_16);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_15, 0);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
x_26 = x_15;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6(x_35, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_38;
}
else
{
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 18);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(x_17, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_22 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_23 = x_21;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_mkNot(x_22);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
return x_21;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_17);
x_31 = lean_ctor_get(x_18, 0);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
x_32 = x_18;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_130; 
x_16 = lean_ctor_get(x_15, 0);
x_130 = !lean_is_exclusive(x_15);
if (x_130 == 0)
{
x_17 = x_15;
x_18 = x_130;
goto block_129;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; 
x_19 = lean_ctor_get(x_16, 37);
lean_inc_ref(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_30 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(x_19, x_20);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1));
x_33 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_32, x_12);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
x_21 = x_31;
x_22 = lean_box(0);
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_65; 
x_36 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_1, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_1, 0);
lean_dec(x_67);
x_37 = x_1;
x_38 = x_65;
goto block_64;
}
else
{
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = x_65;
goto block_64;
}
block_64:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec_ref(x_36);
x_40 = l_Lean_MessageData_ofExpr(x_39);
x_41 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3, &l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3);
if (x_38 == 0)
{
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_41);
lean_ctor_set(x_37, 0, x_40);
x_42 = x_37;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_41);
x_42 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_31);
x_43 = l_Lean_MessageData_ofName(x_31);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_32, x_44, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_21 = x_31;
x_22 = lean_box(0);
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_31);
lean_dec(x_20);
lean_del_object(x_17);
x_46 = lean_ctor_get(x_45, 0);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
x_47 = x_45;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_del_object(x_37);
lean_dec(x_31);
lean_dec(x_20);
lean_del_object(x_17);
x_56 = lean_ctor_get(x_36, 0);
x_63 = !lean_is_exclusive(x_36);
if (x_63 == 0)
{
x_57 = x_36;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_36);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
}
else
{
lean_object* x_68; 
lean_dec(x_30);
lean_inc(x_3);
lean_inc_ref(x_1);
x_68 = l_Lean_Meta_Grind_Arith_Linear_mkCase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_85 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1));
x_86 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_85, x_12);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_dec_ref(x_1);
x_70 = x_3;
x_71 = x_4;
x_72 = lean_box(0);
goto block_84;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_118; 
x_89 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_118 = !lean_is_exclusive(x_1);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_1, 1);
lean_dec(x_119);
x_120 = lean_ctor_get(x_1, 0);
lean_dec(x_120);
x_90 = x_1;
x_91 = x_118;
goto block_117;
}
else
{
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = x_118;
goto block_117;
}
block_117:
{
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec_ref(x_89);
x_93 = l_Lean_MessageData_ofExpr(x_92);
x_94 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3, &l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3);
if (x_91 == 0)
{
lean_ctor_set_tag(x_90, 7);
lean_ctor_set(x_90, 1, x_94);
lean_ctor_set(x_90, 0, x_93);
x_95 = x_90;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
x_95 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_inc(x_69);
x_96 = l_Lean_MessageData_ofName(x_69);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_85, x_97, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_70 = x_3;
x_71 = x_4;
x_72 = lean_box(0);
goto block_84;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec(x_69);
lean_dec(x_20);
lean_del_object(x_17);
lean_dec(x_3);
x_99 = lean_ctor_get(x_98, 0);
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
x_100 = x_98;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_del_object(x_90);
lean_dec(x_69);
lean_dec(x_20);
lean_del_object(x_17);
lean_dec(x_3);
x_109 = lean_ctor_get(x_89, 0);
x_116 = !lean_is_exclusive(x_89);
if (x_116 == 0)
{
x_110 = x_89;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_89);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
}
block_84:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc(x_69);
lean_inc(x_20);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0___boxed), 4, 3);
lean_closure_set(x_73, 0, x_70);
lean_closure_set(x_73, 1, x_20);
lean_closure_set(x_73, 2, x_69);
x_74 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_75 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_74, x_73, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_dec_ref(x_75);
x_21 = x_69;
x_22 = lean_box(0);
goto block_29;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_69);
lean_dec(x_20);
lean_del_object(x_17);
x_76 = lean_ctor_get(x_75, 0);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
x_77 = x_75;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_128; 
lean_dec(x_20);
lean_del_object(x_17);
lean_dec(x_3);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_68, 0);
x_128 = !lean_is_exclusive(x_68);
if (x_128 == 0)
{
x_122 = x_68;
x_123 = x_128;
goto block_127;
}
else
{
lean_inc(x_121);
lean_dec(x_68);
x_122 = lean_box(0);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_123 == 0)
{
x_124 = x_122;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
}
block_29:
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 1;
x_24 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_25);
x_26 = x_17;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_138; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_131 = lean_ctor_get(x_15, 0);
x_138 = !lean_is_exclusive(x_15);
if (x_138 == 0)
{
x_132 = x_15;
x_133 = x_138;
goto block_137;
}
else
{
lean_inc(x_131);
lean_dec(x_15);
x_132 = lean_box(0);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_133 == 0)
{
x_134 = x_132;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_131);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_1, x_2, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = l_Lean_Grind_Linarith_Poly_leadCoeff(x_29);
x_31 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_32 = lean_int_dec_lt(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
x_16 = x_2;
goto block_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0, &l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0);
lean_inc(x_29);
x_34 = l_Lean_Grind_Linarith_Poly_mul(x_29, x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_16 = x_36;
goto block_28;
}
block_28:
{
lean_object* x_17; 
lean_inc(x_4);
x_17 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_17, 0);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
x_21 = x_17;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_75; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_75 = !lean_is_exclusive(x_3);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_3, 7);
lean_dec(x_76);
x_77 = lean_ctor_get(x_3, 6);
lean_dec(x_77);
x_78 = lean_ctor_get(x_3, 5);
lean_dec(x_78);
x_79 = lean_ctor_get(x_3, 4);
lean_dec(x_79);
x_80 = lean_ctor_get(x_3, 3);
lean_dec(x_80);
x_81 = lean_ctor_get(x_3, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_3, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_3, 0);
lean_dec(x_83);
x_14 = x_3;
x_15 = x_75;
goto block_74;
}
else
{
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_73; 
x_16 = lean_array_fget(x_4, x_1);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 2);
x_20 = lean_ctor_get(x_16, 3);
x_21 = lean_ctor_get(x_16, 4);
x_22 = lean_ctor_get(x_16, 5);
x_23 = lean_ctor_get(x_16, 6);
x_24 = lean_ctor_get(x_16, 7);
x_25 = lean_ctor_get(x_16, 8);
x_26 = lean_ctor_get(x_16, 9);
x_27 = lean_ctor_get(x_16, 10);
x_28 = lean_ctor_get(x_16, 11);
x_29 = lean_ctor_get(x_16, 12);
x_30 = lean_ctor_get(x_16, 13);
x_31 = lean_ctor_get(x_16, 14);
x_32 = lean_ctor_get(x_16, 15);
x_33 = lean_ctor_get(x_16, 16);
x_34 = lean_ctor_get(x_16, 17);
x_35 = lean_ctor_get(x_16, 18);
x_36 = lean_ctor_get(x_16, 19);
x_37 = lean_ctor_get(x_16, 20);
x_38 = lean_ctor_get(x_16, 21);
x_39 = lean_ctor_get(x_16, 22);
x_40 = lean_ctor_get(x_16, 23);
x_41 = lean_ctor_get(x_16, 24);
x_42 = lean_ctor_get(x_16, 25);
x_43 = lean_ctor_get(x_16, 26);
x_44 = lean_ctor_get(x_16, 27);
x_45 = lean_ctor_get(x_16, 28);
x_46 = lean_ctor_get(x_16, 29);
x_47 = lean_ctor_get(x_16, 30);
x_48 = lean_ctor_get(x_16, 31);
x_49 = lean_ctor_get(x_16, 32);
x_50 = lean_ctor_get(x_16, 33);
x_51 = lean_ctor_get(x_16, 34);
x_52 = lean_ctor_get(x_16, 35);
x_53 = lean_ctor_get_uint8(x_16, sizeof(void*)*42);
x_54 = lean_ctor_get(x_16, 36);
x_55 = lean_ctor_get(x_16, 37);
x_56 = lean_ctor_get(x_16, 38);
x_57 = lean_ctor_get(x_16, 39);
x_58 = lean_ctor_get(x_16, 40);
x_59 = lean_ctor_get(x_16, 41);
x_73 = !lean_is_exclusive(x_16);
if (x_73 == 0)
{
x_60 = x_16;
x_61 = x_73;
goto block_72;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_16);
x_60 = lean_box(0);
x_61 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_box(0);
x_63 = lean_array_fset(x_4, x_1, x_62);
x_64 = l_Lean_PersistentArray_push___redArg(x_59, x_2);
if (x_61 == 0)
{
lean_ctor_set(x_60, 41, x_64);
x_65 = x_60;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_71, 0, x_17);
lean_ctor_set(x_71, 1, x_18);
lean_ctor_set(x_71, 2, x_19);
lean_ctor_set(x_71, 3, x_20);
lean_ctor_set(x_71, 4, x_21);
lean_ctor_set(x_71, 5, x_22);
lean_ctor_set(x_71, 6, x_23);
lean_ctor_set(x_71, 7, x_24);
lean_ctor_set(x_71, 8, x_25);
lean_ctor_set(x_71, 9, x_26);
lean_ctor_set(x_71, 10, x_27);
lean_ctor_set(x_71, 11, x_28);
lean_ctor_set(x_71, 12, x_29);
lean_ctor_set(x_71, 13, x_30);
lean_ctor_set(x_71, 14, x_31);
lean_ctor_set(x_71, 15, x_32);
lean_ctor_set(x_71, 16, x_33);
lean_ctor_set(x_71, 17, x_34);
lean_ctor_set(x_71, 18, x_35);
lean_ctor_set(x_71, 19, x_36);
lean_ctor_set(x_71, 20, x_37);
lean_ctor_set(x_71, 21, x_38);
lean_ctor_set(x_71, 22, x_39);
lean_ctor_set(x_71, 23, x_40);
lean_ctor_set(x_71, 24, x_41);
lean_ctor_set(x_71, 25, x_42);
lean_ctor_set(x_71, 26, x_43);
lean_ctor_set(x_71, 27, x_44);
lean_ctor_set(x_71, 28, x_45);
lean_ctor_set(x_71, 29, x_46);
lean_ctor_set(x_71, 30, x_47);
lean_ctor_set(x_71, 31, x_48);
lean_ctor_set(x_71, 32, x_49);
lean_ctor_set(x_71, 33, x_50);
lean_ctor_set(x_71, 34, x_51);
lean_ctor_set(x_71, 35, x_52);
lean_ctor_set(x_71, 36, x_54);
lean_ctor_set(x_71, 37, x_55);
lean_ctor_set(x_71, 38, x_56);
lean_ctor_set(x_71, 39, x_57);
lean_ctor_set(x_71, 40, x_58);
lean_ctor_set(x_71, 41, x_64);
lean_ctor_set_uint8(x_71, sizeof(void*)*42, x_53);
x_65 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_array_fset(x_63, x_1, x_65);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_66);
x_67 = x_14;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_5);
lean_ctor_set(x_69, 2, x_6);
lean_ctor_set(x_69, 3, x_7);
lean_ctor_set(x_69, 4, x_8);
lean_ctor_set(x_69, 5, x_9);
lean_ctor_set(x_69, 6, x_10);
lean_ctor_set(x_69, 7, x_11);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_47; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
x_6 = x_1;
x_7 = x_47;
goto block_46;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_8; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_eq(x_17, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_27 = lean_int_dec_lt(x_16, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_nat_abs(x_16);
lean_dec(x_16);
x_29 = l_Nat_reprFast(x_28);
x_18 = x_29;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_nat_abs(x_16);
lean_dec(x_16);
x_31 = lean_nat_sub(x_30, x_24);
lean_dec(x_30);
x_32 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_33 = lean_nat_add(x_31, x_24);
lean_dec(x_31);
x_34 = l_Nat_reprFast(x_33);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
x_18 = x_35;
goto block_23;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_17);
x_36 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_37 = lean_int_dec_lt(x_16, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_nat_abs(x_16);
lean_dec(x_16);
x_39 = l_Nat_reprFast(x_38);
x_8 = x_39;
goto block_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_nat_abs(x_16);
lean_dec(x_16);
x_41 = lean_nat_sub(x_40, x_24);
lean_dec(x_40);
x_42 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_43 = lean_nat_add(x_41, x_24);
lean_dec(x_41);
x_44 = l_Nat_reprFast(x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec_ref(x_44);
x_8 = x_45;
goto block_15;
}
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_MessageData_ofFormat(x_9);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_10);
x_11 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_2);
x_11 = x_14;
goto block_13;
}
block_13:
{
x_1 = x_5;
x_2 = x_11;
goto _start;
}
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Nat_reprFast(x_17);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_8 = x_22;
goto block_15;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_getDiseqValues(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_113; 
x_53 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2));
x_54 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_53, x_12);
x_55 = lean_ctor_get(x_54, 0);
x_113 = !lean_is_exclusive(x_54);
if (x_113 == 0)
{
x_56 = x_54;
x_57 = x_113;
goto block_112;
}
else
{
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3);
x_59 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding(x_58, x_20);
x_60 = lean_unbox(x_55);
lean_dec(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
lean_del_object(x_56);
lean_dec(x_20);
x_61 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_84; lean_object* x_90; uint8_t x_91; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
x_64 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_dec_eq(x_63, x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_93 = lean_int_dec_lt(x_62, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_nat_abs(x_62);
lean_dec(x_62);
x_95 = l_Nat_reprFast(x_94);
x_84 = x_95;
goto block_89;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_nat_abs(x_62);
lean_dec(x_62);
x_97 = lean_nat_sub(x_96, x_90);
lean_dec(x_96);
x_98 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_99 = lean_nat_add(x_97, x_90);
lean_dec(x_97);
x_100 = l_Nat_reprFast(x_99);
x_101 = lean_string_append(x_98, x_100);
lean_dec_ref(x_100);
x_84 = x_101;
goto block_89;
}
}
else
{
lean_object* x_102; uint8_t x_103; 
lean_dec(x_63);
x_102 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_103 = lean_int_dec_lt(x_62, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_nat_abs(x_62);
lean_dec(x_62);
x_105 = l_Nat_reprFast(x_104);
x_65 = x_105;
goto block_83;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_nat_abs(x_62);
lean_dec(x_62);
x_107 = lean_nat_sub(x_106, x_90);
lean_dec(x_106);
x_108 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_109 = lean_nat_add(x_107, x_90);
lean_dec(x_107);
x_110 = l_Nat_reprFast(x_109);
x_111 = lean_string_append(x_108, x_110);
lean_dec_ref(x_110);
x_65 = x_111;
goto block_83;
}
}
block_83:
{
lean_object* x_66; 
if (x_57 == 0)
{
lean_ctor_set_tag(x_56, 3);
lean_ctor_set(x_56, 0, x_65);
x_66 = x_56;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_65);
x_66 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = l_Lean_MessageData_ofFormat(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_size(x_20);
x_72 = 0;
x_73 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_71, x_72, x_20);
x_74 = lean_array_to_list(x_73);
x_75 = lean_box(0);
x_76 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_74, x_75);
x_77 = l_Lean_MessageData_ofList(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_53, x_78, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec_ref(x_79);
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_80;
}
else
{
lean_dec_ref(x_59);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_79;
}
}
}
block_89:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Nat_reprFast(x_63);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
x_65 = x_88;
goto block_83;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_237; 
x_114 = lean_ctor_get(x_18, 0);
x_237 = !lean_is_exclusive(x_18);
if (x_237 == 0)
{
x_115 = x_18;
x_116 = x_237;
goto block_236;
}
else
{
lean_inc(x_114);
lean_dec(x_18);
x_115 = lean_box(0);
x_116 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_234; 
x_117 = lean_ctor_get(x_114, 0);
x_234 = !lean_is_exclusive(x_114);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_114, 1);
lean_dec(x_235);
x_118 = x_114;
x_119 = x_234;
goto block_233;
}
else
{
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_box(0);
x_119 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_232; 
x_120 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2));
x_121 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_120, x_12);
x_122 = lean_ctor_get(x_121, 0);
x_232 = !lean_is_exclusive(x_121);
if (x_232 == 0)
{
x_123 = x_121;
x_124 = x_232;
goto block_231;
}
else
{
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_box(0);
x_124 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_161; 
lean_inc(x_117);
x_125 = l_Rat_floor(x_117);
x_126 = l_Rat_ofInt(x_125);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0, &l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0);
x_129 = l_Rat_sub(x_126, x_128);
x_130 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding(x_129, x_20);
x_161 = lean_unbox(x_122);
lean_dec(x_122);
if (x_161 == 0)
{
lean_object* x_162; 
lean_del_object(x_123);
lean_del_object(x_118);
lean_dec(x_117);
lean_del_object(x_115);
lean_dec(x_20);
x_162 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_204; uint8_t x_210; 
x_163 = lean_ctor_get(x_130, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_130, 1);
lean_inc(x_164);
x_165 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5);
x_210 = lean_nat_dec_eq(x_164, x_127);
if (x_210 == 0)
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_212 = lean_int_dec_lt(x_163, x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_nat_abs(x_163);
lean_dec(x_163);
x_214 = l_Nat_reprFast(x_213);
x_204 = x_214;
goto block_209;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_nat_abs(x_163);
lean_dec(x_163);
x_216 = lean_nat_sub(x_215, x_127);
lean_dec(x_215);
x_217 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_218 = lean_nat_add(x_216, x_127);
lean_dec(x_216);
x_219 = l_Nat_reprFast(x_218);
x_220 = lean_string_append(x_217, x_219);
lean_dec_ref(x_219);
x_204 = x_220;
goto block_209;
}
}
else
{
lean_object* x_221; uint8_t x_222; 
lean_dec(x_164);
x_221 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_222 = lean_int_dec_lt(x_163, x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_nat_abs(x_163);
lean_dec(x_163);
x_224 = l_Nat_reprFast(x_223);
x_166 = x_224;
goto block_203;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_nat_abs(x_163);
lean_dec(x_163);
x_226 = lean_nat_sub(x_225, x_127);
lean_dec(x_225);
x_227 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_228 = lean_nat_add(x_226, x_127);
lean_dec(x_226);
x_229 = l_Nat_reprFast(x_228);
x_230 = lean_string_append(x_227, x_229);
lean_dec_ref(x_229);
x_166 = x_230;
goto block_203;
}
}
block_203:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_202; 
x_167 = lean_ctor_get(x_117, 0);
x_168 = lean_ctor_get(x_117, 1);
x_202 = !lean_is_exclusive(x_117);
if (x_202 == 0)
{
x_169 = x_117;
x_170 = x_202;
goto block_201;
}
else
{
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_117);
x_169 = lean_box(0);
x_170 = x_202;
goto block_201;
}
block_201:
{
lean_object* x_171; 
if (x_116 == 0)
{
lean_ctor_set_tag(x_115, 3);
lean_ctor_set(x_115, 0, x_166);
x_171 = x_115;
goto block_199;
}
else
{
lean_object* x_200; 
x_200 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_200, 0, x_166);
x_171 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_172; lean_object* x_173; 
x_172 = l_Lean_MessageData_ofFormat(x_171);
if (x_170 == 0)
{
lean_ctor_set_tag(x_169, 7);
lean_ctor_set(x_169, 1, x_172);
lean_ctor_set(x_169, 0, x_165);
x_173 = x_169;
goto block_197;
}
else
{
lean_object* x_198; 
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_165);
lean_ctor_set(x_198, 1, x_172);
x_173 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_nat_dec_eq(x_168, x_127);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_178 = lean_int_dec_lt(x_167, x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_nat_abs(x_167);
lean_dec(x_167);
x_180 = l_Nat_reprFast(x_179);
x_153 = x_168;
x_154 = x_175;
x_155 = x_180;
goto block_160;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_nat_abs(x_167);
lean_dec(x_167);
x_182 = lean_nat_sub(x_181, x_127);
lean_dec(x_181);
x_183 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_184 = lean_nat_add(x_182, x_127);
lean_dec(x_182);
x_185 = l_Nat_reprFast(x_184);
x_186 = lean_string_append(x_183, x_185);
lean_dec_ref(x_185);
x_153 = x_168;
x_154 = x_175;
x_155 = x_186;
goto block_160;
}
}
else
{
lean_object* x_187; uint8_t x_188; 
lean_dec(x_168);
x_187 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_188 = lean_int_dec_lt(x_167, x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_nat_abs(x_167);
lean_dec(x_167);
x_190 = l_Nat_reprFast(x_189);
x_131 = x_175;
x_132 = x_190;
goto block_152;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_191 = lean_nat_abs(x_167);
lean_dec(x_167);
x_192 = lean_nat_sub(x_191, x_127);
lean_dec(x_191);
x_193 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_194 = lean_nat_add(x_192, x_127);
lean_dec(x_192);
x_195 = l_Nat_reprFast(x_194);
x_196 = lean_string_append(x_193, x_195);
lean_dec_ref(x_195);
x_131 = x_175;
x_132 = x_196;
goto block_152;
}
}
}
}
}
}
block_209:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_206 = lean_string_append(x_204, x_205);
x_207 = l_Nat_reprFast(x_164);
x_208 = lean_string_append(x_206, x_207);
lean_dec_ref(x_207);
x_166 = x_208;
goto block_203;
}
}
block_152:
{
lean_object* x_133; 
if (x_124 == 0)
{
lean_ctor_set_tag(x_123, 3);
lean_ctor_set(x_123, 0, x_132);
x_133 = x_123;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_151, 0, x_132);
x_133 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lean_MessageData_ofFormat(x_133);
if (x_119 == 0)
{
lean_ctor_set_tag(x_118, 7);
lean_ctor_set(x_118, 1, x_134);
lean_ctor_set(x_118, 0, x_131);
x_135 = x_118;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_131);
lean_ctor_set(x_149, 1, x_134);
x_135 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_136; lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_136 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_array_size(x_20);
x_139 = 0;
x_140 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_138, x_139, x_20);
x_141 = lean_array_to_list(x_140);
x_142 = lean_box(0);
x_143 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_141, x_142);
x_144 = l_Lean_MessageData_ofList(x_143);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_120, x_145, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
lean_dec_ref(x_146);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_147;
}
else
{
lean_dec_ref(x_130);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_146;
}
}
}
}
block_160:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_157 = lean_string_append(x_155, x_156);
x_158 = l_Nat_reprFast(x_153);
x_159 = lean_string_append(x_157, x_158);
lean_dec_ref(x_158);
x_131 = x_154;
x_132 = x_159;
goto block_152;
}
}
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_679; 
x_238 = lean_ctor_get(x_16, 0);
x_679 = !lean_is_exclusive(x_16);
if (x_679 == 0)
{
x_239 = x_16;
x_240 = x_679;
goto block_678;
}
else
{
lean_inc(x_238);
lean_dec(x_16);
x_239 = lean_box(0);
x_240 = x_679;
goto block_678;
}
block_678:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_677; 
x_241 = lean_ctor_get(x_238, 0);
x_242 = lean_ctor_get(x_238, 1);
x_677 = !lean_is_exclusive(x_238);
if (x_677 == 0)
{
x_243 = x_238;
x_244 = x_677;
goto block_676;
}
else
{
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_238);
x_243 = lean_box(0);
x_244 = x_677;
goto block_676;
}
block_676:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_423; 
lean_del_object(x_243);
lean_dec(x_242);
lean_del_object(x_239);
x_315 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2));
x_316 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_315, x_12);
x_317 = lean_ctor_get(x_316, 0);
x_423 = !lean_is_exclusive(x_316);
if (x_423 == 0)
{
x_318 = x_316;
x_319 = x_423;
goto block_422;
}
else
{
lean_inc(x_317);
lean_dec(x_316);
x_318 = lean_box(0);
x_319 = x_423;
goto block_422;
}
block_422:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_354; 
lean_inc(x_241);
x_320 = l_Rat_ceil(x_241);
x_321 = l_Rat_ofInt(x_320);
x_322 = lean_unsigned_to_nat(1u);
x_323 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0, &l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0);
x_324 = l_Rat_add(x_321, x_323);
x_325 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding(x_324, x_20);
x_354 = lean_unbox(x_317);
lean_dec(x_317);
if (x_354 == 0)
{
lean_object* x_355; 
lean_del_object(x_318);
lean_dec(x_241);
lean_dec(x_20);
x_355 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_325, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_395; uint8_t x_401; 
x_356 = lean_ctor_get(x_325, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_325, 1);
lean_inc(x_357);
x_358 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5);
x_401 = lean_nat_dec_eq(x_357, x_322);
if (x_401 == 0)
{
lean_object* x_402; uint8_t x_403; 
x_402 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_403 = lean_int_dec_lt(x_356, x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_nat_abs(x_356);
lean_dec(x_356);
x_405 = l_Nat_reprFast(x_404);
x_395 = x_405;
goto block_400;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_406 = lean_nat_abs(x_356);
lean_dec(x_356);
x_407 = lean_nat_sub(x_406, x_322);
lean_dec(x_406);
x_408 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_409 = lean_nat_add(x_407, x_322);
lean_dec(x_407);
x_410 = l_Nat_reprFast(x_409);
x_411 = lean_string_append(x_408, x_410);
lean_dec_ref(x_410);
x_395 = x_411;
goto block_400;
}
}
else
{
lean_object* x_412; uint8_t x_413; 
lean_dec(x_357);
x_412 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_413 = lean_int_dec_lt(x_356, x_412);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_nat_abs(x_356);
lean_dec(x_356);
x_415 = l_Nat_reprFast(x_414);
x_359 = x_415;
goto block_394;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_416 = lean_nat_abs(x_356);
lean_dec(x_356);
x_417 = lean_nat_sub(x_416, x_322);
lean_dec(x_416);
x_418 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_419 = lean_nat_add(x_417, x_322);
lean_dec(x_417);
x_420 = l_Nat_reprFast(x_419);
x_421 = lean_string_append(x_418, x_420);
lean_dec_ref(x_420);
x_359 = x_421;
goto block_394;
}
}
block_394:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; uint8_t x_393; 
x_360 = lean_ctor_get(x_241, 0);
x_361 = lean_ctor_get(x_241, 1);
x_393 = !lean_is_exclusive(x_241);
if (x_393 == 0)
{
x_362 = x_241;
x_363 = x_393;
goto block_392;
}
else
{
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_241);
x_362 = lean_box(0);
x_363 = x_393;
goto block_392;
}
block_392:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_364, 0, x_359);
x_365 = l_Lean_MessageData_ofFormat(x_364);
if (x_363 == 0)
{
lean_ctor_set_tag(x_362, 7);
lean_ctor_set(x_362, 1, x_365);
lean_ctor_set(x_362, 0, x_358);
x_366 = x_362;
goto block_390;
}
else
{
lean_object* x_391; 
x_391 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_391, 0, x_358);
lean_ctor_set(x_391, 1, x_365);
x_366 = x_391;
goto block_390;
}
block_390:
{
lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_367 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13);
x_368 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_nat_dec_eq(x_361, x_322);
if (x_369 == 0)
{
lean_object* x_370; uint8_t x_371; 
x_370 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_371 = lean_int_dec_lt(x_360, x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_nat_abs(x_360);
lean_dec(x_360);
x_373 = l_Nat_reprFast(x_372);
x_346 = x_361;
x_347 = x_368;
x_348 = x_373;
goto block_353;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_374 = lean_nat_abs(x_360);
lean_dec(x_360);
x_375 = lean_nat_sub(x_374, x_322);
lean_dec(x_374);
x_376 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_377 = lean_nat_add(x_375, x_322);
lean_dec(x_375);
x_378 = l_Nat_reprFast(x_377);
x_379 = lean_string_append(x_376, x_378);
lean_dec_ref(x_378);
x_346 = x_361;
x_347 = x_368;
x_348 = x_379;
goto block_353;
}
}
else
{
lean_object* x_380; uint8_t x_381; 
lean_dec(x_361);
x_380 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_381 = lean_int_dec_lt(x_360, x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_nat_abs(x_360);
lean_dec(x_360);
x_383 = l_Nat_reprFast(x_382);
x_326 = x_368;
x_327 = x_383;
goto block_345;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_384 = lean_nat_abs(x_360);
lean_dec(x_360);
x_385 = lean_nat_sub(x_384, x_322);
lean_dec(x_384);
x_386 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_387 = lean_nat_add(x_385, x_322);
lean_dec(x_385);
x_388 = l_Nat_reprFast(x_387);
x_389 = lean_string_append(x_386, x_388);
lean_dec_ref(x_388);
x_326 = x_368;
x_327 = x_389;
goto block_345;
}
}
}
}
}
block_400:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_396 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_397 = lean_string_append(x_395, x_396);
x_398 = l_Nat_reprFast(x_357);
x_399 = lean_string_append(x_397, x_398);
lean_dec_ref(x_398);
x_359 = x_399;
goto block_394;
}
}
block_345:
{
lean_object* x_328; 
if (x_319 == 0)
{
lean_ctor_set_tag(x_318, 3);
lean_ctor_set(x_318, 0, x_327);
x_328 = x_318;
goto block_343;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_344, 0, x_327);
x_328 = x_344;
goto block_343;
}
block_343:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; size_t x_333; size_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_329 = l_Lean_MessageData_ofFormat(x_328);
x_330 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_330, 0, x_326);
lean_ctor_set(x_330, 1, x_329);
x_331 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1);
x_332 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_array_size(x_20);
x_334 = 0;
x_335 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_333, x_334, x_20);
x_336 = lean_array_to_list(x_335);
x_337 = lean_box(0);
x_338 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_336, x_337);
x_339 = l_Lean_MessageData_ofList(x_338);
x_340 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_340, 0, x_332);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_315, x_340, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
lean_dec_ref(x_341);
x_342 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_325, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_342;
}
else
{
lean_dec_ref(x_325);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_341;
}
}
}
block_353:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_350 = lean_string_append(x_348, x_349);
x_351 = l_Nat_reprFast(x_346);
x_352 = lean_string_append(x_350, x_351);
lean_dec_ref(x_351);
x_326 = x_347;
x_327 = x_352;
goto block_345;
}
}
}
else
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; uint8_t x_675; 
x_424 = lean_ctor_get(x_18, 0);
x_675 = !lean_is_exclusive(x_18);
if (x_675 == 0)
{
x_425 = x_18;
x_426 = x_675;
goto block_674;
}
else
{
lean_inc(x_424);
lean_dec(x_18);
x_425 = lean_box(0);
x_426 = x_675;
goto block_674;
}
block_674:
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; uint8_t x_673; 
x_427 = lean_ctor_get(x_424, 0);
x_428 = lean_ctor_get(x_424, 1);
x_673 = !lean_is_exclusive(x_424);
if (x_673 == 0)
{
x_429 = x_424;
x_430 = x_673;
goto block_672;
}
else
{
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_424);
x_429 = lean_box(0);
x_430 = x_673;
goto block_672;
}
block_672:
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_539; uint8_t x_571; uint8_t x_667; 
lean_inc(x_241);
lean_inc(x_427);
x_667 = l_Rat_blt(x_427, x_241);
if (x_667 == 0)
{
uint8_t x_668; 
x_668 = l_instDecidableEqRat_decEq(x_241, x_427);
if (x_668 == 0)
{
x_571 = x_668;
goto block_666;
}
else
{
uint8_t x_669; 
x_669 = lean_ctor_get_uint8(x_242, sizeof(void*)*2);
if (x_669 == 0)
{
uint8_t x_670; 
x_670 = lean_ctor_get_uint8(x_428, sizeof(void*)*2);
x_571 = x_670;
goto block_666;
}
else
{
lean_object* x_671; 
lean_del_object(x_429);
lean_dec(x_427);
lean_del_object(x_425);
lean_del_object(x_243);
lean_dec(x_241);
lean_del_object(x_239);
lean_dec(x_20);
x_671 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(x_242, x_428, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_671;
}
}
}
else
{
x_571 = x_667;
goto block_666;
}
block_475:
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; uint8_t x_474; 
x_436 = lean_ctor_get(x_427, 0);
x_437 = lean_ctor_get(x_427, 1);
x_474 = !lean_is_exclusive(x_427);
if (x_474 == 0)
{
x_438 = x_427;
x_439 = x_474;
goto block_473;
}
else
{
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_427);
x_438 = lean_box(0);
x_439 = x_474;
goto block_473;
}
block_473:
{
lean_object* x_440; 
if (x_426 == 0)
{
lean_ctor_set_tag(x_425, 3);
lean_ctor_set(x_425, 0, x_435);
x_440 = x_425;
goto block_471;
}
else
{
lean_object* x_472; 
x_472 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_472, 0, x_435);
x_440 = x_472;
goto block_471;
}
block_471:
{
lean_object* x_441; lean_object* x_442; 
x_441 = l_Lean_MessageData_ofFormat(x_440);
if (x_439 == 0)
{
lean_ctor_set_tag(x_438, 7);
lean_ctor_set(x_438, 1, x_441);
lean_ctor_set(x_438, 0, x_433);
x_442 = x_438;
goto block_469;
}
else
{
lean_object* x_470; 
x_470 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_470, 0, x_433);
lean_ctor_set(x_470, 1, x_441);
x_442 = x_470;
goto block_469;
}
block_469:
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7);
if (x_430 == 0)
{
lean_ctor_set_tag(x_429, 7);
lean_ctor_set(x_429, 1, x_443);
lean_ctor_set(x_429, 0, x_442);
x_444 = x_429;
goto block_467;
}
else
{
lean_object* x_468; 
x_468 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_468, 0, x_442);
lean_ctor_set(x_468, 1, x_443);
x_444 = x_468;
goto block_467;
}
block_467:
{
lean_object* x_445; uint8_t x_446; 
x_445 = lean_unsigned_to_nat(1u);
x_446 = lean_nat_dec_eq(x_437, x_445);
if (x_446 == 0)
{
lean_object* x_447; uint8_t x_448; 
x_447 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_448 = lean_int_dec_lt(x_436, x_447);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_nat_abs(x_436);
lean_dec(x_436);
x_450 = l_Nat_reprFast(x_449);
x_42 = x_437;
x_43 = x_431;
x_44 = lean_box(0);
x_45 = x_444;
x_46 = x_434;
x_47 = x_450;
goto block_52;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_451 = lean_nat_abs(x_436);
lean_dec(x_436);
x_452 = lean_nat_sub(x_451, x_445);
lean_dec(x_451);
x_453 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_454 = lean_nat_add(x_452, x_445);
lean_dec(x_452);
x_455 = l_Nat_reprFast(x_454);
x_456 = lean_string_append(x_453, x_455);
lean_dec_ref(x_455);
x_42 = x_437;
x_43 = x_431;
x_44 = lean_box(0);
x_45 = x_444;
x_46 = x_434;
x_47 = x_456;
goto block_52;
}
}
else
{
lean_object* x_457; uint8_t x_458; 
lean_dec(x_437);
x_457 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_458 = lean_int_dec_lt(x_436, x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; 
x_459 = lean_nat_abs(x_436);
lean_dec(x_436);
x_460 = l_Nat_reprFast(x_459);
x_21 = lean_box(0);
x_22 = x_431;
x_23 = x_434;
x_24 = x_444;
x_25 = x_460;
goto block_41;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_461 = lean_nat_abs(x_436);
lean_dec(x_436);
x_462 = lean_nat_sub(x_461, x_445);
lean_dec(x_461);
x_463 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_464 = lean_nat_add(x_462, x_445);
lean_dec(x_462);
x_465 = l_Nat_reprFast(x_464);
x_466 = lean_string_append(x_463, x_465);
lean_dec_ref(x_465);
x_21 = lean_box(0);
x_22 = x_431;
x_23 = x_434;
x_24 = x_444;
x_25 = x_466;
goto block_41;
}
}
}
}
}
}
}
block_486:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_483 = lean_string_append(x_481, x_482);
x_484 = l_Nat_reprFast(x_480);
x_485 = lean_string_append(x_483, x_484);
lean_dec_ref(x_484);
x_431 = x_477;
x_432 = lean_box(0);
x_433 = x_478;
x_434 = x_479;
x_435 = x_485;
goto block_475;
}
block_527:
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; uint8_t x_526; 
x_492 = lean_ctor_get(x_241, 0);
x_493 = lean_ctor_get(x_241, 1);
x_526 = !lean_is_exclusive(x_241);
if (x_526 == 0)
{
x_494 = x_241;
x_495 = x_526;
goto block_525;
}
else
{
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_241);
x_494 = lean_box(0);
x_495 = x_526;
goto block_525;
}
block_525:
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_496, 0, x_491);
x_497 = l_Lean_MessageData_ofFormat(x_496);
if (x_495 == 0)
{
lean_ctor_set_tag(x_494, 7);
lean_ctor_set(x_494, 1, x_497);
lean_ctor_set(x_494, 0, x_489);
x_498 = x_494;
goto block_523;
}
else
{
lean_object* x_524; 
x_524 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_524, 0, x_489);
lean_ctor_set(x_524, 1, x_497);
x_498 = x_524;
goto block_523;
}
block_523:
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_499 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13);
x_500 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
x_501 = lean_unsigned_to_nat(1u);
x_502 = lean_nat_dec_eq(x_493, x_501);
if (x_502 == 0)
{
lean_object* x_503; uint8_t x_504; 
x_503 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_504 = lean_int_dec_lt(x_492, x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_nat_abs(x_492);
lean_dec(x_492);
x_506 = l_Nat_reprFast(x_505);
x_476 = lean_box(0);
x_477 = x_488;
x_478 = x_500;
x_479 = x_490;
x_480 = x_493;
x_481 = x_506;
goto block_486;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_507 = lean_nat_abs(x_492);
lean_dec(x_492);
x_508 = lean_nat_sub(x_507, x_501);
lean_dec(x_507);
x_509 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_510 = lean_nat_add(x_508, x_501);
lean_dec(x_508);
x_511 = l_Nat_reprFast(x_510);
x_512 = lean_string_append(x_509, x_511);
lean_dec_ref(x_511);
x_476 = lean_box(0);
x_477 = x_488;
x_478 = x_500;
x_479 = x_490;
x_480 = x_493;
x_481 = x_512;
goto block_486;
}
}
else
{
lean_object* x_513; uint8_t x_514; 
lean_dec(x_493);
x_513 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_514 = lean_int_dec_lt(x_492, x_513);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_nat_abs(x_492);
lean_dec(x_492);
x_516 = l_Nat_reprFast(x_515);
x_431 = x_488;
x_432 = lean_box(0);
x_433 = x_500;
x_434 = x_490;
x_435 = x_516;
goto block_475;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_517 = lean_nat_abs(x_492);
lean_dec(x_492);
x_518 = lean_nat_sub(x_517, x_501);
lean_dec(x_517);
x_519 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_520 = lean_nat_add(x_518, x_501);
lean_dec(x_518);
x_521 = l_Nat_reprFast(x_520);
x_522 = lean_string_append(x_519, x_521);
lean_dec_ref(x_521);
x_431 = x_488;
x_432 = lean_box(0);
x_433 = x_500;
x_434 = x_490;
x_435 = x_522;
goto block_475;
}
}
}
}
}
block_538:
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_535 = lean_string_append(x_533, x_534);
x_536 = l_Nat_reprFast(x_531);
x_537 = lean_string_append(x_535, x_536);
lean_dec_ref(x_536);
x_487 = lean_box(0);
x_488 = x_528;
x_489 = x_530;
x_490 = x_532;
x_491 = x_537;
goto block_527;
}
block_570:
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
x_540 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2));
x_541 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_540, x_12);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
lean_dec_ref(x_541);
x_543 = lean_unbox(x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; 
lean_del_object(x_429);
lean_dec(x_427);
lean_del_object(x_425);
lean_dec(x_241);
lean_dec(x_20);
x_544 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_539, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_544;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_545 = lean_ctor_get(x_539, 0);
x_546 = lean_ctor_get(x_539, 1);
x_547 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5);
x_548 = lean_unsigned_to_nat(1u);
x_549 = lean_nat_dec_eq(x_546, x_548);
if (x_549 == 0)
{
lean_object* x_550; uint8_t x_551; 
lean_inc(x_546);
x_550 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_551 = lean_int_dec_lt(x_545, x_550);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_nat_abs(x_545);
x_553 = l_Nat_reprFast(x_552);
x_528 = x_540;
x_529 = lean_box(0);
x_530 = x_547;
x_531 = x_546;
x_532 = x_539;
x_533 = x_553;
goto block_538;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_554 = lean_nat_abs(x_545);
x_555 = lean_nat_sub(x_554, x_548);
lean_dec(x_554);
x_556 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_557 = lean_nat_add(x_555, x_548);
lean_dec(x_555);
x_558 = l_Nat_reprFast(x_557);
x_559 = lean_string_append(x_556, x_558);
lean_dec_ref(x_558);
x_528 = x_540;
x_529 = lean_box(0);
x_530 = x_547;
x_531 = x_546;
x_532 = x_539;
x_533 = x_559;
goto block_538;
}
}
else
{
lean_object* x_560; uint8_t x_561; 
x_560 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_561 = lean_int_dec_lt(x_545, x_560);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; 
x_562 = lean_nat_abs(x_545);
x_563 = l_Nat_reprFast(x_562);
x_487 = lean_box(0);
x_488 = x_540;
x_489 = x_547;
x_490 = x_539;
x_491 = x_563;
goto block_527;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_564 = lean_nat_abs(x_545);
x_565 = lean_nat_sub(x_564, x_548);
lean_dec(x_564);
x_566 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_567 = lean_nat_add(x_565, x_548);
lean_dec(x_565);
x_568 = l_Nat_reprFast(x_567);
x_569 = lean_string_append(x_566, x_568);
lean_dec_ref(x_568);
x_487 = lean_box(0);
x_488 = x_540;
x_489 = x_547;
x_490 = x_539;
x_491 = x_569;
goto block_527;
}
}
}
}
block_666:
{
if (x_571 == 0)
{
uint8_t x_572; 
x_572 = l_instDecidableEqRat_decEq(x_241, x_427);
if (x_572 == 0)
{
uint8_t x_573; uint8_t x_574; lean_object* x_575; 
lean_del_object(x_243);
lean_del_object(x_239);
x_573 = lean_ctor_get_uint8(x_242, sizeof(void*)*2);
lean_dec(x_242);
x_574 = lean_ctor_get_uint8(x_428, sizeof(void*)*2);
lean_dec(x_428);
lean_inc(x_427);
lean_inc(x_241);
x_575 = l_Lean_Meta_Grind_Arith_Linear_findInt_x3f(x_241, x_573, x_427, x_574, x_20);
if (lean_obj_tag(x_575) == 1)
{
lean_object* x_576; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
lean_dec_ref(x_575);
x_539 = x_576;
goto block_570;
}
else
{
lean_object* x_577; 
lean_dec(x_575);
lean_inc(x_427);
lean_inc(x_241);
x_577 = l_Lean_Meta_Grind_Arith_Linear_findRat(x_241, x_427, x_20);
x_539 = x_577;
goto block_570;
}
}
else
{
lean_object* x_578; 
lean_del_object(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_del_object(x_425);
x_578 = l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(x_241, x_20);
if (lean_obj_tag(x_578) == 1)
{
lean_object* x_579; lean_object* x_580; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
lean_dec_ref(x_578);
x_580 = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; uint8_t x_582; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
lean_dec_ref(x_580);
x_582 = lean_unbox(x_581);
lean_dec(x_581);
if (x_582 == 0)
{
lean_object* x_583; 
lean_dec(x_242);
x_583 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(x_579, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_579);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
lean_dec_ref(x_583);
lean_inc(x_3);
x_585 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0___boxed), 3, 2);
lean_closure_set(x_585, 0, x_3);
lean_closure_set(x_585, 1, x_584);
x_586 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_587 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_586, x_585, x_4);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
lean_dec_ref(x_587);
x_588 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2));
x_589 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_588, x_12);
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec_ref(x_589);
x_591 = lean_unbox(x_590);
lean_dec(x_590);
if (x_591 == 0)
{
lean_object* x_592; 
lean_del_object(x_243);
lean_del_object(x_239);
lean_dec(x_20);
x_592 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_241, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_592;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; 
x_593 = lean_ctor_get(x_241, 0);
x_594 = lean_ctor_get(x_241, 1);
x_595 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5);
x_596 = lean_unsigned_to_nat(1u);
x_597 = lean_nat_dec_eq(x_594, x_596);
if (x_597 == 0)
{
lean_object* x_598; uint8_t x_599; 
x_598 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_599 = lean_int_dec_lt(x_593, x_598);
if (x_599 == 0)
{
lean_object* x_600; lean_object* x_601; 
x_600 = lean_nat_abs(x_593);
x_601 = l_Nat_reprFast(x_600);
lean_inc(x_594);
x_272 = x_594;
x_273 = lean_box(0);
x_274 = x_595;
x_275 = x_588;
x_276 = x_601;
goto block_281;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_602 = lean_nat_abs(x_593);
x_603 = lean_nat_sub(x_602, x_596);
lean_dec(x_602);
x_604 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_605 = lean_nat_add(x_603, x_596);
lean_dec(x_603);
x_606 = l_Nat_reprFast(x_605);
x_607 = lean_string_append(x_604, x_606);
lean_dec_ref(x_606);
lean_inc(x_594);
x_272 = x_594;
x_273 = lean_box(0);
x_274 = x_595;
x_275 = x_588;
x_276 = x_607;
goto block_281;
}
}
else
{
lean_object* x_608; uint8_t x_609; 
x_608 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_609 = lean_int_dec_lt(x_593, x_608);
if (x_609 == 0)
{
lean_object* x_610; lean_object* x_611; 
x_610 = lean_nat_abs(x_593);
x_611 = l_Nat_reprFast(x_610);
x_245 = lean_box(0);
x_246 = x_595;
x_247 = x_588;
x_248 = x_611;
goto block_271;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_612 = lean_nat_abs(x_593);
x_613 = lean_nat_sub(x_612, x_596);
lean_dec(x_612);
x_614 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_615 = lean_nat_add(x_613, x_596);
lean_dec(x_613);
x_616 = l_Nat_reprFast(x_615);
x_617 = lean_string_append(x_614, x_616);
lean_dec_ref(x_616);
x_245 = lean_box(0);
x_246 = x_595;
x_247 = x_588;
x_248 = x_617;
goto block_271;
}
}
}
}
else
{
lean_del_object(x_243);
lean_dec(x_241);
lean_del_object(x_239);
lean_dec(x_20);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_587;
}
}
else
{
lean_object* x_618; lean_object* x_619; uint8_t x_620; uint8_t x_625; 
lean_del_object(x_243);
lean_dec(x_241);
lean_del_object(x_239);
lean_dec(x_20);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_618 = lean_ctor_get(x_583, 0);
x_625 = !lean_is_exclusive(x_583);
if (x_625 == 0)
{
x_619 = x_583;
x_620 = x_625;
goto block_624;
}
else
{
lean_inc(x_618);
lean_dec(x_583);
x_619 = lean_box(0);
x_620 = x_625;
goto block_624;
}
block_624:
{
lean_object* x_621; 
if (x_620 == 0)
{
x_621 = x_619;
goto block_622;
}
else
{
lean_object* x_623; 
x_623 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_623, 0, x_618);
x_621 = x_623;
goto block_622;
}
block_622:
{
return x_621;
}
}
}
}
else
{
lean_object* x_626; 
lean_del_object(x_243);
lean_dec(x_241);
lean_del_object(x_239);
lean_dec(x_20);
x_626 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict(x_242, x_579, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_626;
}
}
else
{
lean_object* x_627; lean_object* x_628; uint8_t x_629; uint8_t x_634; 
lean_dec(x_579);
lean_del_object(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_del_object(x_239);
lean_dec(x_20);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_627 = lean_ctor_get(x_580, 0);
x_634 = !lean_is_exclusive(x_580);
if (x_634 == 0)
{
x_628 = x_580;
x_629 = x_634;
goto block_633;
}
else
{
lean_inc(x_627);
lean_dec(x_580);
x_628 = lean_box(0);
x_629 = x_634;
goto block_633;
}
block_633:
{
lean_object* x_630; 
if (x_629 == 0)
{
x_630 = x_628;
goto block_631;
}
else
{
lean_object* x_632; 
x_632 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_632, 0, x_627);
x_630 = x_632;
goto block_631;
}
block_631:
{
return x_630;
}
}
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; 
lean_dec(x_578);
lean_del_object(x_243);
lean_dec(x_242);
lean_del_object(x_239);
x_635 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2));
x_636 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_635, x_12);
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
lean_dec_ref(x_636);
x_638 = lean_unbox(x_637);
lean_dec(x_637);
if (x_638 == 0)
{
lean_object* x_639; 
lean_dec(x_20);
x_639 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_241, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_639;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; 
x_640 = lean_ctor_get(x_241, 0);
x_641 = lean_ctor_get(x_241, 1);
x_642 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5);
x_643 = lean_unsigned_to_nat(1u);
x_644 = lean_nat_dec_eq(x_641, x_643);
if (x_644 == 0)
{
lean_object* x_645; uint8_t x_646; 
x_645 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_646 = lean_int_dec_lt(x_640, x_645);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_nat_abs(x_640);
x_648 = l_Nat_reprFast(x_647);
lean_inc(x_641);
x_305 = x_635;
x_306 = lean_box(0);
x_307 = x_641;
x_308 = x_642;
x_309 = x_648;
goto block_314;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_649 = lean_nat_abs(x_640);
x_650 = lean_nat_sub(x_649, x_643);
lean_dec(x_649);
x_651 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_652 = lean_nat_add(x_650, x_643);
lean_dec(x_650);
x_653 = l_Nat_reprFast(x_652);
x_654 = lean_string_append(x_651, x_653);
lean_dec_ref(x_653);
lean_inc(x_641);
x_305 = x_635;
x_306 = lean_box(0);
x_307 = x_641;
x_308 = x_642;
x_309 = x_654;
goto block_314;
}
}
else
{
lean_object* x_655; uint8_t x_656; 
x_655 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_656 = lean_int_dec_lt(x_640, x_655);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; 
x_657 = lean_nat_abs(x_640);
x_658 = l_Nat_reprFast(x_657);
x_282 = lean_box(0);
x_283 = x_635;
x_284 = x_642;
x_285 = x_658;
goto block_304;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_659 = lean_nat_abs(x_640);
x_660 = lean_nat_sub(x_659, x_643);
lean_dec(x_659);
x_661 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10));
x_662 = lean_nat_add(x_660, x_643);
lean_dec(x_660);
x_663 = l_Nat_reprFast(x_662);
x_664 = lean_string_append(x_661, x_663);
lean_dec_ref(x_663);
x_282 = lean_box(0);
x_283 = x_635;
x_284 = x_642;
x_285 = x_664;
goto block_304;
}
}
}
}
}
}
else
{
lean_object* x_665; 
lean_del_object(x_429);
lean_dec(x_427);
lean_del_object(x_425);
lean_del_object(x_243);
lean_dec(x_241);
lean_del_object(x_239);
lean_dec(x_20);
x_665 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(x_242, x_428, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_665;
}
}
}
}
}
block_271:
{
lean_object* x_249; 
if (x_240 == 0)
{
lean_ctor_set_tag(x_239, 3);
lean_ctor_set(x_239, 0, x_248);
x_249 = x_239;
goto block_269;
}
else
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_270, 0, x_248);
x_249 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_250; lean_object* x_251; 
x_250 = l_Lean_MessageData_ofFormat(x_249);
lean_inc_ref(x_250);
if (x_244 == 0)
{
lean_ctor_set_tag(x_243, 7);
lean_ctor_set(x_243, 1, x_250);
lean_ctor_set(x_243, 0, x_246);
x_251 = x_243;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_268, 0, x_246);
lean_ctor_set(x_268, 1, x_250);
x_251 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; size_t x_257; size_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_252 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9);
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
x_255 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11);
x_256 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_array_size(x_20);
x_258 = 0;
x_259 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_257, x_258, x_20);
x_260 = lean_array_to_list(x_259);
x_261 = lean_box(0);
x_262 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_260, x_261);
x_263 = l_Lean_MessageData_ofList(x_262);
x_264 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_264, 0, x_256);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_247, x_264, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; 
lean_dec_ref(x_265);
x_266 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_241, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_266;
}
else
{
lean_dec(x_241);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_265;
}
}
}
}
block_281:
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_278 = lean_string_append(x_276, x_277);
x_279 = l_Nat_reprFast(x_272);
x_280 = lean_string_append(x_278, x_279);
lean_dec_ref(x_279);
x_245 = lean_box(0);
x_246 = x_274;
x_247 = x_275;
x_248 = x_280;
goto block_271;
}
block_304:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; size_t x_294; size_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_286 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_287 = l_Lean_MessageData_ofFormat(x_286);
lean_inc_ref(x_287);
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_284);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9);
x_290 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_287);
x_292 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1);
x_293 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_array_size(x_20);
x_295 = 0;
x_296 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_294, x_295, x_20);
x_297 = lean_array_to_list(x_296);
x_298 = lean_box(0);
x_299 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_297, x_298);
x_300 = l_Lean_MessageData_ofList(x_299);
x_301 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_301, 0, x_293);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_283, x_301, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; 
lean_dec_ref(x_302);
x_303 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_241, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_303;
}
else
{
lean_dec(x_241);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_302;
}
}
block_314:
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_310 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_311 = lean_string_append(x_309, x_310);
x_312 = l_Nat_reprFast(x_307);
x_313 = lean_string_append(x_311, x_312);
lean_dec_ref(x_312);
x_282 = lean_box(0);
x_283 = x_305;
x_284 = x_308;
x_285 = x_313;
goto block_304;
}
}
}
}
block_41:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_size(x_20);
x_32 = 0;
x_33 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_31, x_32, x_20);
x_34 = lean_array_to_list(x_33);
x_35 = lean_box(0);
x_36 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_34, x_35);
x_37 = l_Lean_MessageData_ofList(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_22, x_38, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec_ref(x_39);
x_40 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_40;
}
else
{
lean_dec_ref(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
block_52:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8));
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Nat_reprFast(x_42);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_21 = lean_box(0);
x_22 = x_43;
x_23 = x_46;
x_24 = x_45;
x_25 = x_51;
goto block_41;
}
}
else
{
lean_object* x_680; lean_object* x_681; uint8_t x_682; uint8_t x_687; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_680 = lean_ctor_get(x_19, 0);
x_687 = !lean_is_exclusive(x_19);
if (x_687 == 0)
{
x_681 = x_19;
x_682 = x_687;
goto block_686;
}
else
{
lean_inc(x_680);
lean_dec(x_19);
x_681 = lean_box(0);
x_682 = x_687;
goto block_686;
}
block_686:
{
lean_object* x_683; 
if (x_682 == 0)
{
x_683 = x_681;
goto block_684;
}
else
{
lean_object* x_685; 
x_685 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_685, 0, x_680);
x_683 = x_685;
goto block_684;
}
block_684:
{
return x_683;
}
}
}
}
else
{
lean_object* x_688; lean_object* x_689; uint8_t x_690; uint8_t x_695; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_688 = lean_ctor_get(x_17, 0);
x_695 = !lean_is_exclusive(x_17);
if (x_695 == 0)
{
x_689 = x_17;
x_690 = x_695;
goto block_694;
}
else
{
lean_inc(x_688);
lean_dec(x_17);
x_689 = lean_box(0);
x_690 = x_695;
goto block_694;
}
block_694:
{
lean_object* x_691; 
if (x_690 == 0)
{
x_691 = x_689;
goto block_692;
}
else
{
lean_object* x_693; 
x_693 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_693, 0, x_688);
x_691 = x_693;
goto block_692;
}
block_692:
{
return x_691;
}
}
}
}
else
{
lean_object* x_696; lean_object* x_697; uint8_t x_698; uint8_t x_703; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_696 = lean_ctor_get(x_15, 0);
x_703 = !lean_is_exclusive(x_15);
if (x_703 == 0)
{
x_697 = x_15;
x_698 = x_703;
goto block_702;
}
else
{
lean_inc(x_696);
lean_dec(x_15);
x_697 = lean_box(0);
x_698 = x_703;
goto block_702;
}
block_702:
{
lean_object* x_699; 
if (x_698 == 0)
{
x_699 = x_697;
goto block_700;
}
else
{
lean_object* x_701; 
x_701 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_701, 0, x_696);
x_699 = x_701;
goto block_700;
}
block_700:
{
return x_699;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_16 = lean_ctor_get(x_14, 30);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
x_18 = x_15;
x_19 = x_29;
goto block_28;
}
else
{
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_17, 35);
lean_inc_ref(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_16, 2);
lean_inc(x_21);
lean_dec_ref(x_16);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_box(x_23);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_24);
x_25 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
x_31 = x_15;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_38 = lean_ctor_get(x_13, 0);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
x_39 = x_13;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_13);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_hasAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_86; 
x_15 = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0);
x_16 = l_ReaderT_instMonad___redArg(x_15);
x_17 = lean_ctor_get(x_16, 0);
x_86 = !lean_is_exclusive(x_16);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_16, 1);
lean_dec(x_87);
x_18 = x_16;
x_19 = x_86;
goto block_85;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_83; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_83 = !lean_is_exclusive(x_17);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_17, 1);
lean_dec(x_84);
x_24 = x_17;
x_25 = x_83;
goto block_82;
}
else
{
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1));
x_27 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2));
lean_inc_ref(x_20);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_28, 0, x_20);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_31, 0, x_23);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_32, 0, x_22);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_33, 0, x_21);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_31);
lean_ctor_set(x_24, 3, x_32);
lean_ctor_set(x_24, 2, x_33);
lean_ctor_set(x_24, 1, x_26);
lean_ctor_set(x_24, 0, x_30);
x_34 = x_24;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_30);
lean_ctor_set(x_81, 1, x_26);
lean_ctor_set(x_81, 2, x_33);
lean_ctor_set(x_81, 3, x_32);
lean_ctor_set(x_81, 4, x_31);
x_34 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_35; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_34);
x_35 = x_18;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_34);
lean_ctor_set(x_79, 1, x_27);
x_35 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_76; 
x_36 = l_ReaderT_instMonad___redArg(x_35);
x_37 = lean_ctor_get(x_36, 0);
x_76 = !lean_is_exclusive(x_36);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_36, 1);
lean_dec(x_77);
x_38 = x_36;
x_39 = x_76;
goto block_75;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_73; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 2);
x_42 = lean_ctor_get(x_37, 3);
x_43 = lean_ctor_get(x_37, 4);
x_73 = !lean_is_exclusive(x_37);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_37, 1);
lean_dec(x_74);
x_44 = x_37;
x_45 = x_73;
goto block_72;
}
else
{
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_37);
x_44 = lean_box(0);
x_45 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3));
x_47 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4));
lean_inc_ref(x_40);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_48, 0, x_40);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_49, 0, x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_51, 0, x_43);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_52, 0, x_42);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_53, 0, x_41);
if (x_45 == 0)
{
lean_ctor_set(x_44, 4, x_51);
lean_ctor_set(x_44, 3, x_52);
lean_ctor_set(x_44, 2, x_53);
lean_ctor_set(x_44, 1, x_46);
lean_ctor_set(x_44, 0, x_50);
x_54 = x_44;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_50);
lean_ctor_set(x_71, 1, x_46);
lean_ctor_set(x_71, 2, x_53);
lean_ctor_set(x_71, 3, x_52);
lean_ctor_set(x_71, 4, x_51);
x_54 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_55; 
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_47);
lean_ctor_set(x_38, 0, x_54);
x_55 = x_38;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_54);
lean_ctor_set(x_69, 1, x_47);
x_55 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = l_ReaderT_instMonad___redArg(x_55);
x_57 = l_ReaderT_instMonad___redArg(x_56);
x_58 = l_ReaderT_instMonad___redArg(x_57);
x_59 = l_ReaderT_instMonad___redArg(x_58);
x_60 = l_ReaderT_instMonad___redArg(x_59);
x_61 = l_ReaderT_instMonad___redArg(x_60);
x_62 = l_ReaderT_instMonad___redArg(x_61);
x_63 = l_ReaderT_instMonad___redArg(x_62);
x_64 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_13(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_67;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_105; 
x_15 = lean_st_ref_get(x_2);
x_16 = lean_ctor_get(x_15, 0);
x_105 = !lean_is_exclusive(x_15);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_15, 1);
lean_dec(x_106);
x_17 = x_15;
x_18 = x_105;
goto block_104;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_92; uint8_t x_93; 
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_box(0);
x_76 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_nat_dec_lt(x_92, x_19);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__5);
x_95 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_94, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_95) == 0)
{
lean_dec_ref(x_95);
x_77 = x_2;
x_78 = x_10;
x_79 = x_11;
x_80 = x_12;
x_81 = x_13;
x_82 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
lean_dec(x_19);
lean_del_object(x_17);
x_96 = lean_ctor_get(x_95, 0);
x_103 = !lean_is_exclusive(x_95);
if (x_103 == 0)
{
x_97 = x_95;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
}
else
{
x_77 = x_2;
x_78 = x_10;
x_79 = x_11;
x_80 = x_12;
x_81 = x_13;
x_82 = lean_box(0);
goto block_91;
}
block_75:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_74; 
x_28 = lean_st_ref_take(x_23);
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get(x_28, 1);
x_74 = !lean_is_exclusive(x_28);
if (x_74 == 0)
{
x_31 = x_28;
x_32 = x_74;
goto block_73;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_PersistentArray_pop___redArg(x_29);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_33);
x_34 = x_31;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_33);
lean_ctor_set(x_72, 1, x_30);
x_34 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_st_ref_set(x_23, x_34);
x_36 = lean_ctor_get(x_27, 1);
x_37 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_36, x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_inc(x_36);
lean_dec_ref(x_27);
x_38 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1));
x_39 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_38, x_26);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_dec(x_36);
lean_del_object(x_17);
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__3);
x_44 = l_Lean_MessageData_ofName(x_36);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_44);
lean_ctor_set(x_17, 0, x_43);
x_45 = x_17;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_44);
x_45 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_46; 
x_46 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_38, x_45, x_25, x_21, x_26, x_22);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
x_48 = lean_ctor_get(x_46, 0);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
x_49 = x_46;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_36);
lean_del_object(x_17);
x_58 = lean_ctor_get(x_39, 0);
x_65 = !lean_is_exclusive(x_39);
if (x_65 == 0)
{
x_59 = x_39;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_39);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_27);
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_20);
lean_ctor_set(x_17, 0, x_66);
x_67 = x_17;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_20);
x_67 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
}
block_91:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_st_ref_get(x_77);
x_84 = lean_ctor_get(x_83, 0);
lean_inc_ref(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get(x_84, 2);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_19, x_86);
lean_dec(x_19);
x_88 = lean_nat_dec_lt(x_87, x_85);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_87);
lean_dec_ref(x_84);
x_89 = l_outOfBounds___redArg(x_76);
x_21 = x_79;
x_22 = x_81;
x_23 = x_77;
x_24 = lean_box(0);
x_25 = x_78;
x_26 = x_80;
x_27 = x_89;
goto block_75;
}
else
{
lean_object* x_90; 
x_90 = l_Lean_PersistentArray_get_x21___redArg(x_76, x_84, x_87);
lean_dec(x_87);
x_21 = x_79;
x_22 = x_81;
x_23 = x_77;
x_24 = lean_box(0);
x_25 = x_78;
x_26 = x_80;
x_27 = x_90;
goto block_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(224u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_27; 
x_16 = lean_ctor_get(x_15, 0);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
x_17 = x_15;
x_18 = x_27;
goto block_26;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_del_object(x_17);
x_20 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3);
x_21 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_22);
x_23 = x_17;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_15, 0);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
x_29 = x_15;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_2, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_24; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_3, 7);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 6);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 5);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 4);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_3, 0);
lean_dec(x_32);
x_14 = x_3;
x_15 = x_24;
goto block_23;
}
else
{
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_16);
lean_dec_ref(x_2);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_4, x_1, x_17);
x_19 = lean_array_fset(x_18, x_1, x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_19);
x_20 = x_14;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set(x_22, 3, x_7);
lean_ctor_set(x_22, 4, x_8);
lean_ctor_set(x_22, 5, x_9);
lean_ctor_set(x_22, 6, x_10);
lean_ctor_set(x_22, 7, x_11);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
x_6 = x_1;
x_7 = x_13;
goto block_12;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_8; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
x_8 = x_6;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_2);
x_8 = x_11;
goto block_10;
}
block_10:
{
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(x_1, x_4);
x_7 = lean_array_push(x_6, x_3);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_660; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_660 = !lean_is_exclusive(x_2);
if (x_660 == 0)
{
lean_object* x_661; 
x_661 = lean_ctor_get(x_2, 0);
lean_dec(x_661);
x_7 = x_2;
x_8 = x_660;
goto block_659;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_660;
goto block_659;
}
block_659:
{
uint8_t x_9; 
x_9 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_9) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_1, x_5);
x_11 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_mul(x_18, x_12);
x_20 = lean_nat_dec_lt(x_19, x_13);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
x_21 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_22 = lean_nat_add(x_21, x_13);
lean_dec(x_21);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_22);
x_23 = x_7;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_10);
lean_ctor_set(x_25, 4, x_6);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_89; 
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_6, 4);
lean_dec(x_90);
x_91 = lean_ctor_get(x_6, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_6, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_6, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_6, 0);
lean_dec(x_94);
x_26 = x_6;
x_27 = x_89;
goto block_88;
}
else
{
lean_dec(x_6);
x_26 = lean_box(0);
x_27 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get(x_16, 3);
x_32 = lean_ctor_get(x_16, 4);
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_34, x_33);
x_36 = lean_nat_dec_lt(x_28, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_64; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_16, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_16, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_16, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_16, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_16, 0);
lean_dec(x_69);
x_37 = x_16;
x_38 = x_64;
goto block_63;
}
else
{
lean_dec(x_16);
x_37 = lean_box(0);
x_38 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; 
x_39 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_40 = lean_nat_add(x_39, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_31, 0);
lean_inc(x_61);
x_52 = x_61;
goto block_60;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_52 = x_62;
goto block_60;
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_nat_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_17);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_44);
x_45 = x_37;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_14);
lean_ctor_set(x_50, 2, x_15);
lean_ctor_set(x_50, 3, x_32);
lean_ctor_set(x_50, 4, x_17);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_45);
lean_ctor_set(x_26, 3, x_42);
lean_ctor_set(x_26, 2, x_30);
lean_ctor_set(x_26, 1, x_29);
lean_ctor_set(x_26, 0, x_40);
x_46 = x_26;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
block_60:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_add(x_39, x_52);
lean_dec(x_52);
lean_dec(x_39);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_31);
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_53);
x_54 = x_7;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_3);
lean_ctor_set(x_59, 2, x_4);
lean_ctor_set(x_59, 3, x_10);
lean_ctor_set(x_59, 4, x_31);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
x_55 = lean_nat_add(x_11, x_33);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
x_41 = x_55;
x_42 = x_54;
x_43 = x_56;
goto block_51;
}
else
{
lean_object* x_57; 
x_57 = lean_unsigned_to_nat(0u);
x_41 = x_55;
x_42 = x_54;
x_43 = x_57;
goto block_51;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_del_object(x_7);
x_70 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_71 = lean_nat_add(x_70, x_13);
lean_dec(x_13);
x_72 = lean_nat_add(x_70, x_28);
lean_dec(x_70);
lean_inc_ref(x_10);
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_16);
lean_ctor_set(x_26, 3, x_10);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 0, x_72);
x_73 = x_26;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_3);
lean_ctor_set(x_87, 2, x_4);
lean_ctor_set(x_87, 3, x_10);
lean_ctor_set(x_87, 4, x_16);
x_73 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_80 = !lean_is_exclusive(x_10);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_10, 4);
lean_dec(x_81);
x_82 = lean_ctor_get(x_10, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_10, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_10, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_10, 0);
lean_dec(x_85);
x_74 = x_10;
x_75 = x_80;
goto block_79;
}
else
{
lean_dec(x_10);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 4, x_17);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 2, x_15);
lean_ctor_set(x_74, 1, x_14);
lean_ctor_set(x_74, 0, x_71);
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_14);
lean_ctor_set(x_78, 2, x_15);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_17);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_10, 0);
lean_inc(x_95);
x_96 = lean_nat_add(x_11, x_95);
lean_dec(x_95);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_96);
x_97 = x_7;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_3);
lean_ctor_set(x_99, 2, x_4);
lean_ctor_set(x_99, 3, x_10);
lean_ctor_set(x_99, 4, x_6);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_6, 3);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_6, 4);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_117; 
x_102 = lean_ctor_get(x_6, 0);
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
x_117 = !lean_is_exclusive(x_6);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_6, 4);
lean_dec(x_118);
x_119 = lean_ctor_get(x_6, 3);
lean_dec(x_119);
x_105 = x_6;
x_106 = x_117;
goto block_116;
}
else
{
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
x_105 = lean_box(0);
x_106 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_100, 0);
x_108 = lean_nat_add(x_11, x_102);
lean_dec(x_102);
x_109 = lean_nat_add(x_11, x_107);
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_100);
lean_ctor_set(x_105, 3, x_10);
lean_ctor_set(x_105, 2, x_4);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 0, x_109);
x_110 = x_105;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 2, x_4);
lean_ctor_set(x_115, 3, x_10);
lean_ctor_set(x_115, 4, x_100);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_101);
lean_ctor_set(x_7, 3, x_110);
lean_ctor_set(x_7, 2, x_104);
lean_ctor_set(x_7, 1, x_103);
lean_ctor_set(x_7, 0, x_108);
x_111 = x_7;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_103);
lean_ctor_set(x_113, 2, x_104);
lean_ctor_set(x_113, 3, x_110);
lean_ctor_set(x_113, 4, x_101);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_144; 
x_120 = lean_ctor_get(x_6, 1);
x_121 = lean_ctor_get(x_6, 2);
x_144 = !lean_is_exclusive(x_6);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_6, 4);
lean_dec(x_145);
x_146 = lean_ctor_get(x_6, 3);
lean_dec(x_146);
x_147 = lean_ctor_get(x_6, 0);
lean_dec(x_147);
x_122 = x_6;
x_123 = x_144;
goto block_143;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_6);
x_122 = lean_box(0);
x_123 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_139; 
x_124 = lean_ctor_get(x_100, 1);
x_125 = lean_ctor_get(x_100, 2);
x_139 = !lean_is_exclusive(x_100);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_100, 4);
lean_dec(x_140);
x_141 = lean_ctor_get(x_100, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_100, 0);
lean_dec(x_142);
x_126 = x_100;
x_127 = x_139;
goto block_138;
}
else
{
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_100);
x_126 = lean_box(0);
x_127 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_unsigned_to_nat(3u);
if (x_127 == 0)
{
lean_ctor_set(x_126, 4, x_101);
lean_ctor_set(x_126, 3, x_101);
lean_ctor_set(x_126, 2, x_4);
lean_ctor_set(x_126, 1, x_3);
lean_ctor_set(x_126, 0, x_11);
x_129 = x_126;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_11);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_4);
lean_ctor_set(x_137, 3, x_101);
lean_ctor_set(x_137, 4, x_101);
x_129 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_130; 
if (x_123 == 0)
{
lean_ctor_set(x_122, 3, x_101);
lean_ctor_set(x_122, 0, x_11);
x_130 = x_122;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_11);
lean_ctor_set(x_135, 1, x_120);
lean_ctor_set(x_135, 2, x_121);
lean_ctor_set(x_135, 3, x_101);
lean_ctor_set(x_135, 4, x_101);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_130);
lean_ctor_set(x_7, 3, x_129);
lean_ctor_set(x_7, 2, x_125);
lean_ctor_set(x_7, 1, x_124);
lean_ctor_set(x_7, 0, x_128);
x_131 = x_7;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_124);
lean_ctor_set(x_133, 2, x_125);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
}
}
else
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_6, 4);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_161; 
x_149 = lean_ctor_get(x_6, 1);
x_150 = lean_ctor_get(x_6, 2);
x_161 = !lean_is_exclusive(x_6);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_6, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_6, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_6, 0);
lean_dec(x_164);
x_151 = x_6;
x_152 = x_161;
goto block_160;
}
else
{
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_6);
x_151 = lean_box(0);
x_152 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_unsigned_to_nat(3u);
if (x_152 == 0)
{
lean_ctor_set(x_151, 4, x_100);
lean_ctor_set(x_151, 2, x_4);
lean_ctor_set(x_151, 1, x_3);
lean_ctor_set(x_151, 0, x_11);
x_154 = x_151;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_11);
lean_ctor_set(x_159, 1, x_3);
lean_ctor_set(x_159, 2, x_4);
lean_ctor_set(x_159, 3, x_100);
lean_ctor_set(x_159, 4, x_100);
x_154 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_155; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_148);
lean_ctor_set(x_7, 3, x_154);
lean_ctor_set(x_7, 2, x_150);
lean_ctor_set(x_7, 1, x_149);
lean_ctor_set(x_7, 0, x_153);
x_155 = x_7;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_150);
lean_ctor_set(x_157, 3, x_154);
lean_ctor_set(x_157, 4, x_148);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_178; 
x_165 = lean_ctor_get(x_6, 0);
x_166 = lean_ctor_get(x_6, 1);
x_167 = lean_ctor_get(x_6, 2);
x_178 = !lean_is_exclusive(x_6);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_6, 4);
lean_dec(x_179);
x_180 = lean_ctor_get(x_6, 3);
lean_dec(x_180);
x_168 = x_6;
x_169 = x_178;
goto block_177;
}
else
{
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_6);
x_168 = lean_box(0);
x_169 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_170; 
if (x_169 == 0)
{
lean_ctor_set(x_168, 3, x_148);
x_170 = x_168;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_165);
lean_ctor_set(x_176, 1, x_166);
lean_ctor_set(x_176, 2, x_167);
lean_ctor_set(x_176, 3, x_148);
lean_ctor_set(x_176, 4, x_148);
x_170 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_170);
lean_ctor_set(x_7, 3, x_148);
lean_ctor_set(x_7, 0, x_171);
x_172 = x_7;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_3);
lean_ctor_set(x_174, 2, x_4);
lean_ctor_set(x_174, 3, x_148);
lean_ctor_set(x_174, 4, x_170);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
}
}
else
{
lean_object* x_181; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 0, x_11);
x_181 = x_7;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_183, 0, x_11);
lean_ctor_set(x_183, 1, x_3);
lean_ctor_set(x_183, 2, x_4);
lean_ctor_set(x_183, 3, x_6);
lean_ctor_set(x_183, 4, x_6);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
case 1:
{
lean_del_object(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_184 = lean_ctor_get(x_5, 0);
x_185 = lean_ctor_get(x_5, 1);
x_186 = lean_ctor_get(x_5, 2);
x_187 = lean_ctor_get(x_5, 3);
x_188 = lean_ctor_get(x_5, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_6, 0);
x_190 = lean_ctor_get(x_6, 1);
x_191 = lean_ctor_get(x_6, 2);
x_192 = lean_ctor_get(x_6, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_6, 4);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_dec_lt(x_184, x_189);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; uint8_t x_331; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_331 = !lean_is_exclusive(x_5);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_5, 4);
lean_dec(x_332);
x_333 = lean_ctor_get(x_5, 3);
lean_dec(x_333);
x_334 = lean_ctor_get(x_5, 2);
lean_dec(x_334);
x_335 = lean_ctor_get(x_5, 1);
lean_dec(x_335);
x_336 = lean_ctor_get(x_5, 0);
lean_dec(x_336);
x_196 = x_5;
x_197 = x_331;
goto block_330;
}
else
{
lean_dec(x_5);
x_196 = lean_box(0);
x_197 = x_331;
goto block_330;
}
block_330:
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_185, x_186, x_187, x_188);
x_199 = lean_ctor_get(x_198, 2);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec_ref(x_198);
x_202 = lean_ctor_get(x_199, 0);
x_203 = lean_unsigned_to_nat(3u);
x_204 = lean_nat_mul(x_203, x_202);
x_205 = lean_nat_dec_lt(x_204, x_189);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_192);
x_206 = lean_nat_add(x_194, x_202);
x_207 = lean_nat_add(x_206, x_189);
lean_dec(x_206);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_6);
lean_ctor_set(x_196, 3, x_199);
lean_ctor_set(x_196, 2, x_201);
lean_ctor_set(x_196, 1, x_200);
lean_ctor_set(x_196, 0, x_207);
x_208 = x_196;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_200);
lean_ctor_set(x_210, 2, x_201);
lean_ctor_set(x_210, 3, x_199);
lean_ctor_set(x_210, 4, x_6);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
else
{
lean_object* x_211; uint8_t x_212; uint8_t x_265; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_265 = !lean_is_exclusive(x_6);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_6, 4);
lean_dec(x_266);
x_267 = lean_ctor_get(x_6, 3);
lean_dec(x_267);
x_268 = lean_ctor_get(x_6, 2);
lean_dec(x_268);
x_269 = lean_ctor_get(x_6, 1);
lean_dec(x_269);
x_270 = lean_ctor_get(x_6, 0);
lean_dec(x_270);
x_211 = x_6;
x_212 = x_265;
goto block_264;
}
else
{
lean_dec(x_6);
x_211 = lean_box(0);
x_212 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_213 = lean_ctor_get(x_192, 0);
x_214 = lean_ctor_get(x_192, 1);
x_215 = lean_ctor_get(x_192, 2);
x_216 = lean_ctor_get(x_192, 3);
x_217 = lean_ctor_get(x_192, 4);
x_218 = lean_ctor_get(x_193, 0);
x_219 = lean_unsigned_to_nat(2u);
x_220 = lean_nat_mul(x_219, x_218);
x_221 = lean_nat_dec_lt(x_213, x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; uint8_t x_249; 
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
x_249 = !lean_is_exclusive(x_192);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_192, 4);
lean_dec(x_250);
x_251 = lean_ctor_get(x_192, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_192, 2);
lean_dec(x_252);
x_253 = lean_ctor_get(x_192, 1);
lean_dec(x_253);
x_254 = lean_ctor_get(x_192, 0);
lean_dec(x_254);
x_222 = x_192;
x_223 = x_249;
goto block_248;
}
else
{
lean_dec(x_192);
x_222 = lean_box(0);
x_223 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_237; 
x_224 = lean_nat_add(x_194, x_202);
x_225 = lean_nat_add(x_224, x_189);
lean_dec(x_189);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_216, 0);
lean_inc(x_246);
x_237 = x_246;
goto block_245;
}
else
{
lean_object* x_247; 
x_247 = lean_unsigned_to_nat(0u);
x_237 = x_247;
goto block_245;
}
block_236:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_nat_add(x_227, x_228);
lean_dec(x_228);
lean_dec(x_227);
if (x_223 == 0)
{
lean_ctor_set(x_222, 4, x_193);
lean_ctor_set(x_222, 3, x_217);
lean_ctor_set(x_222, 2, x_191);
lean_ctor_set(x_222, 1, x_190);
lean_ctor_set(x_222, 0, x_229);
x_230 = x_222;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_190);
lean_ctor_set(x_235, 2, x_191);
lean_ctor_set(x_235, 3, x_217);
lean_ctor_set(x_235, 4, x_193);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
if (x_212 == 0)
{
lean_ctor_set(x_211, 4, x_230);
lean_ctor_set(x_211, 3, x_226);
lean_ctor_set(x_211, 2, x_215);
lean_ctor_set(x_211, 1, x_214);
lean_ctor_set(x_211, 0, x_225);
x_231 = x_211;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_214);
lean_ctor_set(x_233, 2, x_215);
lean_ctor_set(x_233, 3, x_226);
lean_ctor_set(x_233, 4, x_230);
x_231 = x_233;
goto block_232;
}
block_232:
{
return x_231;
}
}
}
block_245:
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_nat_add(x_224, x_237);
lean_dec(x_237);
lean_dec(x_224);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_216);
lean_ctor_set(x_196, 3, x_199);
lean_ctor_set(x_196, 2, x_201);
lean_ctor_set(x_196, 1, x_200);
lean_ctor_set(x_196, 0, x_238);
x_239 = x_196;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_244, 0, x_238);
lean_ctor_set(x_244, 1, x_200);
lean_ctor_set(x_244, 2, x_201);
lean_ctor_set(x_244, 3, x_199);
lean_ctor_set(x_244, 4, x_216);
x_239 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_240; 
x_240 = lean_nat_add(x_194, x_218);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_217, 0);
lean_inc(x_241);
x_226 = x_239;
x_227 = x_240;
x_228 = x_241;
goto block_236;
}
else
{
lean_object* x_242; 
x_242 = lean_unsigned_to_nat(0u);
x_226 = x_239;
x_227 = x_240;
x_228 = x_242;
goto block_236;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_nat_add(x_194, x_202);
x_256 = lean_nat_add(x_255, x_189);
lean_dec(x_189);
x_257 = lean_nat_add(x_255, x_213);
lean_dec(x_255);
if (x_212 == 0)
{
lean_ctor_set(x_211, 4, x_192);
lean_ctor_set(x_211, 3, x_199);
lean_ctor_set(x_211, 2, x_201);
lean_ctor_set(x_211, 1, x_200);
lean_ctor_set(x_211, 0, x_257);
x_258 = x_211;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_200);
lean_ctor_set(x_263, 2, x_201);
lean_ctor_set(x_263, 3, x_199);
lean_ctor_set(x_263, 4, x_192);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_258);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_256);
x_259 = x_196;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_190);
lean_ctor_set(x_261, 2, x_191);
lean_ctor_set(x_261, 3, x_258);
lean_ctor_set(x_261, 4, x_193);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
}
}
else
{
lean_object* x_271; uint8_t x_272; uint8_t x_324; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_324 = !lean_is_exclusive(x_6);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_6, 4);
lean_dec(x_325);
x_326 = lean_ctor_get(x_6, 3);
lean_dec(x_326);
x_327 = lean_ctor_get(x_6, 2);
lean_dec(x_327);
x_328 = lean_ctor_get(x_6, 1);
lean_dec(x_328);
x_329 = lean_ctor_get(x_6, 0);
lean_dec(x_329);
x_271 = x_6;
x_272 = x_324;
goto block_323;
}
else
{
lean_dec(x_6);
x_271 = lean_box(0);
x_272 = x_324;
goto block_323;
}
block_323:
{
if (lean_obj_tag(x_192) == 0)
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_198, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_198, 1);
lean_inc(x_274);
lean_dec_ref(x_198);
x_275 = lean_ctor_get(x_192, 0);
x_276 = lean_nat_add(x_194, x_189);
lean_dec(x_189);
x_277 = lean_nat_add(x_194, x_275);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_192);
lean_ctor_set(x_271, 3, x_199);
lean_ctor_set(x_271, 2, x_274);
lean_ctor_set(x_271, 1, x_273);
lean_ctor_set(x_271, 0, x_277);
x_278 = x_271;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set(x_283, 2, x_274);
lean_ctor_set(x_283, 3, x_199);
lean_ctor_set(x_283, 4, x_192);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_278);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_276);
x_279 = x_196;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_190);
lean_ctor_set(x_281, 2, x_191);
lean_ctor_set(x_281, 3, x_278);
lean_ctor_set(x_281, 4, x_193);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_301; 
lean_dec(x_189);
x_284 = lean_ctor_get(x_198, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_198, 1);
lean_inc(x_285);
lean_dec_ref(x_198);
x_286 = lean_ctor_get(x_192, 1);
x_287 = lean_ctor_get(x_192, 2);
x_301 = !lean_is_exclusive(x_192);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_192, 4);
lean_dec(x_302);
x_303 = lean_ctor_get(x_192, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_192, 0);
lean_dec(x_304);
x_288 = x_192;
x_289 = x_301;
goto block_300;
}
else
{
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_192);
x_288 = lean_box(0);
x_289 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_unsigned_to_nat(3u);
if (x_289 == 0)
{
lean_ctor_set(x_288, 4, x_193);
lean_ctor_set(x_288, 3, x_193);
lean_ctor_set(x_288, 2, x_285);
lean_ctor_set(x_288, 1, x_284);
lean_ctor_set(x_288, 0, x_194);
x_291 = x_288;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_194);
lean_ctor_set(x_299, 1, x_284);
lean_ctor_set(x_299, 2, x_285);
lean_ctor_set(x_299, 3, x_193);
lean_ctor_set(x_299, 4, x_193);
x_291 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_292; 
if (x_272 == 0)
{
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 0, x_194);
x_292 = x_271;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_297, 0, x_194);
lean_ctor_set(x_297, 1, x_190);
lean_ctor_set(x_297, 2, x_191);
lean_ctor_set(x_297, 3, x_193);
lean_ctor_set(x_297, 4, x_193);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_292);
lean_ctor_set(x_196, 3, x_291);
lean_ctor_set(x_196, 2, x_287);
lean_ctor_set(x_196, 1, x_286);
lean_ctor_set(x_196, 0, x_290);
x_293 = x_196;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_290);
lean_ctor_set(x_295, 1, x_286);
lean_ctor_set(x_295, 2, x_287);
lean_ctor_set(x_295, 3, x_291);
lean_ctor_set(x_295, 4, x_292);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_189);
x_305 = lean_ctor_get(x_198, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_198, 1);
lean_inc(x_306);
lean_dec_ref(x_198);
x_307 = lean_unsigned_to_nat(3u);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_192);
lean_ctor_set(x_271, 2, x_306);
lean_ctor_set(x_271, 1, x_305);
lean_ctor_set(x_271, 0, x_194);
x_308 = x_271;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_194);
lean_ctor_set(x_313, 1, x_305);
lean_ctor_set(x_313, 2, x_306);
lean_ctor_set(x_313, 3, x_192);
lean_ctor_set(x_313, 4, x_192);
x_308 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_309; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_308);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_307);
x_309 = x_196;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_190);
lean_ctor_set(x_311, 2, x_191);
lean_ctor_set(x_311, 3, x_308);
lean_ctor_set(x_311, 4, x_193);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_198, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_198, 1);
lean_inc(x_315);
lean_dec_ref(x_198);
if (x_272 == 0)
{
lean_ctor_set(x_271, 3, x_193);
x_316 = x_271;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_322, 0, x_189);
lean_ctor_set(x_322, 1, x_190);
lean_ctor_set(x_322, 2, x_191);
lean_ctor_set(x_322, 3, x_193);
lean_ctor_set(x_322, 4, x_193);
x_316 = x_322;
goto block_321;
}
block_321:
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_unsigned_to_nat(2u);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_316);
lean_ctor_set(x_196, 3, x_193);
lean_ctor_set(x_196, 2, x_315);
lean_ctor_set(x_196, 1, x_314);
lean_ctor_set(x_196, 0, x_317);
x_318 = x_196;
goto block_319;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_314);
lean_ctor_set(x_320, 2, x_315);
lean_ctor_set(x_320, 3, x_193);
lean_ctor_set(x_320, 4, x_316);
x_318 = x_320;
goto block_319;
}
block_319:
{
return x_318;
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
lean_object* x_337; uint8_t x_338; uint8_t x_489; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
x_489 = !lean_is_exclusive(x_6);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_490 = lean_ctor_get(x_6, 4);
lean_dec(x_490);
x_491 = lean_ctor_get(x_6, 3);
lean_dec(x_491);
x_492 = lean_ctor_get(x_6, 2);
lean_dec(x_492);
x_493 = lean_ctor_get(x_6, 1);
lean_dec(x_493);
x_494 = lean_ctor_get(x_6, 0);
lean_dec(x_494);
x_337 = x_6;
x_338 = x_489;
goto block_488;
}
else
{
lean_dec(x_6);
x_337 = lean_box(0);
x_338 = x_489;
goto block_488;
}
block_488:
{
lean_object* x_339; lean_object* x_340; 
x_339 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_190, x_191, x_192, x_193);
x_340 = lean_ctor_get(x_339, 2);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec_ref(x_339);
x_343 = lean_ctor_get(x_340, 0);
x_344 = lean_unsigned_to_nat(3u);
x_345 = lean_nat_mul(x_344, x_343);
x_346 = lean_nat_dec_lt(x_345, x_184);
lean_dec(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_188);
x_347 = lean_nat_add(x_194, x_184);
x_348 = lean_nat_add(x_347, x_343);
lean_dec(x_347);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_5);
lean_ctor_set(x_337, 2, x_342);
lean_ctor_set(x_337, 1, x_341);
lean_ctor_set(x_337, 0, x_348);
x_349 = x_337;
goto block_350;
}
else
{
lean_object* x_351; 
x_351 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_341);
lean_ctor_set(x_351, 2, x_342);
lean_ctor_set(x_351, 3, x_5);
lean_ctor_set(x_351, 4, x_340);
x_349 = x_351;
goto block_350;
}
block_350:
{
return x_349;
}
}
else
{
lean_object* x_352; uint8_t x_353; uint8_t x_417; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_417 = !lean_is_exclusive(x_5);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_5, 4);
lean_dec(x_418);
x_419 = lean_ctor_get(x_5, 3);
lean_dec(x_419);
x_420 = lean_ctor_get(x_5, 2);
lean_dec(x_420);
x_421 = lean_ctor_get(x_5, 1);
lean_dec(x_421);
x_422 = lean_ctor_get(x_5, 0);
lean_dec(x_422);
x_352 = x_5;
x_353 = x_417;
goto block_416;
}
else
{
lean_dec(x_5);
x_352 = lean_box(0);
x_353 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_354 = lean_ctor_get(x_187, 0);
x_355 = lean_ctor_get(x_188, 0);
x_356 = lean_ctor_get(x_188, 1);
x_357 = lean_ctor_get(x_188, 2);
x_358 = lean_ctor_get(x_188, 3);
x_359 = lean_ctor_get(x_188, 4);
x_360 = lean_unsigned_to_nat(2u);
x_361 = lean_nat_mul(x_360, x_354);
x_362 = lean_nat_dec_lt(x_355, x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; uint8_t x_400; 
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_del_object(x_352);
x_400 = !lean_is_exclusive(x_188);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_188, 4);
lean_dec(x_401);
x_402 = lean_ctor_get(x_188, 3);
lean_dec(x_402);
x_403 = lean_ctor_get(x_188, 2);
lean_dec(x_403);
x_404 = lean_ctor_get(x_188, 1);
lean_dec(x_404);
x_405 = lean_ctor_get(x_188, 0);
lean_dec(x_405);
x_363 = x_188;
x_364 = x_400;
goto block_399;
}
else
{
lean_dec(x_188);
x_363 = lean_box(0);
x_364 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_387; lean_object* x_388; 
x_365 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_366 = lean_nat_add(x_365, x_343);
lean_dec(x_365);
x_387 = lean_nat_add(x_194, x_354);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_358, 0);
lean_inc(x_397);
x_388 = x_397;
goto block_396;
}
else
{
lean_object* x_398; 
x_398 = lean_unsigned_to_nat(0u);
x_388 = x_398;
goto block_396;
}
block_386:
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_nat_add(x_367, x_369);
lean_dec(x_369);
lean_dec(x_367);
lean_inc_ref(x_340);
if (x_364 == 0)
{
lean_ctor_set(x_363, 4, x_340);
lean_ctor_set(x_363, 3, x_359);
lean_ctor_set(x_363, 2, x_342);
lean_ctor_set(x_363, 1, x_341);
lean_ctor_set(x_363, 0, x_370);
x_371 = x_363;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_370);
lean_ctor_set(x_385, 1, x_341);
lean_ctor_set(x_385, 2, x_342);
lean_ctor_set(x_385, 3, x_359);
lean_ctor_set(x_385, 4, x_340);
x_371 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_372; uint8_t x_373; uint8_t x_378; 
x_378 = !lean_is_exclusive(x_340);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_379 = lean_ctor_get(x_340, 4);
lean_dec(x_379);
x_380 = lean_ctor_get(x_340, 3);
lean_dec(x_380);
x_381 = lean_ctor_get(x_340, 2);
lean_dec(x_381);
x_382 = lean_ctor_get(x_340, 1);
lean_dec(x_382);
x_383 = lean_ctor_get(x_340, 0);
lean_dec(x_383);
x_372 = x_340;
x_373 = x_378;
goto block_377;
}
else
{
lean_dec(x_340);
x_372 = lean_box(0);
x_373 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_374; 
if (x_373 == 0)
{
lean_ctor_set(x_372, 4, x_371);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set(x_372, 2, x_357);
lean_ctor_set(x_372, 1, x_356);
lean_ctor_set(x_372, 0, x_366);
x_374 = x_372;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_366);
lean_ctor_set(x_376, 1, x_356);
lean_ctor_set(x_376, 2, x_357);
lean_ctor_set(x_376, 3, x_368);
lean_ctor_set(x_376, 4, x_371);
x_374 = x_376;
goto block_375;
}
block_375:
{
return x_374;
}
}
}
}
block_396:
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_nat_add(x_387, x_388);
lean_dec(x_388);
lean_dec(x_387);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_358);
lean_ctor_set(x_337, 3, x_187);
lean_ctor_set(x_337, 2, x_186);
lean_ctor_set(x_337, 1, x_185);
lean_ctor_set(x_337, 0, x_389);
x_390 = x_337;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_395, 0, x_389);
lean_ctor_set(x_395, 1, x_185);
lean_ctor_set(x_395, 2, x_186);
lean_ctor_set(x_395, 3, x_187);
lean_ctor_set(x_395, 4, x_358);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
x_391 = lean_nat_add(x_194, x_343);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_359, 0);
lean_inc(x_392);
x_367 = x_391;
x_368 = x_390;
x_369 = x_392;
goto block_386;
}
else
{
lean_object* x_393; 
x_393 = lean_unsigned_to_nat(0u);
x_367 = x_391;
x_368 = x_390;
x_369 = x_393;
goto block_386;
}
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_406 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_407 = lean_nat_add(x_406, x_343);
lean_dec(x_406);
x_408 = lean_nat_add(x_194, x_343);
x_409 = lean_nat_add(x_408, x_355);
lean_dec(x_408);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_342);
lean_ctor_set(x_337, 1, x_341);
lean_ctor_set(x_337, 0, x_409);
x_410 = x_337;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_415, 0, x_409);
lean_ctor_set(x_415, 1, x_341);
lean_ctor_set(x_415, 2, x_342);
lean_ctor_set(x_415, 3, x_188);
lean_ctor_set(x_415, 4, x_340);
x_410 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_411; 
if (x_353 == 0)
{
lean_ctor_set(x_352, 4, x_410);
lean_ctor_set(x_352, 0, x_407);
x_411 = x_352;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_185);
lean_ctor_set(x_413, 2, x_186);
lean_ctor_set(x_413, 3, x_187);
lean_ctor_set(x_413, 4, x_410);
x_411 = x_413;
goto block_412;
}
block_412:
{
return x_411;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_423; uint8_t x_424; uint8_t x_446; 
lean_inc_ref(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_446 = !lean_is_exclusive(x_5);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_5, 4);
lean_dec(x_447);
x_448 = lean_ctor_get(x_5, 3);
lean_dec(x_448);
x_449 = lean_ctor_get(x_5, 2);
lean_dec(x_449);
x_450 = lean_ctor_get(x_5, 1);
lean_dec(x_450);
x_451 = lean_ctor_get(x_5, 0);
lean_dec(x_451);
x_423 = x_5;
x_424 = x_446;
goto block_445;
}
else
{
lean_dec(x_5);
x_423 = lean_box(0);
x_424 = x_446;
goto block_445;
}
block_445:
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_425 = lean_ctor_get(x_339, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_339, 1);
lean_inc(x_426);
lean_dec_ref(x_339);
x_427 = lean_ctor_get(x_188, 0);
x_428 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_429 = lean_nat_add(x_194, x_427);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_426);
lean_ctor_set(x_337, 1, x_425);
lean_ctor_set(x_337, 0, x_429);
x_430 = x_337;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_435, 0, x_429);
lean_ctor_set(x_435, 1, x_425);
lean_ctor_set(x_435, 2, x_426);
lean_ctor_set(x_435, 3, x_188);
lean_ctor_set(x_435, 4, x_340);
x_430 = x_435;
goto block_434;
}
block_434:
{
lean_object* x_431; 
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_430);
lean_ctor_set(x_423, 0, x_428);
x_431 = x_423;
goto block_432;
}
else
{
lean_object* x_433; 
x_433 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_433, 0, x_428);
lean_ctor_set(x_433, 1, x_185);
lean_ctor_set(x_433, 2, x_186);
lean_ctor_set(x_433, 3, x_187);
lean_ctor_set(x_433, 4, x_430);
x_431 = x_433;
goto block_432;
}
block_432:
{
return x_431;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_184);
x_436 = lean_ctor_get(x_339, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_339, 1);
lean_inc(x_437);
lean_dec_ref(x_339);
x_438 = lean_unsigned_to_nat(3u);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_188);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_437);
lean_ctor_set(x_337, 1, x_436);
lean_ctor_set(x_337, 0, x_194);
x_439 = x_337;
goto block_443;
}
else
{
lean_object* x_444; 
x_444 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_444, 0, x_194);
lean_ctor_set(x_444, 1, x_436);
lean_ctor_set(x_444, 2, x_437);
lean_ctor_set(x_444, 3, x_188);
lean_ctor_set(x_444, 4, x_188);
x_439 = x_444;
goto block_443;
}
block_443:
{
lean_object* x_440; 
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_439);
lean_ctor_set(x_423, 0, x_438);
x_440 = x_423;
goto block_441;
}
else
{
lean_object* x_442; 
x_442 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_442, 0, x_438);
lean_ctor_set(x_442, 1, x_185);
lean_ctor_set(x_442, 2, x_186);
lean_ctor_set(x_442, 3, x_187);
lean_ctor_set(x_442, 4, x_439);
x_440 = x_442;
goto block_441;
}
block_441:
{
return x_440;
}
}
}
}
}
else
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_452; uint8_t x_453; uint8_t x_476; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_476 = !lean_is_exclusive(x_5);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_477 = lean_ctor_get(x_5, 4);
lean_dec(x_477);
x_478 = lean_ctor_get(x_5, 3);
lean_dec(x_478);
x_479 = lean_ctor_get(x_5, 2);
lean_dec(x_479);
x_480 = lean_ctor_get(x_5, 1);
lean_dec(x_480);
x_481 = lean_ctor_get(x_5, 0);
lean_dec(x_481);
x_452 = x_5;
x_453 = x_476;
goto block_475;
}
else
{
lean_dec(x_5);
x_452 = lean_box(0);
x_453 = x_476;
goto block_475;
}
block_475:
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_471; 
x_454 = lean_ctor_get(x_339, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_339, 1);
lean_inc(x_455);
lean_dec_ref(x_339);
x_456 = lean_ctor_get(x_188, 1);
x_457 = lean_ctor_get(x_188, 2);
x_471 = !lean_is_exclusive(x_188);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_188, 4);
lean_dec(x_472);
x_473 = lean_ctor_get(x_188, 3);
lean_dec(x_473);
x_474 = lean_ctor_get(x_188, 0);
lean_dec(x_474);
x_458 = x_188;
x_459 = x_471;
goto block_470;
}
else
{
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_188);
x_458 = lean_box(0);
x_459 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_unsigned_to_nat(3u);
if (x_459 == 0)
{
lean_ctor_set(x_458, 4, x_187);
lean_ctor_set(x_458, 3, x_187);
lean_ctor_set(x_458, 2, x_186);
lean_ctor_set(x_458, 1, x_185);
lean_ctor_set(x_458, 0, x_194);
x_461 = x_458;
goto block_468;
}
else
{
lean_object* x_469; 
x_469 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_469, 0, x_194);
lean_ctor_set(x_469, 1, x_185);
lean_ctor_set(x_469, 2, x_186);
lean_ctor_set(x_469, 3, x_187);
lean_ctor_set(x_469, 4, x_187);
x_461 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_462; 
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_187);
lean_ctor_set(x_337, 3, x_187);
lean_ctor_set(x_337, 2, x_455);
lean_ctor_set(x_337, 1, x_454);
lean_ctor_set(x_337, 0, x_194);
x_462 = x_337;
goto block_466;
}
else
{
lean_object* x_467; 
x_467 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_467, 0, x_194);
lean_ctor_set(x_467, 1, x_454);
lean_ctor_set(x_467, 2, x_455);
lean_ctor_set(x_467, 3, x_187);
lean_ctor_set(x_467, 4, x_187);
x_462 = x_467;
goto block_466;
}
block_466:
{
lean_object* x_463; 
if (x_453 == 0)
{
lean_ctor_set(x_452, 4, x_462);
lean_ctor_set(x_452, 3, x_461);
lean_ctor_set(x_452, 2, x_457);
lean_ctor_set(x_452, 1, x_456);
lean_ctor_set(x_452, 0, x_460);
x_463 = x_452;
goto block_464;
}
else
{
lean_object* x_465; 
x_465 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_465, 0, x_460);
lean_ctor_set(x_465, 1, x_456);
lean_ctor_set(x_465, 2, x_457);
lean_ctor_set(x_465, 3, x_461);
lean_ctor_set(x_465, 4, x_462);
x_463 = x_465;
goto block_464;
}
block_464:
{
return x_463;
}
}
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = lean_ctor_get(x_339, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_339, 1);
lean_inc(x_483);
lean_dec_ref(x_339);
x_484 = lean_unsigned_to_nat(2u);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_188);
lean_ctor_set(x_337, 3, x_5);
lean_ctor_set(x_337, 2, x_483);
lean_ctor_set(x_337, 1, x_482);
lean_ctor_set(x_337, 0, x_484);
x_485 = x_337;
goto block_486;
}
else
{
lean_object* x_487; 
x_487 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_482);
lean_ctor_set(x_487, 2, x_483);
lean_ctor_set(x_487, 3, x_5);
lean_ctor_set(x_487, 4, x_188);
x_485 = x_487;
goto block_486;
}
block_486:
{
return x_485;
}
}
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_495; lean_object* x_496; 
x_495 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_1, x_6);
x_496 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_495) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_5, 0);
x_499 = lean_ctor_get(x_5, 1);
x_500 = lean_ctor_get(x_5, 2);
x_501 = lean_ctor_get(x_5, 3);
x_502 = lean_ctor_get(x_5, 4);
lean_inc(x_502);
x_503 = lean_unsigned_to_nat(3u);
x_504 = lean_nat_mul(x_503, x_497);
x_505 = lean_nat_dec_lt(x_504, x_498);
lean_dec(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_502);
x_506 = lean_nat_add(x_496, x_498);
x_507 = lean_nat_add(x_506, x_497);
lean_dec(x_497);
lean_dec(x_506);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_495);
lean_ctor_set(x_7, 0, x_507);
x_508 = x_7;
goto block_509;
}
else
{
lean_object* x_510; 
x_510 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_3);
lean_ctor_set(x_510, 2, x_4);
lean_ctor_set(x_510, 3, x_5);
lean_ctor_set(x_510, 4, x_495);
x_508 = x_510;
goto block_509;
}
block_509:
{
return x_508;
}
}
else
{
lean_object* x_511; uint8_t x_512; uint8_t x_576; 
lean_inc(x_501);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
x_576 = !lean_is_exclusive(x_5);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_577 = lean_ctor_get(x_5, 4);
lean_dec(x_577);
x_578 = lean_ctor_get(x_5, 3);
lean_dec(x_578);
x_579 = lean_ctor_get(x_5, 2);
lean_dec(x_579);
x_580 = lean_ctor_get(x_5, 1);
lean_dec(x_580);
x_581 = lean_ctor_get(x_5, 0);
lean_dec(x_581);
x_511 = x_5;
x_512 = x_576;
goto block_575;
}
else
{
lean_dec(x_5);
x_511 = lean_box(0);
x_512 = x_576;
goto block_575;
}
block_575:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_513 = lean_ctor_get(x_501, 0);
x_514 = lean_ctor_get(x_502, 0);
x_515 = lean_ctor_get(x_502, 1);
x_516 = lean_ctor_get(x_502, 2);
x_517 = lean_ctor_get(x_502, 3);
x_518 = lean_ctor_get(x_502, 4);
x_519 = lean_unsigned_to_nat(2u);
x_520 = lean_nat_mul(x_519, x_513);
x_521 = lean_nat_dec_lt(x_514, x_520);
lean_dec(x_520);
if (x_521 == 0)
{
lean_object* x_522; uint8_t x_523; uint8_t x_550; 
lean_inc(x_518);
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
x_550 = !lean_is_exclusive(x_502);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_551 = lean_ctor_get(x_502, 4);
lean_dec(x_551);
x_552 = lean_ctor_get(x_502, 3);
lean_dec(x_552);
x_553 = lean_ctor_get(x_502, 2);
lean_dec(x_553);
x_554 = lean_ctor_get(x_502, 1);
lean_dec(x_554);
x_555 = lean_ctor_get(x_502, 0);
lean_dec(x_555);
x_522 = x_502;
x_523 = x_550;
goto block_549;
}
else
{
lean_dec(x_502);
x_522 = lean_box(0);
x_523 = x_550;
goto block_549;
}
block_549:
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_537; lean_object* x_538; 
x_524 = lean_nat_add(x_496, x_498);
lean_dec(x_498);
x_525 = lean_nat_add(x_524, x_497);
lean_dec(x_524);
x_537 = lean_nat_add(x_496, x_513);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_517, 0);
lean_inc(x_547);
x_538 = x_547;
goto block_546;
}
else
{
lean_object* x_548; 
x_548 = lean_unsigned_to_nat(0u);
x_538 = x_548;
goto block_546;
}
block_536:
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_nat_add(x_526, x_528);
lean_dec(x_528);
lean_dec(x_526);
if (x_523 == 0)
{
lean_ctor_set(x_522, 4, x_495);
lean_ctor_set(x_522, 3, x_518);
lean_ctor_set(x_522, 2, x_4);
lean_ctor_set(x_522, 1, x_3);
lean_ctor_set(x_522, 0, x_529);
x_530 = x_522;
goto block_534;
}
else
{
lean_object* x_535; 
x_535 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_535, 0, x_529);
lean_ctor_set(x_535, 1, x_3);
lean_ctor_set(x_535, 2, x_4);
lean_ctor_set(x_535, 3, x_518);
lean_ctor_set(x_535, 4, x_495);
x_530 = x_535;
goto block_534;
}
block_534:
{
lean_object* x_531; 
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_530);
lean_ctor_set(x_511, 3, x_527);
lean_ctor_set(x_511, 2, x_516);
lean_ctor_set(x_511, 1, x_515);
lean_ctor_set(x_511, 0, x_525);
x_531 = x_511;
goto block_532;
}
else
{
lean_object* x_533; 
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_525);
lean_ctor_set(x_533, 1, x_515);
lean_ctor_set(x_533, 2, x_516);
lean_ctor_set(x_533, 3, x_527);
lean_ctor_set(x_533, 4, x_530);
x_531 = x_533;
goto block_532;
}
block_532:
{
return x_531;
}
}
}
block_546:
{
lean_object* x_539; lean_object* x_540; 
x_539 = lean_nat_add(x_537, x_538);
lean_dec(x_538);
lean_dec(x_537);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_517);
lean_ctor_set(x_7, 3, x_501);
lean_ctor_set(x_7, 2, x_500);
lean_ctor_set(x_7, 1, x_499);
lean_ctor_set(x_7, 0, x_539);
x_540 = x_7;
goto block_544;
}
else
{
lean_object* x_545; 
x_545 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_545, 0, x_539);
lean_ctor_set(x_545, 1, x_499);
lean_ctor_set(x_545, 2, x_500);
lean_ctor_set(x_545, 3, x_501);
lean_ctor_set(x_545, 4, x_517);
x_540 = x_545;
goto block_544;
}
block_544:
{
lean_object* x_541; 
x_541 = lean_nat_add(x_496, x_497);
lean_dec(x_497);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_542; 
x_542 = lean_ctor_get(x_518, 0);
lean_inc(x_542);
x_526 = x_541;
x_527 = x_540;
x_528 = x_542;
goto block_536;
}
else
{
lean_object* x_543; 
x_543 = lean_unsigned_to_nat(0u);
x_526 = x_541;
x_527 = x_540;
x_528 = x_543;
goto block_536;
}
}
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_del_object(x_7);
x_556 = lean_nat_add(x_496, x_498);
lean_dec(x_498);
x_557 = lean_nat_add(x_556, x_497);
lean_dec(x_556);
x_558 = lean_nat_add(x_496, x_497);
lean_dec(x_497);
x_559 = lean_nat_add(x_558, x_514);
lean_dec(x_558);
lean_inc_ref(x_495);
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_495);
lean_ctor_set(x_511, 3, x_502);
lean_ctor_set(x_511, 2, x_4);
lean_ctor_set(x_511, 1, x_3);
lean_ctor_set(x_511, 0, x_559);
x_560 = x_511;
goto block_573;
}
else
{
lean_object* x_574; 
x_574 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_574, 0, x_559);
lean_ctor_set(x_574, 1, x_3);
lean_ctor_set(x_574, 2, x_4);
lean_ctor_set(x_574, 3, x_502);
lean_ctor_set(x_574, 4, x_495);
x_560 = x_574;
goto block_573;
}
block_573:
{
lean_object* x_561; uint8_t x_562; uint8_t x_567; 
x_567 = !lean_is_exclusive(x_495);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_568 = lean_ctor_get(x_495, 4);
lean_dec(x_568);
x_569 = lean_ctor_get(x_495, 3);
lean_dec(x_569);
x_570 = lean_ctor_get(x_495, 2);
lean_dec(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_dec(x_571);
x_572 = lean_ctor_get(x_495, 0);
lean_dec(x_572);
x_561 = x_495;
x_562 = x_567;
goto block_566;
}
else
{
lean_dec(x_495);
x_561 = lean_box(0);
x_562 = x_567;
goto block_566;
}
block_566:
{
lean_object* x_563; 
if (x_562 == 0)
{
lean_ctor_set(x_561, 4, x_560);
lean_ctor_set(x_561, 3, x_501);
lean_ctor_set(x_561, 2, x_500);
lean_ctor_set(x_561, 1, x_499);
lean_ctor_set(x_561, 0, x_557);
x_563 = x_561;
goto block_564;
}
else
{
lean_object* x_565; 
x_565 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_565, 0, x_557);
lean_ctor_set(x_565, 1, x_499);
lean_ctor_set(x_565, 2, x_500);
lean_ctor_set(x_565, 3, x_501);
lean_ctor_set(x_565, 4, x_560);
x_563 = x_565;
goto block_564;
}
block_564:
{
return x_563;
}
}
}
}
}
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_495, 0);
lean_inc(x_582);
x_583 = lean_nat_add(x_496, x_582);
lean_dec(x_582);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_495);
lean_ctor_set(x_7, 0, x_583);
x_584 = x_7;
goto block_585;
}
else
{
lean_object* x_586; 
x_586 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_3);
lean_ctor_set(x_586, 2, x_4);
lean_ctor_set(x_586, 3, x_5);
lean_ctor_set(x_586, 4, x_495);
x_584 = x_586;
goto block_585;
}
block_585:
{
return x_584;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_587; 
x_587 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; 
lean_inc_ref(x_587);
x_588 = lean_ctor_get(x_5, 4);
lean_inc(x_588);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; uint8_t x_604; 
x_589 = lean_ctor_get(x_5, 0);
x_590 = lean_ctor_get(x_5, 1);
x_591 = lean_ctor_get(x_5, 2);
x_604 = !lean_is_exclusive(x_5);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_5, 4);
lean_dec(x_605);
x_606 = lean_ctor_get(x_5, 3);
lean_dec(x_606);
x_592 = x_5;
x_593 = x_604;
goto block_603;
}
else
{
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_5);
x_592 = lean_box(0);
x_593 = x_604;
goto block_603;
}
block_603:
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_594 = lean_ctor_get(x_588, 0);
x_595 = lean_nat_add(x_496, x_589);
lean_dec(x_589);
x_596 = lean_nat_add(x_496, x_594);
if (x_593 == 0)
{
lean_ctor_set(x_592, 4, x_495);
lean_ctor_set(x_592, 3, x_588);
lean_ctor_set(x_592, 2, x_4);
lean_ctor_set(x_592, 1, x_3);
lean_ctor_set(x_592, 0, x_596);
x_597 = x_592;
goto block_601;
}
else
{
lean_object* x_602; 
x_602 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_602, 0, x_596);
lean_ctor_set(x_602, 1, x_3);
lean_ctor_set(x_602, 2, x_4);
lean_ctor_set(x_602, 3, x_588);
lean_ctor_set(x_602, 4, x_495);
x_597 = x_602;
goto block_601;
}
block_601:
{
lean_object* x_598; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_597);
lean_ctor_set(x_7, 3, x_587);
lean_ctor_set(x_7, 2, x_591);
lean_ctor_set(x_7, 1, x_590);
lean_ctor_set(x_7, 0, x_595);
x_598 = x_7;
goto block_599;
}
else
{
lean_object* x_600; 
x_600 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_600, 0, x_595);
lean_ctor_set(x_600, 1, x_590);
lean_ctor_set(x_600, 2, x_591);
lean_ctor_set(x_600, 3, x_587);
lean_ctor_set(x_600, 4, x_597);
x_598 = x_600;
goto block_599;
}
block_599:
{
return x_598;
}
}
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; uint8_t x_619; 
x_607 = lean_ctor_get(x_5, 1);
x_608 = lean_ctor_get(x_5, 2);
x_619 = !lean_is_exclusive(x_5);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_5, 4);
lean_dec(x_620);
x_621 = lean_ctor_get(x_5, 3);
lean_dec(x_621);
x_622 = lean_ctor_get(x_5, 0);
lean_dec(x_622);
x_609 = x_5;
x_610 = x_619;
goto block_618;
}
else
{
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_5);
x_609 = lean_box(0);
x_610 = x_619;
goto block_618;
}
block_618:
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_unsigned_to_nat(3u);
if (x_610 == 0)
{
lean_ctor_set(x_609, 3, x_588);
lean_ctor_set(x_609, 2, x_4);
lean_ctor_set(x_609, 1, x_3);
lean_ctor_set(x_609, 0, x_496);
x_612 = x_609;
goto block_616;
}
else
{
lean_object* x_617; 
x_617 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_617, 0, x_496);
lean_ctor_set(x_617, 1, x_3);
lean_ctor_set(x_617, 2, x_4);
lean_ctor_set(x_617, 3, x_588);
lean_ctor_set(x_617, 4, x_588);
x_612 = x_617;
goto block_616;
}
block_616:
{
lean_object* x_613; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_612);
lean_ctor_set(x_7, 3, x_587);
lean_ctor_set(x_7, 2, x_608);
lean_ctor_set(x_7, 1, x_607);
lean_ctor_set(x_7, 0, x_611);
x_613 = x_7;
goto block_614;
}
else
{
lean_object* x_615; 
x_615 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_615, 0, x_611);
lean_ctor_set(x_615, 1, x_607);
lean_ctor_set(x_615, 2, x_608);
lean_ctor_set(x_615, 3, x_587);
lean_ctor_set(x_615, 4, x_612);
x_613 = x_615;
goto block_614;
}
block_614:
{
return x_613;
}
}
}
}
}
else
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_5, 4);
lean_inc(x_623);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; uint8_t x_648; 
lean_inc(x_587);
x_624 = lean_ctor_get(x_5, 1);
x_625 = lean_ctor_get(x_5, 2);
x_648 = !lean_is_exclusive(x_5);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_5, 4);
lean_dec(x_649);
x_650 = lean_ctor_get(x_5, 3);
lean_dec(x_650);
x_651 = lean_ctor_get(x_5, 0);
lean_dec(x_651);
x_626 = x_5;
x_627 = x_648;
goto block_647;
}
else
{
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_5);
x_626 = lean_box(0);
x_627 = x_648;
goto block_647;
}
block_647:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_643; 
x_628 = lean_ctor_get(x_623, 1);
x_629 = lean_ctor_get(x_623, 2);
x_643 = !lean_is_exclusive(x_623);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_623, 4);
lean_dec(x_644);
x_645 = lean_ctor_get(x_623, 3);
lean_dec(x_645);
x_646 = lean_ctor_get(x_623, 0);
lean_dec(x_646);
x_630 = x_623;
x_631 = x_643;
goto block_642;
}
else
{
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_623);
x_630 = lean_box(0);
x_631 = x_643;
goto block_642;
}
block_642:
{
lean_object* x_632; lean_object* x_633; 
x_632 = lean_unsigned_to_nat(3u);
if (x_631 == 0)
{
lean_ctor_set(x_630, 4, x_587);
lean_ctor_set(x_630, 3, x_587);
lean_ctor_set(x_630, 2, x_625);
lean_ctor_set(x_630, 1, x_624);
lean_ctor_set(x_630, 0, x_496);
x_633 = x_630;
goto block_640;
}
else
{
lean_object* x_641; 
x_641 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_641, 0, x_496);
lean_ctor_set(x_641, 1, x_624);
lean_ctor_set(x_641, 2, x_625);
lean_ctor_set(x_641, 3, x_587);
lean_ctor_set(x_641, 4, x_587);
x_633 = x_641;
goto block_640;
}
block_640:
{
lean_object* x_634; 
if (x_627 == 0)
{
lean_ctor_set(x_626, 4, x_587);
lean_ctor_set(x_626, 2, x_4);
lean_ctor_set(x_626, 1, x_3);
lean_ctor_set(x_626, 0, x_496);
x_634 = x_626;
goto block_638;
}
else
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_639, 0, x_496);
lean_ctor_set(x_639, 1, x_3);
lean_ctor_set(x_639, 2, x_4);
lean_ctor_set(x_639, 3, x_587);
lean_ctor_set(x_639, 4, x_587);
x_634 = x_639;
goto block_638;
}
block_638:
{
lean_object* x_635; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_634);
lean_ctor_set(x_7, 3, x_633);
lean_ctor_set(x_7, 2, x_629);
lean_ctor_set(x_7, 1, x_628);
lean_ctor_set(x_7, 0, x_632);
x_635 = x_7;
goto block_636;
}
else
{
lean_object* x_637; 
x_637 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_637, 0, x_632);
lean_ctor_set(x_637, 1, x_628);
lean_ctor_set(x_637, 2, x_629);
lean_ctor_set(x_637, 3, x_633);
lean_ctor_set(x_637, 4, x_634);
x_635 = x_637;
goto block_636;
}
block_636:
{
return x_635;
}
}
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_623);
lean_ctor_set(x_7, 0, x_652);
x_653 = x_7;
goto block_654;
}
else
{
lean_object* x_655; 
x_655 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_3);
lean_ctor_set(x_655, 2, x_4);
lean_ctor_set(x_655, 3, x_5);
lean_ctor_set(x_655, 4, x_623);
x_653 = x_655;
goto block_654;
}
block_654:
{
return x_653;
}
}
}
}
else
{
lean_object* x_656; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 0, x_496);
x_656 = x_7;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_658, 0, x_496);
lean_ctor_set(x_658, 1, x_3);
lean_ctor_set(x_658, 2, x_4);
lean_ctor_set(x_658, 3, x_5);
lean_ctor_set(x_658, 4, x_5);
x_656 = x_658;
goto block_657;
}
block_657:
{
return x_656;
}
}
}
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(x_1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_MessageData_ofName(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_25; 
x_14 = lean_ctor_get(x_13, 0);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
x_15 = x_13;
x_16 = x_25;
goto block_24;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 21);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_del_object(x_15);
x_22 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1);
x_23 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_22, x_8, x_9, x_10, x_11);
return x_23;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
x_26 = lean_ctor_get(x_13, 0);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
x_27 = x_13;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_25; 
x_14 = lean_ctor_get(x_13, 0);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
x_15 = x_13;
x_16 = x_25;
goto block_24;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 20);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_del_object(x_15);
x_22 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1);
x_23 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_22, x_8, x_9, x_10, x_11);
return x_23;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
x_26 = lean_ctor_get(x_13, 0);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
x_27 = x_13;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (x_2 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_30; 
x_21 = lean_ctor_get(x_20, 0);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
x_22 = x_20;
x_23 = x_30;
goto block_29;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 18);
lean_inc_ref(x_24);
lean_dec(x_21);
x_25 = l_Lean_mkAppB(x_17, x_19, x_24);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_25);
x_26 = x_22;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_17);
x_31 = lean_ctor_get(x_20, 0);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
x_32 = x_20;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_dec(x_17);
return x_18;
}
}
else
{
return x_16;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_53; 
x_44 = lean_ctor_get(x_43, 0);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
x_45 = x_43;
x_46 = x_53;
goto block_52;
}
else
{
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 18);
lean_inc_ref(x_47);
lean_dec(x_44);
x_48 = l_Lean_mkAppB(x_40, x_42, x_47);
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_48);
x_49 = x_45;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_42);
lean_dec(x_40);
x_54 = lean_ctor_get(x_43, 0);
x_61 = !lean_is_exclusive(x_43);
if (x_61 == 0)
{
x_55 = x_43;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_43);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_dec(x_40);
return x_41;
}
}
else
{
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4, &l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5, &l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_15 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___closed__1));
x_181 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_15, x_12);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
x_141 = x_2;
x_142 = x_3;
x_143 = x_4;
x_144 = x_5;
x_145 = x_6;
x_146 = x_7;
x_147 = x_8;
x_148 = x_9;
x_149 = x_10;
x_150 = x_11;
x_151 = x_12;
x_152 = x_13;
x_153 = lean_box(0);
goto block_180;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_199; 
x_184 = lean_st_ref_get(x_2);
x_185 = lean_ctor_get(x_184, 0);
x_199 = !lean_is_exclusive(x_184);
if (x_199 == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_184, 1);
lean_dec(x_200);
x_186 = x_184;
x_187 = x_199;
goto block_198;
}
else
{
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_box(0);
x_187 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10, &l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10);
x_189 = l_Lean_PersistentArray_toList___redArg(x_185);
lean_dec_ref(x_185);
x_190 = lean_box(0);
x_191 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__6(x_189, x_190);
x_192 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(x_191, x_190);
x_193 = l_Lean_MessageData_ofList(x_192);
if (x_187 == 0)
{
lean_ctor_set_tag(x_186, 7);
lean_ctor_set(x_186, 1, x_193);
lean_ctor_set(x_186, 0, x_188);
x_194 = x_186;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_193);
x_194 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_195; 
x_195 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_15, x_194, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_195) == 0)
{
lean_dec_ref(x_195);
x_141 = x_2;
x_142 = x_3;
x_143 = x_4;
x_144 = x_5;
x_145 = x_6;
x_146 = x_7;
x_147 = x_8;
x_148 = x_9;
x_149 = x_10;
x_150 = x_11;
x_151 = x_12;
x_152 = x_13;
x_153 = lean_box(0);
goto block_180;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_195;
}
}
}
}
block_60:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_15, x_26);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
x_37 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(x_36, x_17);
x_38 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0, &l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0);
lean_inc(x_33);
x_39 = l_Lean_Grind_Linarith_Poly_mul(x_33, x_38);
x_40 = 1;
x_41 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_21);
lean_ctor_set(x_41, 2, x_1);
lean_ctor_set(x_41, 3, x_37);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_40);
x_43 = lean_unbox(x_35);
lean_dec(x_35);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_29);
x_44 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_42, x_18, x_16, x_25, x_28, x_19, x_24, x_31, x_27, x_20, x_26, x_30);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2(x_42, x_29, x_18, x_16, x_25, x_28, x_19, x_24, x_31, x_27, x_20, x_26, x_30);
lean_dec(x_29);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1, &l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1);
x_48 = l_Lean_MessageData_ofExpr(x_46);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_15, x_49, x_27, x_20, x_26, x_30);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
x_51 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_42, x_18, x_16, x_25, x_28, x_19, x_24, x_31, x_27, x_20, x_26, x_30);
return x_51;
}
else
{
lean_dec_ref(x_42);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
return x_50;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec_ref(x_42);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
x_52 = lean_ctor_get(x_45, 0);
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
x_53 = x_45;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
block_80:
{
lean_object* x_78; 
x_78 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_62, x_63);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
lean_dec(x_64);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_16 = x_67;
x_17 = x_78;
x_18 = x_66;
x_19 = x_70;
x_20 = x_74;
x_21 = x_62;
x_22 = x_61;
x_23 = lean_box(0);
x_24 = x_71;
x_25 = x_68;
x_26 = x_75;
x_27 = x_73;
x_28 = x_69;
x_29 = x_65;
x_30 = x_76;
x_31 = x_72;
x_32 = x_79;
goto block_60;
}
else
{
x_16 = x_67;
x_17 = x_78;
x_18 = x_66;
x_19 = x_70;
x_20 = x_74;
x_21 = x_62;
x_22 = x_61;
x_23 = lean_box(0);
x_24 = x_71;
x_25 = x_68;
x_26 = x_75;
x_27 = x_73;
x_28 = x_69;
x_29 = x_65;
x_30 = x_76;
x_31 = x_72;
x_32 = x_64;
goto block_60;
}
}
block_140:
{
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_96; 
lean_inc(x_94);
lean_inc_ref(x_93);
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_96 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase(x_81, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_inc(x_97);
lean_inc(x_84);
x_98 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0___boxed), 3, 2);
lean_closure_set(x_98, 0, x_84);
lean_closure_set(x_98, 1, x_97);
x_99 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_100 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_99, x_98, x_85);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec_ref(x_100);
x_101 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_15, x_93);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_97, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
lean_dec(x_97);
x_61 = x_104;
x_62 = x_105;
x_63 = x_81;
x_64 = x_82;
x_65 = x_83;
x_66 = x_84;
x_67 = x_85;
x_68 = x_86;
x_69 = x_87;
x_70 = x_88;
x_71 = x_89;
x_72 = x_90;
x_73 = x_91;
x_74 = x_92;
x_75 = x_93;
x_76 = x_94;
x_77 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_97, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_97, 1);
lean_inc(x_107);
lean_dec(x_97);
x_108 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3, &l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3);
lean_inc(x_107);
x_109 = l_Lean_MessageData_ofName(x_107);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_15, x_110, x_91, x_92, x_93, x_94);
if (lean_obj_tag(x_111) == 0)
{
lean_dec_ref(x_111);
x_61 = x_106;
x_62 = x_107;
x_63 = x_81;
x_64 = x_82;
x_65 = x_83;
x_66 = x_84;
x_67 = x_85;
x_68 = x_86;
x_69 = x_87;
x_70 = x_88;
x_71 = x_89;
x_72 = x_90;
x_73 = x_91;
x_74 = x_92;
x_75 = x_93;
x_76 = x_94;
x_77 = lean_box(0);
goto block_80;
}
else
{
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_81);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_1);
return x_111;
}
}
}
else
{
lean_dec(x_97);
lean_dec_ref(x_81);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_1);
return x_100;
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec_ref(x_81);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_1);
x_112 = lean_ctor_get(x_96, 0);
x_119 = !lean_is_exclusive(x_96);
if (x_119 == 0)
{
x_113 = x_96;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_96);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_83);
lean_dec(x_82);
lean_inc(x_94);
lean_inc_ref(x_93);
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc(x_86);
lean_inc(x_85);
x_120 = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_toExprProof(x_1, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = l_Lean_Meta_Grind_closeGoal(x_121, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; uint8_t x_130; 
x_130 = !lean_is_exclusive(x_122);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_122, 0);
lean_dec(x_131);
x_123 = x_122;
x_124 = x_130;
goto block_129;
}
else
{
lean_dec(x_122);
x_123 = lean_box(0);
x_124 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_box(0);
if (x_124 == 0)
{
lean_ctor_set(x_123, 0, x_125);
x_126 = x_123;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_125);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
else
{
return x_122;
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_139; 
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
x_132 = lean_ctor_get(x_120, 0);
x_139 = !lean_is_exclusive(x_120);
if (x_139 == 0)
{
x_133 = x_120;
x_134 = x_139;
goto block_138;
}
else
{
lean_inc(x_132);
lean_dec(x_120);
x_133 = lean_box(0);
x_134 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_135; 
if (x_134 == 0)
{
x_135 = x_133;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_132);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
}
}
block_180:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_st_ref_get(x_141);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_unsigned_to_nat(0u);
x_157 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6, &l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6);
lean_inc_ref(x_1);
x_158 = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_collectDecVars(x_1, x_155, x_157);
lean_dec(x_155);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_15, x_151);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_81 = x_163;
x_82 = x_156;
x_83 = x_141;
x_84 = x_142;
x_85 = x_143;
x_86 = x_144;
x_87 = x_145;
x_88 = x_146;
x_89 = x_147;
x_90 = x_148;
x_91 = x_149;
x_92 = x_150;
x_93 = x_151;
x_94 = x_152;
x_95 = lean_box(0);
goto block_140;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_178; 
x_164 = lean_ctor_get(x_159, 1);
x_178 = !lean_is_exclusive(x_159);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_159, 0);
lean_dec(x_179);
x_165 = x_159;
x_166 = x_178;
goto block_177;
}
else
{
lean_inc(x_164);
lean_dec(x_159);
x_165 = lean_box(0);
x_166 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8, &l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8);
x_168 = lean_box(0);
x_169 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(x_168, x_164);
x_170 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__4(x_169, x_168);
x_171 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(x_170, x_168);
x_172 = l_Lean_MessageData_ofList(x_171);
if (x_166 == 0)
{
lean_ctor_set_tag(x_165, 7);
lean_ctor_set(x_165, 1, x_172);
lean_ctor_set(x_165, 0, x_167);
x_173 = x_165;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_167);
lean_ctor_set(x_176, 1, x_172);
x_173 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_174; 
x_174 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_15, x_173, x_149, x_150, x_151, x_152);
if (lean_obj_tag(x_174) == 0)
{
lean_dec_ref(x_174);
x_81 = x_164;
x_82 = x_156;
x_83 = x_141;
x_84 = x_142;
x_85 = x_143;
x_86 = x_144;
x_87 = x_145;
x_88 = x_146;
x_89 = x_147;
x_90 = x_148;
x_91 = x_149;
x_92 = x_150;
x_93 = x_151;
x_94 = x_152;
x_95 = lean_box(0);
goto block_140;
}
else
{
lean_dec(x_164);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec_ref(x_1);
return x_174;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_116; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_116 = !lean_is_exclusive(x_3);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_3, 7);
lean_dec(x_117);
x_118 = lean_ctor_get(x_3, 6);
lean_dec(x_118);
x_119 = lean_ctor_get(x_3, 5);
lean_dec(x_119);
x_120 = lean_ctor_get(x_3, 4);
lean_dec(x_120);
x_121 = lean_ctor_get(x_3, 3);
lean_dec(x_121);
x_122 = lean_ctor_get(x_3, 2);
lean_dec(x_122);
x_123 = lean_ctor_get(x_3, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_3, 0);
lean_dec(x_124);
x_14 = x_3;
x_15 = x_116;
goto block_115;
}
else
{
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_73; 
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 2);
x_20 = lean_ctor_get(x_16, 3);
x_21 = lean_ctor_get(x_16, 4);
x_22 = lean_ctor_get(x_16, 5);
x_23 = lean_ctor_get(x_16, 6);
x_24 = lean_ctor_get(x_16, 7);
x_25 = lean_ctor_get(x_16, 8);
x_26 = lean_ctor_get(x_16, 9);
x_27 = lean_ctor_get(x_16, 10);
x_28 = lean_ctor_get(x_16, 11);
x_29 = lean_ctor_get(x_16, 12);
x_30 = lean_ctor_get(x_16, 13);
x_31 = lean_ctor_get(x_16, 14);
x_32 = lean_ctor_get(x_16, 15);
x_33 = lean_ctor_get(x_16, 16);
x_34 = lean_ctor_get(x_16, 17);
x_35 = lean_ctor_get(x_16, 18);
x_36 = lean_ctor_get(x_16, 19);
x_37 = lean_ctor_get(x_16, 20);
x_38 = lean_ctor_get(x_16, 21);
x_39 = lean_ctor_get(x_16, 22);
x_40 = lean_ctor_get(x_16, 23);
x_41 = lean_ctor_get(x_16, 24);
x_42 = lean_ctor_get(x_16, 25);
x_43 = lean_ctor_get(x_16, 26);
x_44 = lean_ctor_get(x_16, 27);
x_45 = lean_ctor_get(x_16, 28);
x_46 = lean_ctor_get(x_16, 29);
x_47 = lean_ctor_get(x_16, 30);
x_48 = lean_ctor_get(x_16, 31);
x_49 = lean_ctor_get(x_16, 32);
x_50 = lean_ctor_get(x_16, 33);
x_51 = lean_ctor_get(x_16, 34);
x_52 = lean_ctor_get_uint8(x_16, sizeof(void*)*42);
x_53 = lean_ctor_get(x_16, 36);
x_54 = lean_ctor_get(x_16, 37);
x_55 = lean_ctor_get(x_16, 38);
x_56 = lean_ctor_get(x_16, 39);
x_57 = lean_ctor_get(x_16, 40);
x_58 = lean_ctor_get(x_16, 41);
x_59 = lean_array_fget(x_4, x_1);
x_60 = lean_ctor_get(x_59, 35);
x_73 = !lean_is_exclusive(x_59);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_74 = lean_ctor_get(x_59, 41);
lean_dec(x_74);
x_75 = lean_ctor_get(x_59, 40);
lean_dec(x_75);
x_76 = lean_ctor_get(x_59, 39);
lean_dec(x_76);
x_77 = lean_ctor_get(x_59, 38);
lean_dec(x_77);
x_78 = lean_ctor_get(x_59, 37);
lean_dec(x_78);
x_79 = lean_ctor_get(x_59, 36);
lean_dec(x_79);
x_80 = lean_ctor_get(x_59, 34);
lean_dec(x_80);
x_81 = lean_ctor_get(x_59, 33);
lean_dec(x_81);
x_82 = lean_ctor_get(x_59, 32);
lean_dec(x_82);
x_83 = lean_ctor_get(x_59, 31);
lean_dec(x_83);
x_84 = lean_ctor_get(x_59, 30);
lean_dec(x_84);
x_85 = lean_ctor_get(x_59, 29);
lean_dec(x_85);
x_86 = lean_ctor_get(x_59, 28);
lean_dec(x_86);
x_87 = lean_ctor_get(x_59, 27);
lean_dec(x_87);
x_88 = lean_ctor_get(x_59, 26);
lean_dec(x_88);
x_89 = lean_ctor_get(x_59, 25);
lean_dec(x_89);
x_90 = lean_ctor_get(x_59, 24);
lean_dec(x_90);
x_91 = lean_ctor_get(x_59, 23);
lean_dec(x_91);
x_92 = lean_ctor_get(x_59, 22);
lean_dec(x_92);
x_93 = lean_ctor_get(x_59, 21);
lean_dec(x_93);
x_94 = lean_ctor_get(x_59, 20);
lean_dec(x_94);
x_95 = lean_ctor_get(x_59, 19);
lean_dec(x_95);
x_96 = lean_ctor_get(x_59, 18);
lean_dec(x_96);
x_97 = lean_ctor_get(x_59, 17);
lean_dec(x_97);
x_98 = lean_ctor_get(x_59, 16);
lean_dec(x_98);
x_99 = lean_ctor_get(x_59, 15);
lean_dec(x_99);
x_100 = lean_ctor_get(x_59, 14);
lean_dec(x_100);
x_101 = lean_ctor_get(x_59, 13);
lean_dec(x_101);
x_102 = lean_ctor_get(x_59, 12);
lean_dec(x_102);
x_103 = lean_ctor_get(x_59, 11);
lean_dec(x_103);
x_104 = lean_ctor_get(x_59, 10);
lean_dec(x_104);
x_105 = lean_ctor_get(x_59, 9);
lean_dec(x_105);
x_106 = lean_ctor_get(x_59, 8);
lean_dec(x_106);
x_107 = lean_ctor_get(x_59, 7);
lean_dec(x_107);
x_108 = lean_ctor_get(x_59, 6);
lean_dec(x_108);
x_109 = lean_ctor_get(x_59, 5);
lean_dec(x_109);
x_110 = lean_ctor_get(x_59, 4);
lean_dec(x_110);
x_111 = lean_ctor_get(x_59, 3);
lean_dec(x_111);
x_112 = lean_ctor_get(x_59, 2);
lean_dec(x_112);
x_113 = lean_ctor_get(x_59, 1);
lean_dec(x_113);
x_114 = lean_ctor_get(x_59, 0);
lean_dec(x_114);
x_61 = x_59;
x_62 = x_73;
goto block_72;
}
else
{
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_4, x_1, x_63);
lean_inc_ref(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc_ref(x_54);
lean_inc(x_53);
lean_inc_ref(x_51);
lean_inc_ref(x_50);
lean_inc_ref(x_49);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
lean_inc_ref(x_46);
lean_inc_ref(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
if (x_62 == 0)
{
lean_ctor_set(x_61, 41, x_58);
lean_ctor_set(x_61, 40, x_57);
lean_ctor_set(x_61, 39, x_56);
lean_ctor_set(x_61, 38, x_55);
lean_ctor_set(x_61, 37, x_54);
lean_ctor_set(x_61, 36, x_53);
lean_ctor_set(x_61, 34, x_51);
lean_ctor_set(x_61, 33, x_50);
lean_ctor_set(x_61, 32, x_49);
lean_ctor_set(x_61, 31, x_48);
lean_ctor_set(x_61, 30, x_47);
lean_ctor_set(x_61, 29, x_46);
lean_ctor_set(x_61, 28, x_45);
lean_ctor_set(x_61, 27, x_44);
lean_ctor_set(x_61, 26, x_43);
lean_ctor_set(x_61, 25, x_42);
lean_ctor_set(x_61, 24, x_41);
lean_ctor_set(x_61, 23, x_40);
lean_ctor_set(x_61, 22, x_39);
lean_ctor_set(x_61, 21, x_38);
lean_ctor_set(x_61, 20, x_37);
lean_ctor_set(x_61, 19, x_36);
lean_ctor_set(x_61, 18, x_35);
lean_ctor_set(x_61, 17, x_34);
lean_ctor_set(x_61, 16, x_33);
lean_ctor_set(x_61, 15, x_32);
lean_ctor_set(x_61, 14, x_31);
lean_ctor_set(x_61, 13, x_30);
lean_ctor_set(x_61, 12, x_29);
lean_ctor_set(x_61, 11, x_28);
lean_ctor_set(x_61, 10, x_27);
lean_ctor_set(x_61, 9, x_26);
lean_ctor_set(x_61, 8, x_25);
lean_ctor_set(x_61, 7, x_24);
lean_ctor_set(x_61, 6, x_23);
lean_ctor_set(x_61, 5, x_22);
lean_ctor_set(x_61, 4, x_21);
lean_ctor_set(x_61, 3, x_20);
lean_ctor_set(x_61, 2, x_19);
lean_ctor_set(x_61, 1, x_18);
lean_ctor_set(x_61, 0, x_17);
x_65 = x_61;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_71, 0, x_17);
lean_ctor_set(x_71, 1, x_18);
lean_ctor_set(x_71, 2, x_19);
lean_ctor_set(x_71, 3, x_20);
lean_ctor_set(x_71, 4, x_21);
lean_ctor_set(x_71, 5, x_22);
lean_ctor_set(x_71, 6, x_23);
lean_ctor_set(x_71, 7, x_24);
lean_ctor_set(x_71, 8, x_25);
lean_ctor_set(x_71, 9, x_26);
lean_ctor_set(x_71, 10, x_27);
lean_ctor_set(x_71, 11, x_28);
lean_ctor_set(x_71, 12, x_29);
lean_ctor_set(x_71, 13, x_30);
lean_ctor_set(x_71, 14, x_31);
lean_ctor_set(x_71, 15, x_32);
lean_ctor_set(x_71, 16, x_33);
lean_ctor_set(x_71, 17, x_34);
lean_ctor_set(x_71, 18, x_35);
lean_ctor_set(x_71, 19, x_36);
lean_ctor_set(x_71, 20, x_37);
lean_ctor_set(x_71, 21, x_38);
lean_ctor_set(x_71, 22, x_39);
lean_ctor_set(x_71, 23, x_40);
lean_ctor_set(x_71, 24, x_41);
lean_ctor_set(x_71, 25, x_42);
lean_ctor_set(x_71, 26, x_43);
lean_ctor_set(x_71, 27, x_44);
lean_ctor_set(x_71, 28, x_45);
lean_ctor_set(x_71, 29, x_46);
lean_ctor_set(x_71, 30, x_47);
lean_ctor_set(x_71, 31, x_48);
lean_ctor_set(x_71, 32, x_49);
lean_ctor_set(x_71, 33, x_50);
lean_ctor_set(x_71, 34, x_51);
lean_ctor_set(x_71, 35, x_60);
lean_ctor_set(x_71, 36, x_53);
lean_ctor_set(x_71, 37, x_54);
lean_ctor_set(x_71, 38, x_55);
lean_ctor_set(x_71, 39, x_56);
lean_ctor_set(x_71, 40, x_57);
lean_ctor_set(x_71, 41, x_58);
x_65 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_66; lean_object* x_67; 
lean_ctor_set_uint8(x_65, sizeof(void*)*42, x_52);
x_66 = lean_array_fset(x_64, x_1, x_65);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_66);
x_67 = x_14;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_5);
lean_ctor_set(x_69, 2, x_6);
lean_ctor_set(x_69, 3, x_7);
lean_ctor_set(x_69, 4, x_8);
lean_ctor_set(x_69, 5, x_9);
lean_ctor_set(x_69, 6, x_10);
lean_ctor_set(x_69, 7, x_11);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_PersistentArray_isEmpty___redArg(x_6);
lean_dec_ref(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_st_ref_get(x_1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_14, 2);
x_16 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_14);
x_19 = l_outOfBounds___redArg(x_16);
x_9 = x_19;
goto block_13;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_PersistentArray_get_x21___redArg(x_16, x_14, x_17);
x_9 = x_20;
goto block_13;
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_12 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_11, x_10, x_3);
return x_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(x_1, x_2, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_76; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_76 = !lean_is_exclusive(x_3);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_3, 7);
lean_dec(x_77);
x_78 = lean_ctor_get(x_3, 6);
lean_dec(x_78);
x_79 = lean_ctor_get(x_3, 5);
lean_dec(x_79);
x_80 = lean_ctor_get(x_3, 4);
lean_dec(x_80);
x_81 = lean_ctor_get(x_3, 3);
lean_dec(x_81);
x_82 = lean_ctor_get(x_3, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_3, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_3, 0);
lean_dec(x_84);
x_14 = x_3;
x_15 = x_76;
goto block_75;
}
else
{
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_74; 
x_16 = lean_array_fget(x_4, x_1);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 2);
x_20 = lean_ctor_get(x_16, 3);
x_21 = lean_ctor_get(x_16, 4);
x_22 = lean_ctor_get(x_16, 5);
x_23 = lean_ctor_get(x_16, 6);
x_24 = lean_ctor_get(x_16, 7);
x_25 = lean_ctor_get(x_16, 8);
x_26 = lean_ctor_get(x_16, 9);
x_27 = lean_ctor_get(x_16, 10);
x_28 = lean_ctor_get(x_16, 11);
x_29 = lean_ctor_get(x_16, 12);
x_30 = lean_ctor_get(x_16, 13);
x_31 = lean_ctor_get(x_16, 14);
x_32 = lean_ctor_get(x_16, 15);
x_33 = lean_ctor_get(x_16, 16);
x_34 = lean_ctor_get(x_16, 17);
x_35 = lean_ctor_get(x_16, 18);
x_36 = lean_ctor_get(x_16, 19);
x_37 = lean_ctor_get(x_16, 20);
x_38 = lean_ctor_get(x_16, 21);
x_39 = lean_ctor_get(x_16, 22);
x_40 = lean_ctor_get(x_16, 23);
x_41 = lean_ctor_get(x_16, 24);
x_42 = lean_ctor_get(x_16, 25);
x_43 = lean_ctor_get(x_16, 26);
x_44 = lean_ctor_get(x_16, 27);
x_45 = lean_ctor_get(x_16, 28);
x_46 = lean_ctor_get(x_16, 29);
x_47 = lean_ctor_get(x_16, 30);
x_48 = lean_ctor_get(x_16, 31);
x_49 = lean_ctor_get(x_16, 32);
x_50 = lean_ctor_get(x_16, 33);
x_51 = lean_ctor_get(x_16, 34);
x_52 = lean_ctor_get(x_16, 35);
x_53 = lean_ctor_get_uint8(x_16, sizeof(void*)*42);
x_54 = lean_ctor_get(x_16, 36);
x_55 = lean_ctor_get(x_16, 37);
x_56 = lean_ctor_get(x_16, 38);
x_57 = lean_ctor_get(x_16, 39);
x_58 = lean_ctor_get(x_16, 40);
x_59 = lean_ctor_get(x_16, 41);
x_74 = !lean_is_exclusive(x_16);
if (x_74 == 0)
{
x_60 = x_16;
x_61 = x_74;
goto block_73;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_16);
x_60 = lean_box(0);
x_61 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_box(0);
x_63 = lean_array_fset(x_4, x_1, x_62);
x_64 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3, &l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3);
x_65 = l_Lean_PersistentArray_set___redArg(x_52, x_2, x_64);
if (x_61 == 0)
{
lean_ctor_set(x_60, 35, x_65);
x_66 = x_60;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_72, 0, x_17);
lean_ctor_set(x_72, 1, x_18);
lean_ctor_set(x_72, 2, x_19);
lean_ctor_set(x_72, 3, x_20);
lean_ctor_set(x_72, 4, x_21);
lean_ctor_set(x_72, 5, x_22);
lean_ctor_set(x_72, 6, x_23);
lean_ctor_set(x_72, 7, x_24);
lean_ctor_set(x_72, 8, x_25);
lean_ctor_set(x_72, 9, x_26);
lean_ctor_set(x_72, 10, x_27);
lean_ctor_set(x_72, 11, x_28);
lean_ctor_set(x_72, 12, x_29);
lean_ctor_set(x_72, 13, x_30);
lean_ctor_set(x_72, 14, x_31);
lean_ctor_set(x_72, 15, x_32);
lean_ctor_set(x_72, 16, x_33);
lean_ctor_set(x_72, 17, x_34);
lean_ctor_set(x_72, 18, x_35);
lean_ctor_set(x_72, 19, x_36);
lean_ctor_set(x_72, 20, x_37);
lean_ctor_set(x_72, 21, x_38);
lean_ctor_set(x_72, 22, x_39);
lean_ctor_set(x_72, 23, x_40);
lean_ctor_set(x_72, 24, x_41);
lean_ctor_set(x_72, 25, x_42);
lean_ctor_set(x_72, 26, x_43);
lean_ctor_set(x_72, 27, x_44);
lean_ctor_set(x_72, 28, x_45);
lean_ctor_set(x_72, 29, x_46);
lean_ctor_set(x_72, 30, x_47);
lean_ctor_set(x_72, 31, x_48);
lean_ctor_set(x_72, 32, x_49);
lean_ctor_set(x_72, 33, x_50);
lean_ctor_set(x_72, 34, x_51);
lean_ctor_set(x_72, 35, x_65);
lean_ctor_set(x_72, 36, x_54);
lean_ctor_set(x_72, 37, x_55);
lean_ctor_set(x_72, 38, x_56);
lean_ctor_set(x_72, 39, x_57);
lean_ctor_set(x_72, 40, x_58);
lean_ctor_set(x_72, 41, x_59);
lean_ctor_set_uint8(x_72, sizeof(void*)*42, x_53);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_63, x_1, x_66);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_67);
x_68 = x_14;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_5);
lean_ctor_set(x_70, 2, x_6);
lean_ctor_set(x_70, 3, x_7);
lean_ctor_set(x_70, 4, x_8);
lean_ctor_set(x_70, 5, x_9);
lean_ctor_set(x_70, 6, x_10);
lean_ctor_set(x_70, 7, x_11);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec_ref(x_3);
return x_4;
}
else
{
lean_object* x_15; uint8_t x_16; uint8_t x_76; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_76 = !lean_is_exclusive(x_4);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_4, 7);
lean_dec(x_77);
x_78 = lean_ctor_get(x_4, 6);
lean_dec(x_78);
x_79 = lean_ctor_get(x_4, 5);
lean_dec(x_79);
x_80 = lean_ctor_get(x_4, 4);
lean_dec(x_80);
x_81 = lean_ctor_get(x_4, 3);
lean_dec(x_81);
x_82 = lean_ctor_get(x_4, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_4, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_4, 0);
lean_dec(x_84);
x_15 = x_4;
x_16 = x_76;
goto block_75;
}
else
{
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_17 = lean_array_fget(x_5, x_1);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 2);
x_21 = lean_ctor_get(x_17, 3);
x_22 = lean_ctor_get(x_17, 4);
x_23 = lean_ctor_get(x_17, 5);
x_24 = lean_ctor_get(x_17, 6);
x_25 = lean_ctor_get(x_17, 7);
x_26 = lean_ctor_get(x_17, 8);
x_27 = lean_ctor_get(x_17, 9);
x_28 = lean_ctor_get(x_17, 10);
x_29 = lean_ctor_get(x_17, 11);
x_30 = lean_ctor_get(x_17, 12);
x_31 = lean_ctor_get(x_17, 13);
x_32 = lean_ctor_get(x_17, 14);
x_33 = lean_ctor_get(x_17, 15);
x_34 = lean_ctor_get(x_17, 16);
x_35 = lean_ctor_get(x_17, 17);
x_36 = lean_ctor_get(x_17, 18);
x_37 = lean_ctor_get(x_17, 19);
x_38 = lean_ctor_get(x_17, 20);
x_39 = lean_ctor_get(x_17, 21);
x_40 = lean_ctor_get(x_17, 22);
x_41 = lean_ctor_get(x_17, 23);
x_42 = lean_ctor_get(x_17, 24);
x_43 = lean_ctor_get(x_17, 25);
x_44 = lean_ctor_get(x_17, 26);
x_45 = lean_ctor_get(x_17, 27);
x_46 = lean_ctor_get(x_17, 28);
x_47 = lean_ctor_get(x_17, 29);
x_48 = lean_ctor_get(x_17, 30);
x_49 = lean_ctor_get(x_17, 31);
x_50 = lean_ctor_get(x_17, 32);
x_51 = lean_ctor_get(x_17, 33);
x_52 = lean_ctor_get(x_17, 34);
x_53 = lean_ctor_get(x_17, 35);
x_54 = lean_ctor_get_uint8(x_17, sizeof(void*)*42);
x_55 = lean_ctor_get(x_17, 36);
x_56 = lean_ctor_get(x_17, 37);
x_57 = lean_ctor_get(x_17, 38);
x_58 = lean_ctor_get(x_17, 39);
x_59 = lean_ctor_get(x_17, 40);
x_60 = lean_ctor_get(x_17, 41);
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
x_61 = x_17;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_17);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_5, x_1, x_63);
x_65 = l_Lean_PersistentArray_set___redArg(x_53, x_2, x_3);
if (x_62 == 0)
{
lean_ctor_set(x_61, 35, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_72, 0, x_18);
lean_ctor_set(x_72, 1, x_19);
lean_ctor_set(x_72, 2, x_20);
lean_ctor_set(x_72, 3, x_21);
lean_ctor_set(x_72, 4, x_22);
lean_ctor_set(x_72, 5, x_23);
lean_ctor_set(x_72, 6, x_24);
lean_ctor_set(x_72, 7, x_25);
lean_ctor_set(x_72, 8, x_26);
lean_ctor_set(x_72, 9, x_27);
lean_ctor_set(x_72, 10, x_28);
lean_ctor_set(x_72, 11, x_29);
lean_ctor_set(x_72, 12, x_30);
lean_ctor_set(x_72, 13, x_31);
lean_ctor_set(x_72, 14, x_32);
lean_ctor_set(x_72, 15, x_33);
lean_ctor_set(x_72, 16, x_34);
lean_ctor_set(x_72, 17, x_35);
lean_ctor_set(x_72, 18, x_36);
lean_ctor_set(x_72, 19, x_37);
lean_ctor_set(x_72, 20, x_38);
lean_ctor_set(x_72, 21, x_39);
lean_ctor_set(x_72, 22, x_40);
lean_ctor_set(x_72, 23, x_41);
lean_ctor_set(x_72, 24, x_42);
lean_ctor_set(x_72, 25, x_43);
lean_ctor_set(x_72, 26, x_44);
lean_ctor_set(x_72, 27, x_45);
lean_ctor_set(x_72, 28, x_46);
lean_ctor_set(x_72, 29, x_47);
lean_ctor_set(x_72, 30, x_48);
lean_ctor_set(x_72, 31, x_49);
lean_ctor_set(x_72, 32, x_50);
lean_ctor_set(x_72, 33, x_51);
lean_ctor_set(x_72, 34, x_52);
lean_ctor_set(x_72, 35, x_65);
lean_ctor_set(x_72, 36, x_55);
lean_ctor_set(x_72, 37, x_56);
lean_ctor_set(x_72, 38, x_57);
lean_ctor_set(x_72, 39, x_58);
lean_ctor_set(x_72, 40, x_59);
lean_ctor_set(x_72, 41, x_60);
lean_ctor_set_uint8(x_72, sizeof(void*)*42, x_54);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_1, x_66);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_67);
x_68 = x_15;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_6);
lean_ctor_set(x_70, 2, x_7);
lean_ctor_set(x_70, 3, x_8);
lean_ctor_set(x_70, 4, x_9);
lean_ctor_set(x_70, 5, x_10);
lean_ctor_set(x_70, 6, x_11);
lean_ctor_set(x_70, 7, x_12);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_58; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec_ref(x_1);
x_58 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_70 = lean_ctor_get(x_59, 38);
lean_inc_ref(x_70);
lean_dec(x_59);
x_71 = lean_ctor_get(x_70, 2);
x_72 = lean_box(0);
x_73 = lean_nat_dec_lt(x_17, x_71);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec_ref(x_70);
x_74 = l_outOfBounds___redArg(x_72);
x_60 = x_74;
goto block_69;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_PersistentArray_get_x21___redArg(x_72, x_70, x_17);
x_60 = x_75;
goto block_69;
}
block_69:
{
if (lean_obj_tag(x_60) == 1)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_61, 0);
x_63 = l_Lean_Grind_Linarith_Poly_coeff(x_62, x_17);
x_64 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
x_65 = lean_int_dec_eq(x_63, x_64);
if (x_65 == 0)
{
lean_inc(x_62);
x_19 = x_63;
x_20 = x_61;
x_21 = x_62;
x_22 = x_2;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
x_33 = x_13;
x_34 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_18);
lean_dec(x_17);
x_66 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_61);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
x_67 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1);
x_68 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_67, x_10, x_11, x_12, x_13);
return x_68;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
x_76 = lean_ctor_get(x_58, 0);
x_83 = !lean_is_exclusive(x_58);
if (x_83 == 0)
{
x_77 = x_58;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_58);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
block_57:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_17);
lean_inc(x_23);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0___boxed), 3, 2);
lean_closure_set(x_35, 0, x_23);
lean_closure_set(x_35, 1, x_17);
x_36 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_37 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_36, x_35, x_24);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_37);
x_38 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_21, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_20);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Rat_neg(x_40);
x_42 = l_Rat_ofInt(x_19);
x_43 = l_Rat_div(x_41, x_42);
lean_dec_ref(x_41);
lean_inc_ref(x_43);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(x_17, x_43, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_44);
lean_inc(x_23);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1___boxed), 4, 3);
lean_closure_set(x_45, 0, x_23);
lean_closure_set(x_45, 1, x_17);
lean_closure_set(x_45, 2, x_43);
x_46 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_36, x_45, x_24);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
x_1 = x_18;
x_2 = x_22;
x_3 = x_23;
x_4 = x_24;
x_5 = x_25;
x_6 = x_26;
x_7 = x_27;
x_8 = x_28;
x_9 = x_29;
x_10 = x_30;
x_11 = x_31;
x_12 = x_32;
x_13 = x_33;
goto _start;
}
else
{
lean_dec(x_23);
lean_dec(x_18);
return x_46;
}
}
else
{
lean_dec_ref(x_43);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
return x_44;
}
}
else
{
lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_48 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(x_20, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_23);
lean_dec_ref(x_20);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_23);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_49 = lean_ctor_get(x_38, 0);
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
x_50 = x_38;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_38);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_36; 
x_15 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_16 = x_14;
x_17 = x_36;
goto block_35;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_18; 
x_18 = lean_unbox(x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_del_object(x_16);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 39);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_19, 0);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
x_24 = x_19;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_31 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_31);
x_32 = x_16;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_2);
x_37 = lean_ctor_get(x_14, 0);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
x_38 = x_14;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2));
x_40 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2));
x_41 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_40, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_240; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_240 = lean_unbox(x_42);
lean_dec(x_42);
if (x_240 == 0)
{
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_75 = x_1;
x_76 = x_2;
x_77 = x_3;
x_78 = x_4;
x_79 = x_5;
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
x_83 = x_9;
x_84 = x_10;
x_85 = x_11;
x_86 = x_12;
x_87 = lean_box(0);
goto block_239;
}
else
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__7, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__7_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__7);
x_242 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_40, x_241, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_242) == 0)
{
lean_dec_ref(x_242);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_75 = x_1;
x_76 = x_2;
x_77 = x_3;
x_78 = x_4;
x_79 = x_5;
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
x_83 = x_9;
x_84 = x_10;
x_85 = x_11;
x_86 = x_12;
x_87 = lean_box(0);
goto block_239;
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_250; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_243 = lean_ctor_get(x_242, 0);
x_250 = !lean_is_exclusive(x_242);
if (x_250 == 0)
{
x_244 = x_242;
x_245 = x_250;
goto block_249;
}
else
{
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_box(0);
x_245 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_246; 
if (x_245 == 0)
{
x_246 = x_244;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_243);
x_246 = x_248;
goto block_247;
}
block_247:
{
return x_246;
}
}
}
}
block_74:
{
lean_object* x_56; 
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; uint8_t x_64; 
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_56, 0);
lean_dec(x_65);
x_57 = x_56;
x_58 = x_64;
goto block_63;
}
else
{
lean_dec(x_56);
x_57 = lean_box(0);
x_58 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_59; lean_object* x_60; 
x_59 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__1));
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_59);
x_60 = x_57;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_73; 
x_66 = lean_ctor_get(x_56, 0);
x_73 = !lean_is_exclusive(x_56);
if (x_73 == 0)
{
x_67 = x_56;
x_68 = x_73;
goto block_72;
}
else
{
lean_inc(x_66);
lean_dec(x_56);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
block_239:
{
lean_object* x_88; 
x_88 = l_Lean_Core_checkSystem(x_39, x_85, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
lean_dec_ref(x_88);
x_89 = l_Lean_Meta_Grind_Arith_Linear_hasAssignment(x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = l_Lean_Meta_Grind_isInconsistent___redArg(x_77);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_193; 
x_93 = lean_ctor_get(x_92, 0);
x_193 = !lean_is_exclusive(x_92);
if (x_193 == 0)
{
x_94 = x_92;
x_95 = x_193;
goto block_192;
}
else
{
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_box(0);
x_95 = x_193;
goto block_192;
}
block_192:
{
uint8_t x_96; 
x_96 = lean_unbox(x_93);
lean_dec(x_93);
if (x_96 == 0)
{
lean_object* x_97; 
lean_del_object(x_94);
x_97 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_ctor_get(x_98, 36);
lean_inc(x_99);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict(x_100, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_101) == 0)
{
lean_dec_ref(x_101);
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_101, 0);
x_110 = !lean_is_exclusive(x_101);
if (x_110 == 0)
{
x_104 = x_101;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_99);
x_111 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_40, x_85);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_112, 35);
lean_inc_ref(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec_ref(x_113);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_114, 2);
lean_inc(x_117);
lean_dec_ref(x_114);
x_14 = x_117;
x_15 = x_75;
x_16 = x_76;
x_17 = x_77;
x_18 = x_78;
x_19 = x_79;
x_20 = x_80;
x_21 = x_81;
x_22 = x_82;
x_23 = x_83;
x_24 = x_84;
x_25 = x_85;
x_26 = x_86;
x_27 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_114, 2);
lean_inc(x_118);
lean_dec_ref(x_114);
x_119 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_118, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_ctor_get(x_122, 35);
lean_inc_ref(x_123);
lean_dec(x_122);
x_124 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__3);
x_125 = l_Lean_MessageData_ofExpr(x_120);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3, &l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_inc(x_118);
x_129 = l_Nat_reprFast(x_118);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Lean_MessageData_ofFormat(x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_127);
x_134 = l_Lean_PersistentArray_toList___redArg(x_123);
lean_dec_ref(x_123);
x_135 = lean_box(0);
x_136 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_134, x_135);
x_137 = l_Lean_MessageData_ofList(x_136);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_133);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_40, x_138, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_139) == 0)
{
lean_dec_ref(x_139);
x_14 = x_118;
x_15 = x_75;
x_16 = x_76;
x_17 = x_77;
x_18 = x_78;
x_19 = x_79;
x_20 = x_80;
x_21 = x_81;
x_22 = x_82;
x_23 = x_83;
x_24 = x_84;
x_25 = x_85;
x_26 = x_86;
x_27 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_147; 
lean_dec(x_118);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = lean_ctor_get(x_139, 0);
x_147 = !lean_is_exclusive(x_139);
if (x_147 == 0)
{
x_141 = x_139;
x_142 = x_147;
goto block_146;
}
else
{
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_box(0);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_142 == 0)
{
x_143 = x_141;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_ctor_get(x_121, 0);
x_155 = !lean_is_exclusive(x_121);
if (x_155 == 0)
{
x_149 = x_121;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_121);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
lean_dec(x_118);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_119, 0);
x_163 = !lean_is_exclusive(x_119);
if (x_163 == 0)
{
x_157 = x_119;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_dec(x_119);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_171; 
lean_dec(x_112);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_113, 0);
x_171 = !lean_is_exclusive(x_113);
if (x_171 == 0)
{
x_165 = x_113;
x_166 = x_171;
goto block_170;
}
else
{
lean_inc(x_164);
lean_dec(x_113);
x_165 = lean_box(0);
x_166 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_167; 
if (x_166 == 0)
{
x_167 = x_165;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_164);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_179; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_ctor_get(x_111, 0);
x_179 = !lean_is_exclusive(x_111);
if (x_179 == 0)
{
x_173 = x_111;
x_174 = x_179;
goto block_178;
}
else
{
lean_inc(x_172);
lean_dec(x_111);
x_173 = lean_box(0);
x_174 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_175; 
if (x_174 == 0)
{
x_175 = x_173;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_175 = x_177;
goto block_176;
}
block_176:
{
return x_175;
}
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_187; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_97, 0);
x_187 = !lean_is_exclusive(x_97);
if (x_187 == 0)
{
x_181 = x_97;
x_182 = x_187;
goto block_186;
}
else
{
lean_inc(x_180);
lean_dec(x_97);
x_181 = lean_box(0);
x_182 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_183; 
if (x_182 == 0)
{
x_183 = x_181;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_180);
x_183 = x_185;
goto block_184;
}
block_184:
{
return x_183;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__1));
if (x_95 == 0)
{
lean_ctor_set(x_94, 0, x_188);
x_189 = x_94;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_188);
x_189 = x_191;
goto block_190;
}
block_190:
{
return x_189;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_201; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_ctor_get(x_92, 0);
x_201 = !lean_is_exclusive(x_92);
if (x_201 == 0)
{
x_195 = x_92;
x_196 = x_201;
goto block_200;
}
else
{
lean_inc(x_194);
lean_dec(x_92);
x_195 = lean_box(0);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
if (x_196 == 0)
{
x_197 = x_195;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_194);
x_197 = x_199;
goto block_198;
}
block_198:
{
return x_197;
}
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_40, x_85);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
x_43 = x_75;
x_44 = x_76;
x_45 = x_77;
x_46 = x_78;
x_47 = x_79;
x_48 = x_80;
x_49 = x_81;
x_50 = x_82;
x_51 = x_83;
x_52 = x_84;
x_53 = x_85;
x_54 = x_86;
x_55 = lean_box(0);
goto block_74;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___closed__5);
x_206 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_40, x_205, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_206) == 0)
{
lean_dec_ref(x_206);
x_43 = x_75;
x_44 = x_76;
x_45 = x_77;
x_46 = x_78;
x_47 = x_79;
x_48 = x_80;
x_49 = x_81;
x_50 = x_82;
x_51 = x_83;
x_52 = x_84;
x_53 = x_85;
x_54 = x_86;
x_55 = lean_box(0);
goto block_74;
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_214; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
x_207 = lean_ctor_get(x_206, 0);
x_214 = !lean_is_exclusive(x_206);
if (x_214 == 0)
{
x_208 = x_206;
x_209 = x_214;
goto block_213;
}
else
{
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_box(0);
x_209 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_210; 
if (x_209 == 0)
{
x_210 = x_208;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_207);
x_210 = x_212;
goto block_211;
}
block_211:
{
return x_210;
}
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_222; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
x_215 = lean_ctor_get(x_202, 0);
x_222 = !lean_is_exclusive(x_202);
if (x_222 == 0)
{
x_216 = x_202;
x_217 = x_222;
goto block_221;
}
else
{
lean_inc(x_215);
lean_dec(x_202);
x_216 = lean_box(0);
x_217 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_218; 
if (x_217 == 0)
{
x_218 = x_216;
goto block_219;
}
else
{
lean_object* x_220; 
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_215);
x_218 = x_220;
goto block_219;
}
block_219:
{
return x_218;
}
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; uint8_t x_230; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_89, 0);
x_230 = !lean_is_exclusive(x_89);
if (x_230 == 0)
{
x_224 = x_89;
x_225 = x_230;
goto block_229;
}
else
{
lean_inc(x_223);
lean_dec(x_89);
x_224 = lean_box(0);
x_225 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_226; 
if (x_225 == 0)
{
x_226 = x_224;
goto block_227;
}
else
{
lean_object* x_228; 
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_223);
x_226 = x_228;
goto block_227;
}
block_227:
{
return x_226;
}
}
}
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; uint8_t x_238; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = lean_ctor_get(x_88, 0);
x_238 = !lean_is_exclusive(x_88);
if (x_238 == 0)
{
x_232 = x_88;
x_233 = x_238;
goto block_237;
}
else
{
lean_inc(x_231);
lean_dec(x_88);
x_232 = lean_box(0);
x_233 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_234; 
if (x_233 == 0)
{
x_234 = x_232;
goto block_235;
}
else
{
lean_object* x_236; 
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_231);
x_234 = x_236;
goto block_235;
}
block_235:
{
return x_234;
}
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_258; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = lean_ctor_get(x_41, 0);
x_258 = !lean_is_exclusive(x_41);
if (x_258 == 0)
{
x_252 = x_41;
x_253 = x_258;
goto block_257;
}
else
{
lean_inc(x_251);
lean_dec(x_41);
x_252 = lean_box(0);
x_253 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_254; 
if (x_253 == 0)
{
x_254 = x_252;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_251);
x_254 = x_256;
goto block_255;
}
block_255:
{
return x_254;
}
}
}
block_38:
{
lean_object* x_28; 
x_28 = l_Lean_Meta_Grind_Arith_Linear_processVar(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_28) == 0)
{
lean_dec_ref(x_28);
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_ctor_get(x_28, 0);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
x_31 = x_28;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_28; 
x_15 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_16 = x_14;
x_17 = x_28;
goto block_27;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec_ref(x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_29 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_30 = x_14;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_1);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_26; 
x_13 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2);
x_14 = lean_st_mk_ref(x_13);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(x_14, x_1, x_2);
lean_dec(x_2);
x_15 = x_27;
goto block_25;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
x_15 = x_26;
goto block_25;
}
block_25:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
x_17 = x_15;
x_18 = x_24;
goto block_23;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_get(x_14);
lean_dec(x_14);
lean_dec(x_19);
if (x_18 == 0)
{
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_16);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_dec(x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_apply_10(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_17 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_16, x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_2, x_1);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_83; 
x_17 = lean_ctor_get(x_3, 1);
x_83 = !lean_is_exclusive(x_3);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_3, 0);
lean_dec(x_84);
x_18 = x_3;
x_19 = x_83;
goto block_82;
}
else
{
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_54; lean_object* x_55; lean_object* x_59; 
x_20 = lean_box(0);
x_59 = l_Lean_Meta_Grind_Arith_Linear_hasAssignment(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_62 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_54 = x_15;
x_55 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_del_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_62, 0);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
x_64 = x_62;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
uint8_t x_71; 
x_71 = 0;
x_54 = x_71;
x_55 = lean_box(0);
goto block_58;
}
}
else
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
lean_dec_ref(x_59);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
x_54 = x_73;
x_55 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_del_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_74 = lean_ctor_get(x_59, 0);
x_81 = !lean_is_exclusive(x_59);
if (x_81 == 0)
{
x_75 = x_59;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_59);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
block_53:
{
lean_object* x_23; 
x_23 = l_Lean_Meta_Grind_isInconsistent___redArg(x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_44; 
x_24 = lean_ctor_get(x_23, 0);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
x_25 = x_23;
x_26 = x_44;
goto block_43;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_44;
goto block_43;
}
block_43:
{
uint8_t x_27; 
x_27 = lean_unbox(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_del_object(x_25);
lean_dec(x_24);
x_28 = lean_box(x_22);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_20);
x_29 = x_18;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_28);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_2, x_30);
lean_dec(x_2);
x_2 = x_31;
x_3 = x_29;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_24);
x_36 = lean_box(x_22);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_36);
lean_ctor_set(x_18, 0, x_35);
x_37 = x_18;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_36);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_37);
x_38 = x_25;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_45 = lean_ctor_get(x_23, 0);
x_52 = !lean_is_exclusive(x_23);
if (x_52 == 0)
{
x_46 = x_23;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_23);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
block_58:
{
uint8_t x_56; 
x_56 = lean_unbox(x_17);
if (x_56 == 0)
{
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = x_54;
goto block_53;
}
else
{
uint8_t x_57; 
x_57 = lean_unbox(x_17);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = x_57;
goto block_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_array_get_size(x_15);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_box(0);
x_19 = lean_box(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(x_16, x_17, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_35; 
x_22 = lean_ctor_get(x_21, 0);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
x_23 = x_21;
x_24 = x_35;
goto block_34;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_26);
x_27 = x_23;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_25);
lean_dec(x_22);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec_ref(x_25);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_30);
x_31 = x_23;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
x_36 = lean_ctor_get(x_21, 0);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
x_37 = x_21;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_13, 0);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_45 = x_13;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_13);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Linear_check___lam__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_9, 2);
lean_inc_ref(x_12);
x_13 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_check___closed__0));
x_14 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_check___closed__1));
x_15 = lean_box(0);
x_16 = l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(x_13, x_12, x_14, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_check(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(x_1, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_18;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin);
}
#ifdef __cplusplus
}
#endif
