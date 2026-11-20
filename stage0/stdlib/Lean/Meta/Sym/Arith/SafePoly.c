// Lean compiler output
// Module: Lean.Meta.Sym.Arith.SafePoly
// Imports: public import Lean.Meta.Sym.Arith.Types public import Lean.Meta.Sym.Arith.Poly public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.Arith.EvalNum
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_numTerms(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "polynomial of degree "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = " exceeds threshold `(sym.arith.maxDegree := "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "polynomial with "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = " monomials exceeds threshold `(sym.arith.maxTerms := "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "sym arith poly"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_pow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_pow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_powNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_powNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___redArg(lean_object* v_x_1_, lean_object* v_cfg_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; 
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_10_ = lean_apply_8(v_x_1_, v_cfg_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___redArg___boxed(lean_object* v_x_11_, lean_object* v_cfg_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Meta_Sym_Arith_PolyM_run___redArg(v_x_11_, v_cfg_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
lean_dec(v_a_18_);
lean_dec_ref(v_a_17_);
lean_dec(v_a_16_);
lean_dec_ref(v_a_15_);
lean_dec(v_a_14_);
lean_dec_ref(v_a_13_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run(lean_object* v_00_u03b1_21_, lean_object* v_x_22_, lean_object* v_cfg_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_31_; 
lean_inc(v_a_29_);
lean_inc_ref(v_a_28_);
lean_inc(v_a_27_);
lean_inc_ref(v_a_26_);
lean_inc(v_a_25_);
lean_inc_ref(v_a_24_);
v___x_31_ = lean_apply_8(v_x_22_, v_cfg_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, lean_box(0));
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___boxed(lean_object* v_00_u03b1_32_, lean_object* v_x_33_, lean_object* v_cfg_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Meta_Sym_Arith_PolyM_run(v_00_u03b1_32_, v_x_33_, v_cfg_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar_spec__0(lean_object* v_a_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_nat_to_int(v_a_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_char_x3f_48_; 
v_char_x3f_48_ = lean_ctor_get(v_a_46_, 0);
if (lean_obj_tag(v_char_x3f_48_) == 1)
{
lean_object* v_val_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_val_49_ = lean_ctor_get(v_char_x3f_48_, 0);
lean_inc(v_val_49_);
v___x_50_ = lean_nat_to_int(v_val_49_);
v___x_51_ = lean_int_emod(v_a_45_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v_a_45_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
else
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v_a_45_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg___boxed(lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_a_56_, v_a_57_);
lean_dec_ref(v_a_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar(lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_a_60_, v_a_61_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___boxed(lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar(v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_79_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__1));
v___x_84_ = l_Lean_stringToMessageData(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__3));
v___x_87_ = l_Lean_stringToMessageData(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__5));
v___x_90_ = l_Lean_stringToMessageData(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__7));
v___x_93_ = l_Lean_stringToMessageData(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__9));
v___x_96_ = l_Lean_stringToMessageData(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(lean_object* v_p_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_maxTerms_x3f_112_; lean_object* v_maxDegree_x3f_113_; lean_object* v___y_115_; lean_object* v___y_116_; lean_object* v___y_117_; lean_object* v___y_118_; lean_object* v___y_119_; lean_object* v___y_120_; 
v_maxTerms_x3f_112_ = lean_ctor_get(v_a_98_, 1);
v_maxDegree_x3f_113_ = lean_ctor_get(v_a_98_, 2);
if (lean_obj_tag(v_maxTerms_x3f_112_) == 1)
{
lean_object* v_val_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_val_161_ = lean_ctor_get(v_maxTerms_x3f_112_, 0);
v___x_162_ = l_Lean_Grind_CommRing_Poly_numTerms(v_p_97_);
v___x_163_ = lean_nat_dec_lt(v_val_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v___x_162_);
v___y_115_ = v_a_99_;
v___y_116_ = v_a_100_;
v___y_117_ = v_a_101_;
v___y_118_ = v_a_102_;
v___y_119_ = v_a_103_;
v___y_120_ = v_a_104_;
goto v___jp_114_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_164_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8);
v___x_165_ = l_Nat_reprFast(v___x_162_);
v___x_166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
v___x_167_ = l_Lean_MessageData_ofFormat(v___x_166_);
v___x_168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_164_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10);
v___x_170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
lean_inc(v_val_161_);
v___x_171_ = l_Nat_reprFast(v_val_161_);
v___x_172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
v___x_173_ = l_Lean_MessageData_ofFormat(v___x_172_);
v___x_174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_170_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6);
v___x_176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_99_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; uint8_t v_verbose_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v_verbose_179_ = lean_ctor_get_uint8(v_a_178_, 0);
lean_dec(v_a_178_);
if (v_verbose_179_ == 0)
{
lean_dec_ref_known(v___x_176_, 2);
goto v___jp_106_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_Sym_reportIssue(v___x_176_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_dec_ref_known(v___x_180_, 1);
goto v___jp_106_;
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec_ref_known(v___x_176_, 2);
v_a_189_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_177_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_177_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
else
{
v___y_115_ = v_a_99_;
v___y_116_ = v_a_100_;
v___y_117_ = v_a_101_;
v___y_118_ = v_a_102_;
v___y_119_ = v_a_103_;
v___y_120_ = v_a_104_;
goto v___jp_114_;
}
v___jp_106_:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
v___jp_109_:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
v___jp_114_:
{
if (lean_obj_tag(v_maxDegree_x3f_113_) == 1)
{
lean_object* v_val_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_val_121_ = lean_ctor_get(v_maxDegree_x3f_113_, 0);
v___x_122_ = l_Lean_Grind_CommRing_Poly_degree(v_p_97_);
v___x_123_ = lean_nat_dec_lt(v_val_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v___x_122_);
v___x_124_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__0));
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_126_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2);
v___x_127_ = l_Nat_reprFast(v___x_122_);
v___x_128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
v___x_129_ = l_Lean_MessageData_ofFormat(v___x_128_);
v___x_130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_126_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4);
v___x_132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
lean_inc(v_val_121_);
v___x_133_ = l_Nat_reprFast(v_val_121_);
v___x_134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
v___x_135_ = l_Lean_MessageData_ofFormat(v___x_134_);
v___x_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_132_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6);
v___x_138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_115_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; uint8_t v_verbose_141_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
lean_dec_ref_known(v___x_139_, 1);
v_verbose_141_ = lean_ctor_get_uint8(v_a_140_, 0);
lean_dec(v_a_140_);
if (v_verbose_141_ == 0)
{
lean_dec_ref_known(v___x_138_, 2);
goto v___jp_109_;
}
else
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Sym_reportIssue(v___x_138_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_dec_ref_known(v___x_142_, 1);
goto v___jp_109_;
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec_ref_known(v___x_138_, 2);
v_a_151_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_139_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_139_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__0));
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___boxed(lean_object* v_p_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(v_p_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec_ref(v_p_197_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(lean_object* v_p_207_, lean_object* v_k_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_char_x3f_211_; 
v_char_x3f_211_ = lean_ctor_get(v_a_209_, 0);
if (lean_obj_tag(v_char_x3f_211_) == 1)
{
lean_object* v_val_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_val_212_ = lean_ctor_get(v_char_x3f_211_, 0);
lean_inc(v_val_212_);
v___x_213_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_207_, v_k_208_, v_val_212_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_207_, v_k_208_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg___boxed(lean_object* v_p_219_, lean_object* v_k_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_219_, v_k_220_, v_a_221_);
lean_dec_ref(v_a_221_);
lean_dec(v_k_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst(lean_object* v_p_224_, lean_object* v_k_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_224_, v_k_225_, v_a_226_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___boxed(lean_object* v_p_235_, lean_object* v_k_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst(v_p_235_, v_k_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_k_236_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(lean_object* v_k_246_, lean_object* v_p_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_char_x3f_250_; 
v_char_x3f_250_ = lean_ctor_get(v_a_248_, 0);
if (lean_obj_tag(v_char_x3f_250_) == 1)
{
lean_object* v_val_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_val_251_ = lean_ctor_get(v_char_x3f_250_, 0);
lean_inc(v_val_251_);
v___x_252_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_246_, v_p_247_, v_val_251_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_246_, v_p_247_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg___boxed(lean_object* v_k_258_, lean_object* v_p_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_258_, v_p_259_, v_a_260_);
lean_dec_ref(v_a_260_);
lean_dec(v_k_258_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst(lean_object* v_k_263_, lean_object* v_p_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_263_, v_p_264_, v_a_265_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___boxed(lean_object* v_k_274_, lean_object* v_p_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst(v_k_274_, v_p_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_k_274_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(lean_object* v_k_285_, lean_object* v_m_286_, lean_object* v_p_287_, lean_object* v_a_288_){
_start:
{
uint8_t v_commutative_290_; 
v_commutative_290_ = lean_ctor_get_uint8(v_a_288_, sizeof(void*)*3 + 1);
if (v_commutative_290_ == 0)
{
lean_object* v_char_x3f_291_; 
v_char_x3f_291_ = lean_ctor_get(v_a_288_, 0);
if (lean_obj_tag(v_char_x3f_291_) == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_285_, v_m_286_, v_p_287_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_val_295_ = lean_ctor_get(v_char_x3f_291_, 0);
lean_inc(v_val_295_);
v___x_296_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_285_, v_m_286_, v_p_287_, v_val_295_);
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
else
{
lean_object* v_char_x3f_299_; 
v_char_x3f_299_ = lean_ctor_get(v_a_288_, 0);
if (lean_obj_tag(v_char_x3f_299_) == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_285_, v_m_286_, v_p_287_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v_val_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_val_303_ = lean_ctor_get(v_char_x3f_299_, 0);
lean_inc(v_val_303_);
v___x_304_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_285_, v_m_286_, v_p_287_, v_val_303_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg___boxed(lean_object* v_k_307_, lean_object* v_m_308_, lean_object* v_p_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_307_, v_m_308_, v_p_309_, v_a_310_);
lean_dec_ref(v_a_310_);
lean_dec(v_k_307_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon(lean_object* v_k_313_, lean_object* v_m_314_, lean_object* v_p_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_313_, v_m_314_, v_p_315_, v_a_316_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___boxed(lean_object* v_k_325_, lean_object* v_m_326_, lean_object* v_p_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon(v_k_325_, v_m_326_, v_p_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_k_325_);
return v_res_336_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = l_Lean_maxRecDepthErrorMessage;
v___x_343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3);
v___x_345_ = l_Lean_MessageData_ofFormat(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4);
v___x_347_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__2));
v___x_348_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(lean_object* v_ref_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_ref_349_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___boxed(lean_object* v_ref_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0(lean_object* v_00_u03b1_357_, lean_object* v_ref_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_358_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___boxed(lean_object* v_00_u03b1_368_, lean_object* v_ref_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0(v_00_u03b1_368_, v_ref_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_nat_to_int(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(lean_object* v_p_u2081_381_, lean_object* v_p_u2082_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_toCold_391_; lean_object* v_currRecDepth_392_; lean_object* v_ref_393_; uint16_t v_optionFlags_394_; uint8_t v_suppressElabErrors_395_; uint8_t v_checkDeprecated_396_; uint8_t v_isRecordingDeps_397_; lean_object* v_maxRecDepth_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_toCold_391_ = lean_ctor_get(v_a_388_, 0);
lean_inc_ref(v_toCold_391_);
v_currRecDepth_392_ = lean_ctor_get(v_a_388_, 1);
lean_inc(v_currRecDepth_392_);
v_ref_393_ = lean_ctor_get(v_a_388_, 2);
lean_inc(v_ref_393_);
v_optionFlags_394_ = lean_ctor_get_uint16(v_a_388_, sizeof(void*)*3);
v_suppressElabErrors_395_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*3 + 2);
v_checkDeprecated_396_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*3 + 3);
v_isRecordingDeps_397_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_388_);
v_maxRecDepth_559_ = lean_ctor_get(v_toCold_391_, 3);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_nat_dec_eq(v_maxRecDepth_559_, v___x_560_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; 
v___x_562_ = lean_nat_dec_eq(v_currRecDepth_392_, v_maxRecDepth_559_);
if (v___x_562_ == 0)
{
goto v___jp_398_;
}
else
{
lean_object* v___x_563_; 
lean_dec(v_currRecDepth_392_);
lean_dec_ref(v_toCold_391_);
lean_dec_ref(v_p_u2082_382_);
lean_dec_ref(v_p_u2081_381_);
v___x_563_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_393_);
return v___x_563_;
}
}
else
{
goto v___jp_398_;
}
v___jp_398_:
{
if (lean_obj_tag(v_p_u2081_381_) == 0)
{
lean_dec(v_ref_393_);
lean_dec(v_currRecDepth_392_);
lean_dec_ref(v_toCold_391_);
if (lean_obj_tag(v_p_u2082_382_) == 0)
{
lean_object* v_k_399_; lean_object* v_k_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_437_; 
v_k_399_ = lean_ctor_get(v_p_u2081_381_, 0);
lean_inc(v_k_399_);
lean_dec_ref_known(v_p_u2081_381_, 1);
v_k_400_ = lean_ctor_get(v_p_u2082_382_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_p_u2082_382_);
if (v_isSharedCheck_437_ == 0)
{
v___x_402_ = v_p_u2082_382_;
v_isShared_403_ = v_isSharedCheck_437_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_k_400_);
lean_dec(v_p_u2082_382_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_437_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_int_add(v_k_399_, v_k_400_);
lean_dec(v_k_400_);
lean_dec(v_k_399_);
v___x_405_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_404_, v_a_383_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_428_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_428_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_428_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_428_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
if (lean_obj_tag(v_a_406_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_412_; 
lean_del_object(v___x_402_);
v___x_410_ = lean_box(0);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
else
{
lean_object* v_val_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_427_; 
v_val_414_ = lean_ctor_get(v_a_406_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_427_ == 0)
{
v___x_416_ = v_a_406_;
v_isShared_417_ = v_isSharedCheck_427_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_val_414_);
lean_dec(v_a_406_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_427_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v_val_414_);
v___x_419_ = v___x_402_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_val_414_);
v___x_419_ = v_reuseFailAlloc_426_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_425_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_423_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_421_);
v___x_423_ = v___x_408_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_del_object(v___x_402_);
v_a_429_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_405_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_405_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
else
{
lean_object* v_k_438_; lean_object* v___x_439_; 
v_k_438_ = lean_ctor_get(v_p_u2081_381_, 0);
lean_inc(v_k_438_);
lean_dec_ref_known(v_p_u2081_381_, 1);
v___x_439_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_u2082_382_, v_k_438_, v_a_383_);
lean_dec(v_k_438_);
return v___x_439_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_382_) == 0)
{
lean_object* v_k_440_; lean_object* v___x_441_; 
lean_dec(v_ref_393_);
lean_dec(v_currRecDepth_392_);
lean_dec_ref(v_toCold_391_);
v_k_440_ = lean_ctor_get(v_p_u2082_382_, 0);
lean_inc(v_k_440_);
lean_dec_ref_known(v_p_u2082_382_, 1);
v___x_441_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_u2081_381_, v_k_440_, v_a_383_);
lean_dec(v_k_440_);
return v___x_441_;
}
else
{
lean_object* v_k_442_; lean_object* v_v_443_; lean_object* v_p_444_; lean_object* v_k_445_; lean_object* v_v_446_; lean_object* v_p_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_k_442_ = lean_ctor_get(v_p_u2081_381_, 0);
v_v_443_ = lean_ctor_get(v_p_u2081_381_, 1);
v_p_444_ = lean_ctor_get(v_p_u2081_381_, 2);
v_k_445_ = lean_ctor_get(v_p_u2082_382_, 0);
v_v_446_ = lean_ctor_get(v_p_u2082_382_, 1);
v_p_447_ = lean_ctor_get(v_p_u2082_382_, 2);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_add(v_currRecDepth_392_, v___x_448_);
lean_dec(v_currRecDepth_392_);
v___x_450_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_450_, 0, v_toCold_391_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_ctor_set(v___x_450_, 2, v_ref_393_);
lean_ctor_set_uint16(v___x_450_, sizeof(void*)*3, v_optionFlags_394_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*3 + 2, v_suppressElabErrors_395_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*3 + 3, v_checkDeprecated_396_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*3 + 4, v_isRecordingDeps_397_);
v___x_451_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_443_, v_v_446_);
switch(v___x_451_)
{
case 0:
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_476_; 
lean_inc_ref(v_p_447_);
lean_inc(v_v_446_);
lean_inc(v_k_445_);
v_isSharedCheck_476_ = !lean_is_exclusive(v_p_u2082_382_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; 
v_unused_477_ = lean_ctor_get(v_p_u2082_382_, 2);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_p_u2082_382_, 1);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_p_u2082_382_, 0);
lean_dec(v_unused_479_);
v___x_453_ = v_p_u2082_382_;
v_isShared_454_ = v_isSharedCheck_476_;
goto v_resetjp_452_;
}
else
{
lean_dec(v_p_u2082_382_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_476_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_381_, v_p_447_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v___x_450_, v_a_389_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
if (lean_obj_tag(v_a_456_) == 0)
{
lean_del_object(v___x_453_);
lean_dec(v_v_446_);
lean_dec(v_k_445_);
return v___x_455_;
}
else
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_474_; 
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_455_, 0);
lean_dec(v_unused_475_);
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_474_;
goto v_resetjp_457_;
}
else
{
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_474_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_val_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_473_; 
v_val_460_ = lean_ctor_get(v_a_456_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_473_ == 0)
{
v___x_462_ = v_a_456_;
v_isShared_463_ = v_isSharedCheck_473_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_val_460_);
lean_dec(v_a_456_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_473_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 2, v_val_460_);
v___x_465_ = v___x_453_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_k_445_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_v_446_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_val_460_);
v___x_465_ = v_reuseFailAlloc_472_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_467_);
v___x_469_ = v___x_458_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_453_);
lean_dec(v_v_446_);
lean_dec(v_k_445_);
return v___x_455_;
}
}
}
case 1:
{
lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_527_; 
lean_inc_ref(v_p_447_);
lean_inc(v_k_445_);
lean_inc_ref(v_p_444_);
lean_inc(v_v_443_);
lean_inc(v_k_442_);
lean_dec_ref_known(v_p_u2081_381_, 3);
v_isSharedCheck_527_ = !lean_is_exclusive(v_p_u2082_382_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; lean_object* v_unused_529_; lean_object* v_unused_530_; 
v_unused_528_ = lean_ctor_get(v_p_u2082_382_, 2);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_p_u2082_382_, 1);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_p_u2082_382_, 0);
lean_dec(v_unused_530_);
v___x_481_ = v_p_u2082_382_;
v_isShared_482_ = v_isSharedCheck_527_;
goto v_resetjp_480_;
}
else
{
lean_dec(v_p_u2082_382_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_527_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_int_add(v_k_442_, v_k_445_);
lean_dec(v_k_445_);
lean_dec(v_k_442_);
v___x_484_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_483_, v_a_383_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_518_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_518_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_518_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_518_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
if (lean_obj_tag(v_a_485_) == 0)
{
lean_object* v___x_489_; lean_object* v___x_491_; 
lean_del_object(v___x_481_);
lean_dec_ref_known(v___x_450_, 3);
lean_dec_ref(v_p_447_);
lean_dec_ref(v_p_444_);
lean_dec(v_v_443_);
v___x_489_ = lean_box(0);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
else
{
lean_object* v_val_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
lean_del_object(v___x_487_);
v_val_493_ = lean_ctor_get(v_a_485_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v_a_485_, 1);
v___x_494_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0);
v___x_495_ = lean_int_dec_eq(v_val_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
v___x_496_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_444_, v_p_447_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v___x_450_, v_a_389_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
if (lean_obj_tag(v_a_497_) == 0)
{
lean_dec(v_val_493_);
lean_del_object(v___x_481_);
lean_dec(v_v_443_);
return v___x_496_;
}
else
{
lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_515_; 
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v___x_496_, 0);
lean_dec(v_unused_516_);
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
else
{
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_val_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_514_; 
v_val_501_ = lean_ctor_get(v_a_497_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_514_ == 0)
{
v___x_503_ = v_a_497_;
v_isShared_504_ = v_isSharedCheck_514_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_val_501_);
lean_dec(v_a_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_514_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 2, v_val_501_);
lean_ctor_set(v___x_481_, 1, v_v_443_);
lean_ctor_set(v___x_481_, 0, v_val_493_);
v___x_506_ = v___x_481_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_val_493_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_val_501_);
v___x_506_ = v_reuseFailAlloc_513_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_506_);
v___x_508_ = v___x_503_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_512_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_510_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_508_);
v___x_510_ = v___x_499_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
}
else
{
lean_dec(v_val_493_);
lean_del_object(v___x_481_);
lean_dec(v_v_443_);
return v___x_496_;
}
}
else
{
lean_dec(v_val_493_);
lean_del_object(v___x_481_);
lean_dec(v_v_443_);
v_p_u2081_381_ = v_p_444_;
v_p_u2082_382_ = v_p_447_;
v_a_388_ = v___x_450_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_481_);
lean_dec_ref_known(v___x_450_, 3);
lean_dec_ref(v_p_447_);
lean_dec_ref(v_p_444_);
lean_dec(v_v_443_);
v_a_519_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_484_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_484_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
default: 
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_555_; 
lean_inc_ref(v_p_444_);
lean_inc(v_v_443_);
lean_inc(v_k_442_);
v_isSharedCheck_555_ = !lean_is_exclusive(v_p_u2081_381_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; 
v_unused_556_ = lean_ctor_get(v_p_u2081_381_, 2);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_p_u2081_381_, 1);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_p_u2081_381_, 0);
lean_dec(v_unused_558_);
v___x_532_ = v_p_u2081_381_;
v_isShared_533_ = v_isSharedCheck_555_;
goto v_resetjp_531_;
}
else
{
lean_dec(v_p_u2081_381_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_555_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_444_, v_p_u2082_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v___x_450_, v_a_389_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
if (lean_obj_tag(v_a_535_) == 0)
{
lean_del_object(v___x_532_);
lean_dec(v_v_443_);
lean_dec(v_k_442_);
return v___x_534_;
}
else
{
lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_553_; 
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v___x_534_, 0);
lean_dec(v_unused_554_);
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_553_;
goto v_resetjp_536_;
}
else
{
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_553_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_552_; 
v_val_539_ = lean_ctor_get(v_a_535_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_a_535_);
if (v_isSharedCheck_552_ == 0)
{
v___x_541_ = v_a_535_;
v_isShared_542_ = v_isSharedCheck_552_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v_a_535_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_552_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v_val_539_);
v___x_544_ = v___x_532_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_k_442_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_val_539_);
v___x_544_ = v_reuseFailAlloc_551_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_550_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_548_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_546_);
v___x_548_ = v___x_537_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_532_);
lean_dec(v_v_443_);
lean_dec(v_k_442_);
return v___x_534_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___boxed(lean_object* v_p_u2081_564_, lean_object* v_p_u2082_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_564_, v_p_u2082_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec_ref(v_a_566_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine(lean_object* v_p_u2081_575_, lean_object* v_p_u2082_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
lean_inc_ref(v_a_582_);
v___x_585_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_575_, v_p_u2082_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
if (lean_obj_tag(v_a_586_) == 0)
{
return v___x_585_;
}
else
{
lean_object* v_val_587_; lean_object* v___x_588_; 
lean_inc_ref(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v_val_587_ = lean_ctor_get(v_a_586_, 0);
v___x_588_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(v_val_587_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_600_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_600_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
if (lean_obj_tag(v_a_589_) == 0)
{
lean_object* v___x_593_; lean_object* v___x_595_; 
lean_dec_ref_known(v_a_586_, 1);
v___x_593_ = lean_box(0);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
lean_object* v___x_598_; 
lean_dec_ref_known(v_a_589_, 1);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v_a_586_);
v___x_598_ = v___x_591_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_586_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref_known(v_a_586_, 1);
v_a_601_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_588_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_588_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine___boxed(lean_object* v_p_u2081_609_, lean_object* v_p_u2082_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_p_u2081_609_, v_p_u2082_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec_ref(v_a_611_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(lean_object* v_p_u2082_621_, lean_object* v_p_u2081_622_, lean_object* v_acc_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_toCold_632_; lean_object* v_currRecDepth_633_; lean_object* v_ref_634_; uint16_t v_optionFlags_635_; uint8_t v_suppressElabErrors_636_; uint8_t v_checkDeprecated_637_; uint8_t v_isRecordingDeps_638_; lean_object* v_maxRecDepth_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_toCold_632_ = lean_ctor_get(v_a_629_, 0);
lean_inc_ref(v_toCold_632_);
v_currRecDepth_633_ = lean_ctor_get(v_a_629_, 1);
lean_inc(v_currRecDepth_633_);
v_ref_634_ = lean_ctor_get(v_a_629_, 2);
lean_inc(v_ref_634_);
v_optionFlags_635_ = lean_ctor_get_uint16(v_a_629_, sizeof(void*)*3);
v_suppressElabErrors_636_ = lean_ctor_get_uint8(v_a_629_, sizeof(void*)*3 + 2);
v_checkDeprecated_637_ = lean_ctor_get_uint8(v_a_629_, sizeof(void*)*3 + 3);
v_isRecordingDeps_638_ = lean_ctor_get_uint8(v_a_629_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_629_);
v_maxRecDepth_668_ = lean_ctor_get(v_toCold_632_, 3);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_nat_dec_eq(v_maxRecDepth_668_, v___x_669_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = lean_nat_dec_eq(v_currRecDepth_633_, v_maxRecDepth_668_);
if (v___x_671_ == 0)
{
goto v___jp_639_;
}
else
{
lean_object* v___x_672_; 
lean_dec(v_currRecDepth_633_);
lean_dec_ref(v_toCold_632_);
lean_dec_ref(v_acc_623_);
lean_dec_ref(v_p_u2081_622_);
lean_dec_ref(v_p_u2082_621_);
v___x_672_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_634_);
return v___x_672_;
}
}
else
{
goto v___jp_639_;
}
v___jp_639_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_currRecDepth_633_, v___x_640_);
lean_dec(v_currRecDepth_633_);
v___x_642_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_642_, 0, v_toCold_632_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_ctor_set(v___x_642_, 2, v_ref_634_);
lean_ctor_set_uint16(v___x_642_, sizeof(void*)*3, v_optionFlags_635_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*3 + 2, v_suppressElabErrors_636_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*3 + 3, v_checkDeprecated_637_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*3 + 4, v_isRecordingDeps_638_);
if (lean_obj_tag(v_p_u2081_622_) == 0)
{
lean_object* v_k_643_; lean_object* v___x_644_; lean_object* v_a_645_; lean_object* v_val_646_; lean_object* v___x_647_; 
v_k_643_ = lean_ctor_get(v_p_u2081_622_, 0);
lean_inc(v_k_643_);
lean_dec_ref_known(v_p_u2081_622_, 1);
v___x_644_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_643_, v_p_u2082_621_, v_a_624_);
lean_dec(v_k_643_);
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref(v___x_644_);
v_val_646_ = lean_ctor_get(v_a_645_, 0);
lean_inc(v_val_646_);
lean_dec(v_a_645_);
v___x_647_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_acc_623_, v_val_646_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v___x_642_, v_a_630_);
lean_dec_ref_known(v___x_642_, 3);
return v___x_647_;
}
else
{
lean_object* v_k_648_; lean_object* v_v_649_; lean_object* v_p_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_k_648_ = lean_ctor_get(v_p_u2081_622_, 0);
lean_inc(v_k_648_);
v_v_649_ = lean_ctor_get(v_p_u2081_622_, 1);
lean_inc(v_v_649_);
v_p_650_ = lean_ctor_get(v_p_u2081_622_, 2);
lean_inc_ref(v_p_650_);
lean_dec_ref_known(v_p_u2081_622_, 3);
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___closed__0));
v___x_652_ = l_Lean_Core_checkSystem(v___x_651_, v___x_642_, v_a_630_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v_val_655_; lean_object* v___x_656_; 
lean_dec_ref_known(v___x_652_, 1);
lean_inc_ref(v_p_u2082_621_);
v___x_653_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_648_, v_v_649_, v_p_u2082_621_, v_a_624_);
lean_dec(v_k_648_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref(v___x_653_);
v_val_655_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_val_655_);
lean_dec(v_a_654_);
v___x_656_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_acc_623_, v_val_655_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v___x_642_, v_a_630_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
if (lean_obj_tag(v_a_657_) == 0)
{
lean_dec_ref(v_p_650_);
lean_dec_ref_known(v___x_642_, 3);
lean_dec_ref(v_p_u2082_621_);
return v___x_656_;
}
else
{
lean_object* v_val_658_; 
lean_inc_ref(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v_val_658_ = lean_ctor_get(v_a_657_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v_a_657_, 1);
v_p_u2081_622_ = v_p_650_;
v_acc_623_ = v_val_658_;
v_a_629_ = v___x_642_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_650_);
lean_dec_ref_known(v___x_642_, 3);
lean_dec_ref(v_p_u2082_621_);
return v___x_656_;
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_p_650_);
lean_dec(v_v_649_);
lean_dec(v_k_648_);
lean_dec_ref_known(v___x_642_, 3);
lean_dec_ref(v_acc_623_);
lean_dec_ref(v_p_u2082_621_);
v_a_660_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_652_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_652_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___boxed(lean_object* v_p_u2082_673_, lean_object* v_p_u2081_674_, lean_object* v_acc_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(v_p_u2082_673_, v_p_u2081_674_, v_acc_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_684_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul(lean_object* v_p_u2081_687_, lean_object* v_p_u2082_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0, &l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0);
lean_inc_ref(v_a_694_);
v___x_698_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(v_p_u2082_688_, v_p_u2081_687_, v___x_697_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul___boxed(lean_object* v_p_u2081_699_, lean_object* v_p_u2082_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_u2081_699_, v_p_u2082_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_to_int(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(lean_object* v_p_716_, lean_object* v_k_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_toCold_726_; lean_object* v_currRecDepth_727_; lean_object* v_ref_728_; uint16_t v_optionFlags_729_; uint8_t v_suppressElabErrors_730_; uint8_t v_checkDeprecated_731_; uint8_t v_isRecordingDeps_732_; lean_object* v_maxRecDepth_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_toCold_726_ = lean_ctor_get(v_a_723_, 0);
v_currRecDepth_727_ = lean_ctor_get(v_a_723_, 1);
v_ref_728_ = lean_ctor_get(v_a_723_, 2);
v_optionFlags_729_ = lean_ctor_get_uint16(v_a_723_, sizeof(void*)*3);
v_suppressElabErrors_730_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*3 + 2);
v_checkDeprecated_731_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*3 + 3);
v_isRecordingDeps_732_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*3 + 4);
v_maxRecDepth_755_ = lean_ctor_get(v_toCold_726_, 3);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_nat_dec_eq(v_maxRecDepth_755_, v___x_756_);
if (v___x_757_ == 0)
{
uint8_t v___x_758_; 
v___x_758_ = lean_nat_dec_eq(v_currRecDepth_727_, v_maxRecDepth_755_);
if (v___x_758_ == 0)
{
goto v___jp_733_;
}
else
{
lean_object* v___x_759_; 
lean_dec_ref(v_p_716_);
lean_inc(v_ref_728_);
v___x_759_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_728_);
return v___x_759_;
}
}
else
{
goto v___jp_733_;
}
v___jp_733_:
{
lean_object* v_zero_734_; uint8_t v_isZero_735_; 
v_zero_734_ = lean_unsigned_to_nat(0u);
v_isZero_735_ = lean_nat_dec_eq(v_k_717_, v_zero_734_);
if (v_isZero_735_ == 1)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v_p_716_);
v___x_736_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
else
{
lean_object* v_one_738_; lean_object* v_n_739_; uint8_t v_isZero_740_; 
v_one_738_ = lean_unsigned_to_nat(1u);
v_n_739_ = lean_nat_sub(v_k_717_, v_one_738_);
v_isZero_740_ = lean_nat_dec_eq(v_n_739_, v_zero_734_);
if (v_isZero_740_ == 1)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v_n_739_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_p_716_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
else
{
lean_object* v_n_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v_isZero_746_; 
v_n_743_ = lean_nat_sub(v_n_739_, v_one_738_);
lean_dec(v_n_739_);
v___x_744_ = lean_nat_add(v_currRecDepth_727_, v_one_738_);
lean_inc(v_ref_728_);
lean_inc_ref(v_toCold_726_);
v___x_745_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_745_, 0, v_toCold_726_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_ctor_set(v___x_745_, 2, v_ref_728_);
lean_ctor_set_uint16(v___x_745_, sizeof(void*)*3, v_optionFlags_729_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3 + 2, v_suppressElabErrors_730_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3 + 3, v_checkDeprecated_731_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3 + 4, v_isRecordingDeps_732_);
v_isZero_746_ = lean_nat_dec_eq(v_n_743_, v_zero_734_);
if (v_isZero_746_ == 1)
{
lean_object* v___x_747_; 
lean_dec(v_n_743_);
lean_inc_ref(v_p_716_);
v___x_747_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_716_, v_p_716_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v___x_745_, v_a_724_);
lean_dec_ref_known(v___x_745_, 3);
return v___x_747_;
}
else
{
lean_object* v_n_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_n_748_ = lean_nat_sub(v_n_743_, v_one_738_);
lean_dec(v_n_743_);
v___x_749_ = lean_unsigned_to_nat(2u);
v___x_750_ = lean_nat_add(v_n_748_, v___x_749_);
lean_dec(v_n_748_);
lean_inc_ref(v_p_716_);
v___x_751_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_716_, v___x_750_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v___x_745_, v_a_724_);
lean_dec(v___x_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
if (lean_obj_tag(v_a_752_) == 0)
{
lean_dec_ref_known(v___x_745_, 3);
lean_dec_ref(v_p_716_);
return v___x_751_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_754_; 
lean_inc_ref(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v_val_753_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_a_752_, 1);
v___x_754_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_716_, v_val_753_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v___x_745_, v_a_724_);
lean_dec_ref_known(v___x_745_, 3);
return v___x_754_;
}
}
else
{
lean_dec_ref_known(v___x_745_, 3);
lean_dec_ref(v_p_716_);
return v___x_751_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___boxed(lean_object* v_p_760_, lean_object* v_k_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_760_, v_k_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_k_761_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(lean_object* v_p_771_, lean_object* v_k_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_toCold_781_; lean_object* v_currRecDepth_782_; lean_object* v_ref_783_; uint16_t v_optionFlags_784_; uint8_t v_suppressElabErrors_785_; uint8_t v_checkDeprecated_786_; uint8_t v_isRecordingDeps_787_; lean_object* v_maxRecDepth_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_toCold_781_ = lean_ctor_get(v_a_778_, 0);
v_currRecDepth_782_ = lean_ctor_get(v_a_778_, 1);
v_ref_783_ = lean_ctor_get(v_a_778_, 2);
v_optionFlags_784_ = lean_ctor_get_uint16(v_a_778_, sizeof(void*)*3);
v_suppressElabErrors_785_ = lean_ctor_get_uint8(v_a_778_, sizeof(void*)*3 + 2);
v_checkDeprecated_786_ = lean_ctor_get_uint8(v_a_778_, sizeof(void*)*3 + 3);
v_isRecordingDeps_787_ = lean_ctor_get_uint8(v_a_778_, sizeof(void*)*3 + 4);
v_maxRecDepth_806_ = lean_ctor_get(v_toCold_781_, 3);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_nat_dec_eq(v_maxRecDepth_806_, v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_eq(v_currRecDepth_782_, v_maxRecDepth_806_);
if (v___x_809_ == 0)
{
goto v___jp_788_;
}
else
{
lean_object* v___x_810_; 
lean_dec_ref(v_p_771_);
lean_inc(v_ref_783_);
v___x_810_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_783_);
return v___x_810_;
}
}
else
{
goto v___jp_788_;
}
v___jp_788_:
{
lean_object* v_zero_789_; uint8_t v_isZero_790_; 
v_zero_789_ = lean_unsigned_to_nat(0u);
v_isZero_790_ = lean_nat_dec_eq(v_k_772_, v_zero_789_);
if (v_isZero_790_ == 1)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v_p_771_);
v___x_791_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
else
{
lean_object* v_one_793_; lean_object* v_n_794_; uint8_t v_isZero_795_; 
v_one_793_ = lean_unsigned_to_nat(1u);
v_n_794_ = lean_nat_sub(v_k_772_, v_one_793_);
v_isZero_795_ = lean_nat_dec_eq(v_n_794_, v_zero_789_);
if (v_isZero_795_ == 1)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_n_794_);
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_p_771_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
else
{
lean_object* v_n_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_n_798_ = lean_nat_sub(v_n_794_, v_one_793_);
lean_dec(v_n_794_);
v___x_799_ = lean_nat_add(v_currRecDepth_782_, v_one_793_);
lean_inc(v_ref_783_);
lean_inc_ref(v_toCold_781_);
v___x_800_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_800_, 0, v_toCold_781_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
lean_ctor_set(v___x_800_, 2, v_ref_783_);
lean_ctor_set_uint16(v___x_800_, sizeof(void*)*3, v_optionFlags_784_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*3 + 2, v_suppressElabErrors_785_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*3 + 3, v_checkDeprecated_786_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*3 + 4, v_isRecordingDeps_787_);
v___x_801_ = lean_nat_add(v_n_798_, v_one_793_);
lean_dec(v_n_798_);
lean_inc_ref(v_p_771_);
v___x_802_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_771_, v___x_801_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v___x_800_, v_a_779_);
lean_dec(v___x_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
if (lean_obj_tag(v_a_803_) == 0)
{
lean_dec_ref_known(v___x_800_, 3);
lean_dec_ref(v_p_771_);
return v___x_802_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_805_; 
lean_inc_ref(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v_val_804_ = lean_ctor_get(v_a_803_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_a_803_, 1);
v___x_805_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_804_, v_p_771_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v___x_800_, v_a_779_);
lean_dec_ref_known(v___x_800_, 3);
return v___x_805_;
}
}
else
{
lean_dec_ref_known(v___x_800_, 3);
lean_dec_ref(v_p_771_);
return v___x_802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC___boxed(lean_object* v_p_811_, lean_object* v_k_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_811_, v_k_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_k_812_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_pow(lean_object* v_p_822_, lean_object* v_k_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
uint8_t v_commutative_832_; 
v_commutative_832_ = lean_ctor_get_uint8(v_a_824_, sizeof(void*)*3 + 1);
if (v_commutative_832_ == 0)
{
lean_object* v___x_833_; 
v___x_833_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_822_, v_k_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
return v___x_833_;
}
else
{
lean_object* v___x_834_; 
v___x_834_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_822_, v_k_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_pow___boxed(lean_object* v_p_835_, lean_object* v_k_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_p_835_, v_k_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_k_836_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg(lean_object* v_k_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg___boxed(lean_object* v_k_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg(v_k_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27(lean_object* v_k_864_, lean_object* v_x_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_864_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___boxed(lean_object* v_k_874_, lean_object* v_x_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27(v_k_874_, v_x_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec_ref(v_x_875_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(lean_object* v_x_884_, lean_object* v_k_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_maxDegree_x3f_904_; 
v_maxDegree_x3f_904_ = lean_ctor_get(v_a_886_, 2);
if (lean_obj_tag(v_maxDegree_x3f_904_) == 1)
{
lean_object* v_val_905_; uint8_t v___x_906_; 
v_val_905_ = lean_ctor_get(v_maxDegree_x3f_904_, 0);
v___x_906_ = lean_nat_dec_lt(v_val_905_, v_k_885_);
if (v___x_906_ == 0)
{
goto v___jp_894_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_x_884_);
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2);
v___x_908_ = l_Nat_reprFast(v_k_885_);
v___x_909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
v___x_910_ = l_Lean_MessageData_ofFormat(v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_907_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
lean_inc(v_val_905_);
v___x_914_ = l_Nat_reprFast(v_val_905_);
v___x_915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
v___x_916_ = l_Lean_MessageData_ofFormat(v___x_915_);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_913_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_887_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; uint8_t v_verbose_922_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v_verbose_922_ = lean_ctor_get_uint8(v_a_921_, 0);
lean_dec(v_a_921_);
if (v_verbose_922_ == 0)
{
lean_dec_ref_known(v___x_919_, 2);
goto v___jp_901_;
}
else
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Meta_Sym_reportIssue(v___x_919_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_dec_ref_known(v___x_923_, 1);
goto v___jp_901_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref_known(v___x_919_, 2);
v_a_932_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_920_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_920_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
else
{
goto v___jp_894_;
}
v___jp_894_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_x_884_);
lean_ctor_set(v___x_895_, 1, v_k_885_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_897_);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
v___jp_901_:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_box(0);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar___boxed(lean_object* v_x_940_, lean_object* v_k_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_x_940_, v_k_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg(lean_object* v_n_951_, lean_object* v_a_952_){
_start:
{
uint8_t v_semiring_954_; 
v_semiring_954_ = lean_ctor_get_uint8(v_a_952_, sizeof(void*)*3);
if (v_semiring_954_ == 0)
{
lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_972_; 
v___x_955_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_n_951_, v_a_952_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_972_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_972_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_972_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_val_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_971_; 
v_val_960_ = lean_ctor_get(v_a_956_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_956_);
if (v_isSharedCheck_971_ == 0)
{
v___x_962_ = v_a_956_;
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_val_960_);
lean_dec(v_a_956_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_val_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_966_);
v___x_968_ = v___x_958_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_973_ = lean_nat_abs(v_n_951_);
lean_dec(v_n_951_);
v___x_974_ = lean_nat_to_int(v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg___boxed(lean_object* v_n_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg(v_n_978_, v_a_979_);
lean_dec_ref(v_a_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode(lean_object* v_n_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg(v_n_982_, v_a_983_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___boxed(lean_object* v_n_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Meta_Sym_Arith_SafePoly_numNode(v_n_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(lean_object* v_k_1002_, lean_object* v_n_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
lean_inc(v_k_1002_);
v___x_1012_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1002_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1056_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1056_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1056_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
if (lean_obj_tag(v_a_1013_) == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_dec(v_k_1002_);
v___x_1017_ = lean_box(0);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
else
{
lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1054_; 
v_isSharedCheck_1054_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v_a_1013_, 0);
lean_dec(v_unused_1055_);
v___x_1022_ = v_a_1013_;
v_isShared_1023_ = v_isSharedCheck_1054_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v_a_1013_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1054_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
uint8_t v_semiring_1024_; 
v_semiring_1024_ = lean_ctor_get_uint8(v_a_1004_, sizeof(void*)*3);
if (v_semiring_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1043_; 
lean_del_object(v___x_1022_);
lean_del_object(v___x_1015_);
v___x_1025_ = l_Int_pow(v_n_1003_, v_k_1002_);
lean_dec(v_k_1002_);
v___x_1026_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1025_, v_a_1004_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1043_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1043_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_val_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1042_; 
v_val_1031_ = lean_ctor_get(v_a_1027_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_a_1027_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1033_ = v_a_1027_;
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_val_1031_);
lean_dec(v_a_1027_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_val_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1037_);
v___x_1039_ = v___x_1029_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
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
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1044_ = lean_nat_abs(v_n_1003_);
v___x_1045_ = lean_nat_to_int(v___x_1044_);
v___x_1046_ = l_Int_pow(v___x_1045_, v_k_1002_);
lean_dec(v_k_1002_);
lean_dec(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1047_);
v___x_1049_ = v___x_1022_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1049_);
v___x_1051_ = v___x_1015_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_k_1002_);
v_a_1057_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1012_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1012_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow___boxed(lean_object* v_k_1065_, lean_object* v_n_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(v_k_1065_, v_n_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_n_1066_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_powNode(lean_object* v_a_1076_, lean_object* v_pa_1077_, lean_object* v_k_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_nat_dec_eq(v_k_1078_, v___x_1087_);
if (v___x_1088_ == 0)
{
switch(lean_obj_tag(v_a_1076_))
{
case 0:
{
lean_object* v_k_1089_; lean_object* v___x_1090_; 
lean_dec_ref(v_pa_1077_);
v_k_1089_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_k_1089_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1090_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(v_k_1078_, v_k_1089_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_k_1089_);
return v___x_1090_;
}
case 2:
{
lean_object* v_k_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v_pa_1077_);
v_k_1091_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_k_1091_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1092_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(v_k_1078_, v_k_1091_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_k_1091_);
return v___x_1092_;
}
case 1:
{
lean_object* v_k_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec_ref(v_pa_1077_);
v_k_1093_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_k_1093_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1094_ = lean_nat_to_int(v_k_1093_);
v___x_1095_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(v_k_1078_, v___x_1094_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v___x_1094_);
return v___x_1095_;
}
case 3:
{
lean_object* v_i_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v_pa_1077_);
v_i_1096_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_i_1096_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1097_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1096_, v_k_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
return v___x_1097_;
}
default: 
{
lean_object* v___x_1098_; 
lean_dec_ref(v_a_1076_);
v___x_1098_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_pa_1077_, v_k_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_k_1078_);
return v___x_1098_;
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec(v_k_1078_);
lean_dec_ref(v_pa_1077_);
lean_dec_ref(v_a_1076_);
v___x_1099_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_powNode___boxed(lean_object* v_a_1101_, lean_object* v_pa_1102_, lean_object* v_k_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Meta_Sym_Arith_SafePoly_powNode(v_a_1101_, v_pa_1102_, v_k_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec_ref(v_a_1104_);
return v_res_1112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0);
v___x_1114_ = lean_int_neg(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(lean_object* v_e_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_n_1125_; lean_object* v___y_1126_; 
switch(lean_obj_tag(v_e_1115_))
{
case 1:
{
lean_object* v_k_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1194_; 
v_k_1157_ = lean_ctor_get(v_e_1115_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_e_1115_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1159_ = v_e_1115_;
v_isShared_1160_ = v_isSharedCheck_1194_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_k_1157_);
lean_dec(v_e_1115_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1194_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_nat_to_int(v_k_1157_);
v___x_1162_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1161_, v_a_1116_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1185_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1185_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1185_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
if (lean_obj_tag(v_a_1163_) == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_del_object(v___x_1159_);
v___x_1167_ = lean_box(0);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v_val_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1184_; 
v_val_1171_ = lean_ctor_get(v_a_1163_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_a_1163_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1173_ = v_a_1163_;
v_isShared_1174_ = v_isSharedCheck_1184_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_val_1171_);
lean_dec(v_a_1163_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1184_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 0);
lean_ctor_set(v___x_1159_, 0, v_val_1171_);
v___x_1176_ = v___x_1159_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_val_1171_);
v___x_1176_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1178_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1176_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1178_);
v___x_1180_ = v___x_1165_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_del_object(v___x_1159_);
v_a_1186_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1162_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1162_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1204_; 
v_i_1195_ = lean_ctor_get(v_e_1115_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_e_1115_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1197_ = v_e_1115_;
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_i_1195_);
lean_dec(v_e_1115_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set_tag(v___x_1197_, 1);
lean_ctor_set(v___x_1197_, 0, v___x_1199_);
v___x_1201_ = v___x_1197_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
}
case 4:
{
lean_object* v_a_1205_; lean_object* v___x_1206_; 
v_a_1205_ = lean_ctor_get(v_e_1115_, 0);
lean_inc_ref(v_a_1205_);
lean_dec_ref_known(v_e_1115_, 1);
v___x_1206_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1205_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
if (lean_obj_tag(v_a_1207_) == 0)
{
return v___x_1206_;
}
else
{
lean_object* v_val_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_inc_ref(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v_val_1208_ = lean_ctor_get(v_a_1207_, 0);
lean_inc(v_val_1208_);
lean_dec_ref_known(v_a_1207_, 1);
v___x_1209_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0);
v___x_1210_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v___x_1209_, v_val_1208_, v_a_1116_);
return v___x_1210_;
}
}
else
{
return v___x_1206_;
}
}
case 5:
{
lean_object* v_a_1211_; lean_object* v_b_1212_; lean_object* v___x_1213_; 
v_a_1211_ = lean_ctor_get(v_e_1115_, 0);
lean_inc_ref(v_a_1211_);
v_b_1212_ = lean_ctor_get(v_e_1115_, 1);
lean_inc_ref(v_b_1212_);
lean_dec_ref_known(v_e_1115_, 2);
v___x_1213_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1211_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
if (lean_obj_tag(v_a_1214_) == 0)
{
lean_dec_ref(v_b_1212_);
return v___x_1213_;
}
else
{
lean_object* v_val_1215_; lean_object* v___x_1216_; 
lean_inc_ref(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v_val_1215_ = lean_ctor_get(v_a_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v_a_1214_, 1);
v___x_1216_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1212_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
if (lean_obj_tag(v_a_1217_) == 0)
{
lean_dec(v_val_1215_);
return v___x_1216_;
}
else
{
lean_object* v_val_1218_; lean_object* v___x_1219_; 
lean_inc_ref(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v_val_1218_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_val_1218_);
lean_dec_ref_known(v_a_1217_, 1);
v___x_1219_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1215_, v_val_1218_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1219_;
}
}
else
{
lean_dec(v_val_1215_);
return v___x_1216_;
}
}
}
else
{
lean_dec_ref(v_b_1212_);
return v___x_1213_;
}
}
case 6:
{
lean_object* v_a_1220_; lean_object* v_b_1221_; lean_object* v___x_1222_; 
v_a_1220_ = lean_ctor_get(v_e_1115_, 0);
lean_inc_ref(v_a_1220_);
v_b_1221_ = lean_ctor_get(v_e_1115_, 1);
lean_inc_ref(v_b_1221_);
lean_dec_ref_known(v_e_1115_, 2);
v___x_1222_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1220_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
if (lean_obj_tag(v_a_1223_) == 0)
{
lean_dec_ref(v_b_1221_);
return v___x_1222_;
}
else
{
lean_object* v_val_1224_; lean_object* v___x_1225_; 
lean_inc_ref(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_val_1224_ = lean_ctor_get(v_a_1223_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v_a_1223_, 1);
v___x_1225_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1221_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
if (lean_obj_tag(v_a_1226_) == 0)
{
lean_dec(v_val_1224_);
return v___x_1225_;
}
else
{
lean_object* v_val_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_inc_ref(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_val_1227_ = lean_ctor_get(v_a_1226_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_a_1226_, 1);
v___x_1228_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0);
v___x_1229_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v___x_1228_, v_val_1227_, v_a_1116_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
if (lean_obj_tag(v_a_1230_) == 0)
{
lean_dec(v_val_1224_);
return v___x_1229_;
}
else
{
lean_object* v_val_1231_; lean_object* v___x_1232_; 
lean_inc_ref(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v_val_1231_ = lean_ctor_get(v_a_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v_a_1230_, 1);
v___x_1232_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1224_, v_val_1231_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1232_;
}
}
else
{
lean_dec(v_val_1224_);
return v___x_1229_;
}
}
}
else
{
lean_dec(v_val_1224_);
return v___x_1225_;
}
}
}
else
{
lean_dec_ref(v_b_1221_);
return v___x_1222_;
}
}
case 7:
{
lean_object* v_a_1233_; lean_object* v_b_1234_; lean_object* v___x_1235_; 
v_a_1233_ = lean_ctor_get(v_e_1115_, 0);
lean_inc_ref(v_a_1233_);
v_b_1234_ = lean_ctor_get(v_e_1115_, 1);
lean_inc_ref(v_b_1234_);
lean_dec_ref_known(v_e_1115_, 2);
v___x_1235_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1233_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
if (lean_obj_tag(v_a_1236_) == 0)
{
lean_dec_ref(v_b_1234_);
return v___x_1235_;
}
else
{
lean_object* v_val_1237_; lean_object* v___x_1238_; 
lean_inc_ref(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v_val_1237_ = lean_ctor_get(v_a_1236_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v_a_1236_, 1);
v___x_1238_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1234_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
if (lean_obj_tag(v_a_1239_) == 0)
{
lean_dec(v_val_1237_);
return v___x_1238_;
}
else
{
lean_object* v_val_1240_; lean_object* v___x_1241_; 
lean_inc_ref(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v_val_1240_ = lean_ctor_get(v_a_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v_a_1239_, 1);
v___x_1241_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_1237_, v_val_1240_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1241_;
}
}
else
{
lean_dec(v_val_1237_);
return v___x_1238_;
}
}
}
else
{
lean_dec_ref(v_b_1234_);
return v___x_1235_;
}
}
case 8:
{
lean_object* v_a_1242_; lean_object* v_k_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_a_1242_ = lean_ctor_get(v_e_1115_, 0);
lean_inc_ref(v_a_1242_);
v_k_1243_ = lean_ctor_get(v_e_1115_, 1);
lean_inc(v_k_1243_);
lean_dec_ref_known(v_e_1115_, 2);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_nat_dec_eq(v_k_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
switch(lean_obj_tag(v_a_1242_))
{
case 0:
{
lean_object* v_k_1246_; lean_object* v___x_1247_; 
v_k_1246_ = lean_ctor_get(v_a_1242_, 0);
lean_inc(v_k_1246_);
lean_dec_ref_known(v_a_1242_, 1);
lean_inc(v_k_1243_);
v___x_1247_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1243_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1294_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1294_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1294_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
if (lean_obj_tag(v_a_1248_) == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec(v_k_1246_);
lean_dec(v_k_1243_);
v___x_1252_ = lean_box(0);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
else
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1250_);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_a_1248_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v_a_1248_, 0);
lean_dec(v_unused_1293_);
v___x_1257_ = v_a_1248_;
v_isShared_1258_ = v_isSharedCheck_1292_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v_a_1248_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1292_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = l_Int_pow(v_k_1246_, v_k_1243_);
lean_dec(v_k_1243_);
lean_dec(v_k_1246_);
v___x_1260_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1259_, v_a_1116_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1283_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1283_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1283_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
if (lean_obj_tag(v_a_1261_) == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_del_object(v___x_1257_);
v___x_1265_ = lean_box(0);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
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
lean_object* v_val_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1282_; 
v_val_1269_ = lean_ctor_get(v_a_1261_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_a_1261_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1271_ = v_a_1261_;
v_isShared_1272_ = v_isSharedCheck_1282_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_val_1269_);
lean_dec(v_a_1261_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1282_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 0);
lean_ctor_set(v___x_1257_, 0, v_val_1269_);
v___x_1274_ = v___x_1257_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_val_1269_);
v___x_1274_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1274_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1276_);
v___x_1278_ = v___x_1263_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_del_object(v___x_1257_);
v_a_1284_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1260_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1260_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_k_1246_);
lean_dec(v_k_1243_);
v_a_1295_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1247_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1247_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
case 3:
{
lean_object* v_i_1303_; lean_object* v___x_1304_; 
v_i_1303_ = lean_ctor_get(v_a_1242_, 0);
lean_inc(v_i_1303_);
lean_dec_ref_known(v_a_1242_, 1);
v___x_1304_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1303_, v_k_1243_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1304_;
}
default: 
{
lean_object* v___x_1305_; 
v___x_1305_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1242_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
if (lean_obj_tag(v_a_1306_) == 0)
{
lean_dec(v_k_1243_);
return v___x_1305_;
}
else
{
lean_object* v_val_1307_; lean_object* v___x_1308_; 
lean_inc_ref(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v_val_1307_ = lean_ctor_get(v_a_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v_a_1306_, 1);
v___x_1308_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_val_1307_, v_k_1243_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_k_1243_);
return v___x_1308_;
}
}
else
{
lean_dec(v_k_1243_);
return v___x_1305_;
}
}
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v_k_1243_);
lean_dec_ref(v_a_1242_);
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
default: 
{
lean_object* v_k_1311_; 
v_k_1311_ = lean_ctor_get(v_e_1115_, 0);
lean_inc(v_k_1311_);
lean_dec_ref(v_e_1115_);
v_n_1125_ = v_k_1311_;
v___y_1126_ = v_a_1116_;
goto v___jp_1124_;
}
}
v___jp_1124_:
{
lean_object* v___x_1127_; 
v___x_1127_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_n_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1148_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1148_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1148_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
if (lean_obj_tag(v_a_1128_) == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_box(0);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_object* v_val_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1147_; 
v_val_1136_ = lean_ctor_get(v_a_1128_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_a_1128_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1138_ = v_a_1128_;
v_isShared_1139_ = v_isSharedCheck_1147_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_val_1136_);
lean_dec(v_a_1128_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1147_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_val_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1142_);
v___x_1144_ = v___x_1130_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
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
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1127_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1127_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___boxed(lean_object* v_e_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1321_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0, &l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(lean_object* v_e_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
switch(lean_obj_tag(v_e_1324_))
{
case 0:
{
lean_object* v_k_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1344_; 
v_k_1333_ = lean_ctor_get(v_e_1324_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_e_1324_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1335_ = v_e_1324_;
v_isShared_1336_ = v_isSharedCheck_1344_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_k_1333_);
lean_dec(v_e_1324_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1344_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = lean_nat_abs(v_k_1333_);
lean_dec(v_k_1333_);
v___x_1338_ = lean_nat_to_int(v___x_1337_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1338_);
v___x_1340_ = v___x_1335_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
}
}
case 1:
{
lean_object* v_k_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1355_; 
v_k_1345_ = lean_ctor_get(v_e_1324_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_e_1324_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1347_ = v_e_1324_;
v_isShared_1348_ = v_isSharedCheck_1355_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_k_1345_);
lean_dec(v_e_1324_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1355_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_nat_to_int(v_k_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
}
case 3:
{
lean_object* v_i_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1365_; 
v_i_1356_ = lean_ctor_get(v_e_1324_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_e_1324_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1358_ = v_e_1324_;
v_isShared_1359_ = v_isSharedCheck_1365_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_i_1356_);
lean_dec(v_e_1324_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1365_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_1356_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set_tag(v___x_1358_, 1);
lean_ctor_set(v___x_1358_, 0, v___x_1360_);
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
}
case 5:
{
lean_object* v_a_1366_; lean_object* v_b_1367_; lean_object* v___x_1368_; 
v_a_1366_ = lean_ctor_get(v_e_1324_, 0);
lean_inc_ref(v_a_1366_);
v_b_1367_ = lean_ctor_get(v_e_1324_, 1);
lean_inc_ref(v_b_1367_);
lean_dec_ref_known(v_e_1324_, 2);
v___x_1368_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1366_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
if (lean_obj_tag(v_a_1369_) == 0)
{
lean_dec_ref(v_b_1367_);
return v___x_1368_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1371_; 
lean_inc_ref(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v_val_1370_ = lean_ctor_get(v_a_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v_a_1369_, 1);
v___x_1371_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_b_1367_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
if (lean_obj_tag(v_a_1372_) == 0)
{
lean_dec(v_val_1370_);
return v___x_1371_;
}
else
{
lean_object* v_val_1373_; lean_object* v___x_1374_; 
lean_inc_ref(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v_val_1373_ = lean_ctor_get(v_a_1372_, 0);
lean_inc(v_val_1373_);
lean_dec_ref_known(v_a_1372_, 1);
v___x_1374_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1370_, v_val_1373_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
return v___x_1374_;
}
}
else
{
lean_dec(v_val_1370_);
return v___x_1371_;
}
}
}
else
{
lean_dec_ref(v_b_1367_);
return v___x_1368_;
}
}
case 7:
{
lean_object* v_a_1375_; lean_object* v_b_1376_; lean_object* v___x_1377_; 
v_a_1375_ = lean_ctor_get(v_e_1324_, 0);
lean_inc_ref(v_a_1375_);
v_b_1376_ = lean_ctor_get(v_e_1324_, 1);
lean_inc_ref(v_b_1376_);
lean_dec_ref_known(v_e_1324_, 2);
v___x_1377_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1375_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
if (lean_obj_tag(v_a_1378_) == 0)
{
lean_dec_ref(v_b_1376_);
return v___x_1377_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1380_; 
lean_inc_ref(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v_val_1379_ = lean_ctor_get(v_a_1378_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v_a_1378_, 1);
v___x_1380_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_b_1376_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
if (lean_obj_tag(v_a_1381_) == 0)
{
lean_dec(v_val_1379_);
return v___x_1380_;
}
else
{
lean_object* v_val_1382_; lean_object* v___x_1383_; 
lean_inc_ref(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_val_1382_ = lean_ctor_get(v_a_1381_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v_a_1381_, 1);
v___x_1383_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_1379_, v_val_1382_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
return v___x_1383_;
}
}
else
{
lean_dec(v_val_1379_);
return v___x_1380_;
}
}
}
else
{
lean_dec_ref(v_b_1376_);
return v___x_1377_;
}
}
case 8:
{
lean_object* v_a_1384_; lean_object* v_k_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_a_1384_ = lean_ctor_get(v_e_1324_, 0);
lean_inc_ref(v_a_1384_);
v_k_1385_ = lean_ctor_get(v_e_1324_, 1);
lean_inc(v_k_1385_);
lean_dec_ref_known(v_e_1324_, 2);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_nat_dec_eq(v_k_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
switch(lean_obj_tag(v_a_1384_))
{
case 0:
{
lean_object* v_k_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1427_; 
v_k_1388_ = lean_ctor_get(v_a_1384_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_a_1384_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1390_ = v_a_1384_;
v_isShared_1391_ = v_isSharedCheck_1427_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_k_1388_);
lean_dec(v_a_1384_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1427_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; 
lean_inc(v_k_1385_);
v___x_1392_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1385_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1418_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1418_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1418_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
if (lean_obj_tag(v_a_1393_) == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_del_object(v___x_1390_);
lean_dec(v_k_1388_);
lean_dec(v_k_1385_);
v___x_1397_ = lean_box(0);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1416_; 
v_isSharedCheck_1416_ = !lean_is_exclusive(v_a_1393_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v_a_1393_, 0);
lean_dec(v_unused_1417_);
v___x_1402_ = v_a_1393_;
v_isShared_1403_ = v_isSharedCheck_1416_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v_a_1393_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1416_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1404_ = lean_nat_abs(v_k_1388_);
lean_dec(v_k_1388_);
v___x_1405_ = lean_nat_to_int(v___x_1404_);
v___x_1406_ = l_Int_pow(v___x_1405_, v_k_1385_);
lean_dec(v_k_1385_);
lean_dec(v___x_1405_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1406_);
v___x_1408_ = v___x_1390_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1408_);
v___x_1410_ = v___x_1402_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1410_);
v___x_1412_ = v___x_1395_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1390_);
lean_dec(v_k_1388_);
lean_dec(v_k_1385_);
v_a_1419_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1392_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1392_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1428_; lean_object* v___x_1429_; 
v_i_1428_ = lean_ctor_get(v_a_1384_, 0);
lean_inc(v_i_1428_);
lean_dec_ref_known(v_a_1384_, 1);
v___x_1429_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1428_, v_k_1385_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
return v___x_1429_;
}
default: 
{
lean_object* v___x_1430_; 
v___x_1430_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1384_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
if (lean_obj_tag(v_a_1431_) == 0)
{
lean_dec(v_k_1385_);
return v___x_1430_;
}
else
{
lean_object* v_val_1432_; lean_object* v___x_1433_; 
lean_inc_ref(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v_val_1432_ = lean_ctor_get(v_a_1431_, 0);
lean_inc(v_val_1432_);
lean_dec_ref_known(v_a_1431_, 1);
v___x_1433_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_val_1432_, v_k_1385_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_k_1385_);
return v___x_1433_;
}
}
else
{
lean_dec(v_k_1385_);
return v___x_1430_;
}
}
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec(v_k_1385_);
lean_dec_ref(v_a_1384_);
v___x_1434_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
default: 
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_e_1324_);
v___x_1436_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___boxed(lean_object* v_e_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec_ref(v_a_1439_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f(lean_object* v_e_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
uint8_t v_semiring_1457_; 
v_semiring_1457_ = lean_ctor_get_uint8(v_a_1449_, sizeof(void*)*3);
if (v_semiring_1457_ == 0)
{
lean_object* v___x_1458_; 
v___x_1458_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
return v___x_1458_;
}
else
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f___boxed(lean_object* v_e_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Meta_Sym_Arith_toPoly_x3f(v_e_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1469_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_SafePoly(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_SafePoly(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_SafePoly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_SafePoly(builtin);
}
#ifdef __cplusplus
}
#endif
