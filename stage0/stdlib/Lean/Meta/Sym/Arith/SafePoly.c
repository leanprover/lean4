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
lean_object* v_toCold_391_; lean_object* v_currRecDepth_392_; lean_object* v_ref_393_; uint16_t v_optionFlags_394_; uint8_t v_suppressElabErrors_395_; uint8_t v_isRecordingDeps_396_; lean_object* v_maxRecDepth_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_toCold_391_ = lean_ctor_get(v_a_388_, 0);
lean_inc_ref(v_toCold_391_);
v_currRecDepth_392_ = lean_ctor_get(v_a_388_, 1);
lean_inc(v_currRecDepth_392_);
v_ref_393_ = lean_ctor_get(v_a_388_, 2);
lean_inc(v_ref_393_);
v_optionFlags_394_ = lean_ctor_get_uint16(v_a_388_, sizeof(void*)*3);
v_suppressElabErrors_395_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*3 + 2);
v_isRecordingDeps_396_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_388_);
v_maxRecDepth_558_ = lean_ctor_get(v_toCold_391_, 3);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_nat_dec_eq(v_maxRecDepth_558_, v___x_559_);
if (v___x_560_ == 0)
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_eq(v_currRecDepth_392_, v_maxRecDepth_558_);
if (v___x_561_ == 0)
{
goto v___jp_397_;
}
else
{
lean_object* v___x_562_; 
lean_dec(v_currRecDepth_392_);
lean_dec_ref(v_toCold_391_);
lean_dec_ref(v_p_u2082_382_);
lean_dec_ref(v_p_u2081_381_);
v___x_562_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_393_);
return v___x_562_;
}
}
else
{
goto v___jp_397_;
}
v___jp_397_:
{
if (lean_obj_tag(v_p_u2081_381_) == 0)
{
lean_dec(v_ref_393_);
lean_dec(v_currRecDepth_392_);
lean_dec_ref(v_toCold_391_);
if (lean_obj_tag(v_p_u2082_382_) == 0)
{
lean_object* v_k_398_; lean_object* v_k_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_436_; 
v_k_398_ = lean_ctor_get(v_p_u2081_381_, 0);
lean_inc(v_k_398_);
lean_dec_ref_known(v_p_u2081_381_, 1);
v_k_399_ = lean_ctor_get(v_p_u2082_382_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_p_u2082_382_);
if (v_isSharedCheck_436_ == 0)
{
v___x_401_ = v_p_u2082_382_;
v_isShared_402_ = v_isSharedCheck_436_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_k_399_);
lean_dec(v_p_u2082_382_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_436_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_int_add(v_k_398_, v_k_399_);
lean_dec(v_k_399_);
lean_dec(v_k_398_);
v___x_404_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_403_, v_a_383_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_427_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_427_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_427_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_427_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
if (lean_obj_tag(v_a_405_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_411_; 
lean_del_object(v___x_401_);
v___x_409_ = lean_box(0);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
else
{
lean_object* v_val_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_426_; 
v_val_413_ = lean_ctor_get(v_a_405_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_a_405_);
if (v_isSharedCheck_426_ == 0)
{
v___x_415_ = v_a_405_;
v_isShared_416_ = v_isSharedCheck_426_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_val_413_);
lean_dec(v_a_405_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_426_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_val_413_);
v___x_418_ = v___x_401_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_val_413_);
v___x_418_ = v_reuseFailAlloc_425_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_418_);
v___x_420_ = v___x_415_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_422_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_420_);
v___x_422_ = v___x_407_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_del_object(v___x_401_);
v_a_428_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_404_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_404_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v_k_437_; lean_object* v___x_438_; 
v_k_437_ = lean_ctor_get(v_p_u2081_381_, 0);
lean_inc(v_k_437_);
lean_dec_ref_known(v_p_u2081_381_, 1);
v___x_438_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_u2082_382_, v_k_437_, v_a_383_);
lean_dec(v_k_437_);
return v___x_438_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_382_) == 0)
{
lean_object* v_k_439_; lean_object* v___x_440_; 
lean_dec(v_ref_393_);
lean_dec(v_currRecDepth_392_);
lean_dec_ref(v_toCold_391_);
v_k_439_ = lean_ctor_get(v_p_u2082_382_, 0);
lean_inc(v_k_439_);
lean_dec_ref_known(v_p_u2082_382_, 1);
v___x_440_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_u2081_381_, v_k_439_, v_a_383_);
lean_dec(v_k_439_);
return v___x_440_;
}
else
{
lean_object* v_k_441_; lean_object* v_v_442_; lean_object* v_p_443_; lean_object* v_k_444_; lean_object* v_v_445_; lean_object* v_p_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_k_441_ = lean_ctor_get(v_p_u2081_381_, 0);
v_v_442_ = lean_ctor_get(v_p_u2081_381_, 1);
v_p_443_ = lean_ctor_get(v_p_u2081_381_, 2);
v_k_444_ = lean_ctor_get(v_p_u2082_382_, 0);
v_v_445_ = lean_ctor_get(v_p_u2082_382_, 1);
v_p_446_ = lean_ctor_get(v_p_u2082_382_, 2);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_currRecDepth_392_, v___x_447_);
lean_dec(v_currRecDepth_392_);
v___x_449_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_449_, 0, v_toCold_391_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
lean_ctor_set(v___x_449_, 2, v_ref_393_);
lean_ctor_set_uint16(v___x_449_, sizeof(void*)*3, v_optionFlags_394_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*3 + 2, v_suppressElabErrors_395_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*3 + 3, v_isRecordingDeps_396_);
v___x_450_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_442_, v_v_445_);
switch(v___x_450_)
{
case 0:
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_475_; 
lean_inc_ref(v_p_446_);
lean_inc(v_v_445_);
lean_inc(v_k_444_);
v_isSharedCheck_475_ = !lean_is_exclusive(v_p_u2082_382_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_476_ = lean_ctor_get(v_p_u2082_382_, 2);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_p_u2082_382_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_p_u2082_382_, 0);
lean_dec(v_unused_478_);
v___x_452_ = v_p_u2082_382_;
v_isShared_453_ = v_isSharedCheck_475_;
goto v_resetjp_451_;
}
else
{
lean_dec(v_p_u2082_382_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_475_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_381_, v_p_446_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v___x_449_, v_a_389_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
if (lean_obj_tag(v_a_455_) == 0)
{
lean_del_object(v___x_452_);
lean_dec(v_v_445_);
lean_dec(v_k_444_);
return v___x_454_;
}
else
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_473_; 
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_474_);
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_473_;
goto v_resetjp_456_;
}
else
{
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_473_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_val_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_472_; 
v_val_459_ = lean_ctor_get(v_a_455_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_a_455_);
if (v_isSharedCheck_472_ == 0)
{
v___x_461_ = v_a_455_;
v_isShared_462_ = v_isSharedCheck_472_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_val_459_);
lean_dec(v_a_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_472_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 2, v_val_459_);
v___x_464_ = v___x_452_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_k_444_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_v_445_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_val_459_);
v___x_464_ = v_reuseFailAlloc_471_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_466_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_466_);
v___x_468_ = v___x_457_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_452_);
lean_dec(v_v_445_);
lean_dec(v_k_444_);
return v___x_454_;
}
}
}
case 1:
{
lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_526_; 
lean_inc_ref(v_p_446_);
lean_inc(v_k_444_);
lean_inc_ref(v_p_443_);
lean_inc(v_v_442_);
lean_inc(v_k_441_);
lean_dec_ref_known(v_p_u2081_381_, 3);
v_isSharedCheck_526_ = !lean_is_exclusive(v_p_u2082_382_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; lean_object* v_unused_528_; lean_object* v_unused_529_; 
v_unused_527_ = lean_ctor_get(v_p_u2082_382_, 2);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_p_u2082_382_, 1);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_p_u2082_382_, 0);
lean_dec(v_unused_529_);
v___x_480_ = v_p_u2082_382_;
v_isShared_481_ = v_isSharedCheck_526_;
goto v_resetjp_479_;
}
else
{
lean_dec(v_p_u2082_382_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_526_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_int_add(v_k_441_, v_k_444_);
lean_dec(v_k_444_);
lean_dec(v_k_441_);
v___x_483_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_482_, v_a_383_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_517_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_517_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_517_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_517_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
if (lean_obj_tag(v_a_484_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_490_; 
lean_del_object(v___x_480_);
lean_dec_ref_known(v___x_449_, 3);
lean_dec_ref(v_p_446_);
lean_dec_ref(v_p_443_);
lean_dec(v_v_442_);
v___x_488_ = lean_box(0);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
else
{
lean_object* v_val_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
lean_del_object(v___x_486_);
v_val_492_ = lean_ctor_get(v_a_484_, 0);
lean_inc(v_val_492_);
lean_dec_ref_known(v_a_484_, 1);
v___x_493_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0);
v___x_494_ = lean_int_dec_eq(v_val_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_443_, v_p_446_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v___x_449_, v_a_389_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
if (lean_obj_tag(v_a_496_) == 0)
{
lean_dec(v_val_492_);
lean_del_object(v___x_480_);
lean_dec(v_v_442_);
return v___x_495_;
}
else
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_514_; 
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v___x_495_, 0);
lean_dec(v_unused_515_);
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_514_;
goto v_resetjp_497_;
}
else
{
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_514_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_513_; 
v_val_500_ = lean_ctor_get(v_a_496_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_a_496_);
if (v_isSharedCheck_513_ == 0)
{
v___x_502_ = v_a_496_;
v_isShared_503_ = v_isSharedCheck_513_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v_a_496_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_513_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 2, v_val_500_);
lean_ctor_set(v___x_480_, 1, v_v_442_);
lean_ctor_set(v___x_480_, 0, v_val_492_);
v___x_505_ = v___x_480_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_val_492_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_v_442_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_val_500_);
v___x_505_ = v_reuseFailAlloc_512_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_507_);
v___x_509_ = v___x_498_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
}
else
{
lean_dec(v_val_492_);
lean_del_object(v___x_480_);
lean_dec(v_v_442_);
return v___x_495_;
}
}
else
{
lean_dec(v_val_492_);
lean_del_object(v___x_480_);
lean_dec(v_v_442_);
v_p_u2081_381_ = v_p_443_;
v_p_u2082_382_ = v_p_446_;
v_a_388_ = v___x_449_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_del_object(v___x_480_);
lean_dec_ref_known(v___x_449_, 3);
lean_dec_ref(v_p_446_);
lean_dec_ref(v_p_443_);
lean_dec(v_v_442_);
v_a_518_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_483_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_483_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
default: 
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_554_; 
lean_inc_ref(v_p_443_);
lean_inc(v_v_442_);
lean_inc(v_k_441_);
v_isSharedCheck_554_ = !lean_is_exclusive(v_p_u2081_381_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; 
v_unused_555_ = lean_ctor_get(v_p_u2081_381_, 2);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_p_u2081_381_, 1);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_p_u2081_381_, 0);
lean_dec(v_unused_557_);
v___x_531_ = v_p_u2081_381_;
v_isShared_532_ = v_isSharedCheck_554_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_p_u2081_381_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_554_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; 
v___x_533_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_443_, v_p_u2082_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v___x_449_, v_a_389_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
if (lean_obj_tag(v_a_534_) == 0)
{
lean_del_object(v___x_531_);
lean_dec(v_v_442_);
lean_dec(v_k_441_);
return v___x_533_;
}
else
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_552_; 
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v___x_533_, 0);
lean_dec(v_unused_553_);
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_552_;
goto v_resetjp_535_;
}
else
{
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_552_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_val_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_551_; 
v_val_538_ = lean_ctor_get(v_a_534_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_534_);
if (v_isSharedCheck_551_ == 0)
{
v___x_540_ = v_a_534_;
v_isShared_541_ = v_isSharedCheck_551_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_val_538_);
lean_dec(v_a_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_551_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 2, v_val_538_);
v___x_543_ = v___x_531_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_k_441_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_v_442_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_val_538_);
v___x_543_ = v_reuseFailAlloc_550_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_543_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_549_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_545_);
v___x_547_ = v___x_536_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_531_);
lean_dec(v_v_442_);
lean_dec(v_k_441_);
return v___x_533_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___boxed(lean_object* v_p_u2081_563_, lean_object* v_p_u2082_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_563_, v_p_u2082_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
lean_dec(v_a_571_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine(lean_object* v_p_u2081_574_, lean_object* v_p_u2082_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; 
lean_inc_ref(v_a_581_);
v___x_584_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_574_, v_p_u2082_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
if (lean_obj_tag(v_a_585_) == 0)
{
return v___x_584_;
}
else
{
lean_object* v_val_586_; lean_object* v___x_587_; 
lean_inc_ref(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v_val_586_ = lean_ctor_get(v_a_585_, 0);
v___x_587_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(v_val_586_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_599_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_599_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_599_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_599_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
if (lean_obj_tag(v_a_588_) == 0)
{
lean_object* v___x_592_; lean_object* v___x_594_; 
lean_dec_ref_known(v_a_585_, 1);
v___x_592_ = lean_box(0);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
lean_object* v___x_597_; 
lean_dec_ref_known(v_a_588_, 1);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_a_585_);
v___x_597_ = v___x_590_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_585_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref_known(v_a_585_, 1);
v_a_600_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_587_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_587_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
else
{
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine___boxed(lean_object* v_p_u2081_608_, lean_object* v_p_u2082_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_p_u2081_608_, v_p_u2082_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec_ref(v_a_610_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(lean_object* v_p_u2082_620_, lean_object* v_p_u2081_621_, lean_object* v_acc_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_toCold_631_; lean_object* v_currRecDepth_632_; lean_object* v_ref_633_; uint16_t v_optionFlags_634_; uint8_t v_suppressElabErrors_635_; uint8_t v_isRecordingDeps_636_; lean_object* v_maxRecDepth_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_toCold_631_ = lean_ctor_get(v_a_628_, 0);
lean_inc_ref(v_toCold_631_);
v_currRecDepth_632_ = lean_ctor_get(v_a_628_, 1);
lean_inc(v_currRecDepth_632_);
v_ref_633_ = lean_ctor_get(v_a_628_, 2);
lean_inc(v_ref_633_);
v_optionFlags_634_ = lean_ctor_get_uint16(v_a_628_, sizeof(void*)*3);
v_suppressElabErrors_635_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*3 + 2);
v_isRecordingDeps_636_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_628_);
v_maxRecDepth_666_ = lean_ctor_get(v_toCold_631_, 3);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_nat_dec_eq(v_maxRecDepth_666_, v___x_667_);
if (v___x_668_ == 0)
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_eq(v_currRecDepth_632_, v_maxRecDepth_666_);
if (v___x_669_ == 0)
{
goto v___jp_637_;
}
else
{
lean_object* v___x_670_; 
lean_dec(v_currRecDepth_632_);
lean_dec_ref(v_toCold_631_);
lean_dec_ref(v_acc_622_);
lean_dec_ref(v_p_u2081_621_);
lean_dec_ref(v_p_u2082_620_);
v___x_670_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_633_);
return v___x_670_;
}
}
else
{
goto v___jp_637_;
}
v___jp_637_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_currRecDepth_632_, v___x_638_);
lean_dec(v_currRecDepth_632_);
v___x_640_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_640_, 0, v_toCold_631_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_ctor_set(v___x_640_, 2, v_ref_633_);
lean_ctor_set_uint16(v___x_640_, sizeof(void*)*3, v_optionFlags_634_);
lean_ctor_set_uint8(v___x_640_, sizeof(void*)*3 + 2, v_suppressElabErrors_635_);
lean_ctor_set_uint8(v___x_640_, sizeof(void*)*3 + 3, v_isRecordingDeps_636_);
if (lean_obj_tag(v_p_u2081_621_) == 0)
{
lean_object* v_k_641_; lean_object* v___x_642_; lean_object* v_a_643_; lean_object* v_val_644_; lean_object* v___x_645_; 
v_k_641_ = lean_ctor_get(v_p_u2081_621_, 0);
lean_inc(v_k_641_);
lean_dec_ref_known(v_p_u2081_621_, 1);
v___x_642_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_641_, v_p_u2082_620_, v_a_623_);
lean_dec(v_k_641_);
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v___x_642_);
v_val_644_ = lean_ctor_get(v_a_643_, 0);
lean_inc(v_val_644_);
lean_dec(v_a_643_);
v___x_645_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_acc_622_, v_val_644_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v___x_640_, v_a_629_);
lean_dec_ref_known(v___x_640_, 3);
return v___x_645_;
}
else
{
lean_object* v_k_646_; lean_object* v_v_647_; lean_object* v_p_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_k_646_ = lean_ctor_get(v_p_u2081_621_, 0);
lean_inc(v_k_646_);
v_v_647_ = lean_ctor_get(v_p_u2081_621_, 1);
lean_inc(v_v_647_);
v_p_648_ = lean_ctor_get(v_p_u2081_621_, 2);
lean_inc_ref(v_p_648_);
lean_dec_ref_known(v_p_u2081_621_, 3);
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___closed__0));
v___x_650_ = l_Lean_Core_checkSystem(v___x_649_, v___x_640_, v_a_629_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v_a_652_; lean_object* v_val_653_; lean_object* v___x_654_; 
lean_dec_ref_known(v___x_650_, 1);
lean_inc_ref(v_p_u2082_620_);
v___x_651_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_646_, v_v_647_, v_p_u2082_620_, v_a_623_);
lean_dec(v_k_646_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
v_val_653_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_val_653_);
lean_dec(v_a_652_);
v___x_654_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_acc_622_, v_val_653_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v___x_640_, v_a_629_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
if (lean_obj_tag(v_a_655_) == 0)
{
lean_dec_ref(v_p_648_);
lean_dec_ref_known(v___x_640_, 3);
lean_dec_ref(v_p_u2082_620_);
return v___x_654_;
}
else
{
lean_object* v_val_656_; 
lean_inc_ref(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v_val_656_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v_a_655_, 1);
v_p_u2081_621_ = v_p_648_;
v_acc_622_ = v_val_656_;
v_a_628_ = v___x_640_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_648_);
lean_dec_ref_known(v___x_640_, 3);
lean_dec_ref(v_p_u2082_620_);
return v___x_654_;
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_p_648_);
lean_dec(v_v_647_);
lean_dec(v_k_646_);
lean_dec_ref_known(v___x_640_, 3);
lean_dec_ref(v_acc_622_);
lean_dec_ref(v_p_u2082_620_);
v_a_658_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_650_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_650_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___boxed(lean_object* v_p_u2082_671_, lean_object* v_p_u2081_672_, lean_object* v_acc_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(v_p_u2082_671_, v_p_u2081_672_, v_acc_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_682_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul(lean_object* v_p_u2081_685_, lean_object* v_p_u2082_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0, &l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0);
lean_inc_ref(v_a_692_);
v___x_696_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(v_p_u2082_686_, v_p_u2081_685_, v___x_695_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul___boxed(lean_object* v_p_u2081_697_, lean_object* v_p_u2082_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_u2081_697_, v_p_u2082_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec_ref(v_a_699_);
return v_res_707_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_to_int(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(lean_object* v_p_714_, lean_object* v_k_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_toCold_724_; lean_object* v_currRecDepth_725_; lean_object* v_ref_726_; uint16_t v_optionFlags_727_; uint8_t v_suppressElabErrors_728_; uint8_t v_isRecordingDeps_729_; lean_object* v_maxRecDepth_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_toCold_724_ = lean_ctor_get(v_a_721_, 0);
v_currRecDepth_725_ = lean_ctor_get(v_a_721_, 1);
v_ref_726_ = lean_ctor_get(v_a_721_, 2);
v_optionFlags_727_ = lean_ctor_get_uint16(v_a_721_, sizeof(void*)*3);
v_suppressElabErrors_728_ = lean_ctor_get_uint8(v_a_721_, sizeof(void*)*3 + 2);
v_isRecordingDeps_729_ = lean_ctor_get_uint8(v_a_721_, sizeof(void*)*3 + 3);
v_maxRecDepth_752_ = lean_ctor_get(v_toCold_724_, 3);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_nat_dec_eq(v_maxRecDepth_752_, v___x_753_);
if (v___x_754_ == 0)
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_eq(v_currRecDepth_725_, v_maxRecDepth_752_);
if (v___x_755_ == 0)
{
goto v___jp_730_;
}
else
{
lean_object* v___x_756_; 
lean_dec_ref(v_p_714_);
lean_inc(v_ref_726_);
v___x_756_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_726_);
return v___x_756_;
}
}
else
{
goto v___jp_730_;
}
v___jp_730_:
{
lean_object* v_zero_731_; uint8_t v_isZero_732_; 
v_zero_731_ = lean_unsigned_to_nat(0u);
v_isZero_732_ = lean_nat_dec_eq(v_k_715_, v_zero_731_);
if (v_isZero_732_ == 1)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec_ref(v_p_714_);
v___x_733_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
else
{
lean_object* v_one_735_; lean_object* v_n_736_; uint8_t v_isZero_737_; 
v_one_735_ = lean_unsigned_to_nat(1u);
v_n_736_ = lean_nat_sub(v_k_715_, v_one_735_);
v_isZero_737_ = lean_nat_dec_eq(v_n_736_, v_zero_731_);
if (v_isZero_737_ == 1)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_n_736_);
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v_p_714_);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
else
{
lean_object* v_n_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v_isZero_743_; 
v_n_740_ = lean_nat_sub(v_n_736_, v_one_735_);
lean_dec(v_n_736_);
v___x_741_ = lean_nat_add(v_currRecDepth_725_, v_one_735_);
lean_inc(v_ref_726_);
lean_inc_ref(v_toCold_724_);
v___x_742_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_742_, 0, v_toCold_724_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
lean_ctor_set(v___x_742_, 2, v_ref_726_);
lean_ctor_set_uint16(v___x_742_, sizeof(void*)*3, v_optionFlags_727_);
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*3 + 2, v_suppressElabErrors_728_);
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*3 + 3, v_isRecordingDeps_729_);
v_isZero_743_ = lean_nat_dec_eq(v_n_740_, v_zero_731_);
if (v_isZero_743_ == 1)
{
lean_object* v___x_744_; 
lean_dec(v_n_740_);
lean_inc_ref(v_p_714_);
v___x_744_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_714_, v_p_714_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v___x_742_, v_a_722_);
lean_dec_ref_known(v___x_742_, 3);
return v___x_744_;
}
else
{
lean_object* v_n_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_n_745_ = lean_nat_sub(v_n_740_, v_one_735_);
lean_dec(v_n_740_);
v___x_746_ = lean_unsigned_to_nat(2u);
v___x_747_ = lean_nat_add(v_n_745_, v___x_746_);
lean_dec(v_n_745_);
lean_inc_ref(v_p_714_);
v___x_748_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_714_, v___x_747_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v___x_742_, v_a_722_);
lean_dec(v___x_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
if (lean_obj_tag(v_a_749_) == 0)
{
lean_dec_ref_known(v___x_742_, 3);
lean_dec_ref(v_p_714_);
return v___x_748_;
}
else
{
lean_object* v_val_750_; lean_object* v___x_751_; 
lean_inc_ref(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v_val_750_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v_a_749_, 1);
v___x_751_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_714_, v_val_750_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v___x_742_, v_a_722_);
lean_dec_ref_known(v___x_742_, 3);
return v___x_751_;
}
}
else
{
lean_dec_ref_known(v___x_742_, 3);
lean_dec_ref(v_p_714_);
return v___x_748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___boxed(lean_object* v_p_757_, lean_object* v_k_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_757_, v_k_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_k_758_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(lean_object* v_p_768_, lean_object* v_k_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_toCold_778_; lean_object* v_currRecDepth_779_; lean_object* v_ref_780_; uint16_t v_optionFlags_781_; uint8_t v_suppressElabErrors_782_; uint8_t v_isRecordingDeps_783_; lean_object* v_maxRecDepth_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_toCold_778_ = lean_ctor_get(v_a_775_, 0);
v_currRecDepth_779_ = lean_ctor_get(v_a_775_, 1);
v_ref_780_ = lean_ctor_get(v_a_775_, 2);
v_optionFlags_781_ = lean_ctor_get_uint16(v_a_775_, sizeof(void*)*3);
v_suppressElabErrors_782_ = lean_ctor_get_uint8(v_a_775_, sizeof(void*)*3 + 2);
v_isRecordingDeps_783_ = lean_ctor_get_uint8(v_a_775_, sizeof(void*)*3 + 3);
v_maxRecDepth_802_ = lean_ctor_get(v_toCold_778_, 3);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_nat_dec_eq(v_maxRecDepth_802_, v___x_803_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; 
v___x_805_ = lean_nat_dec_eq(v_currRecDepth_779_, v_maxRecDepth_802_);
if (v___x_805_ == 0)
{
goto v___jp_784_;
}
else
{
lean_object* v___x_806_; 
lean_dec_ref(v_p_768_);
lean_inc(v_ref_780_);
v___x_806_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_780_);
return v___x_806_;
}
}
else
{
goto v___jp_784_;
}
v___jp_784_:
{
lean_object* v_zero_785_; uint8_t v_isZero_786_; 
v_zero_785_ = lean_unsigned_to_nat(0u);
v_isZero_786_ = lean_nat_dec_eq(v_k_769_, v_zero_785_);
if (v_isZero_786_ == 1)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_p_768_);
v___x_787_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
else
{
lean_object* v_one_789_; lean_object* v_n_790_; uint8_t v_isZero_791_; 
v_one_789_ = lean_unsigned_to_nat(1u);
v_n_790_ = lean_nat_sub(v_k_769_, v_one_789_);
v_isZero_791_ = lean_nat_dec_eq(v_n_790_, v_zero_785_);
if (v_isZero_791_ == 1)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_n_790_);
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v_p_768_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
else
{
lean_object* v_n_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_n_794_ = lean_nat_sub(v_n_790_, v_one_789_);
lean_dec(v_n_790_);
v___x_795_ = lean_nat_add(v_currRecDepth_779_, v_one_789_);
lean_inc(v_ref_780_);
lean_inc_ref(v_toCold_778_);
v___x_796_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_796_, 0, v_toCold_778_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
lean_ctor_set(v___x_796_, 2, v_ref_780_);
lean_ctor_set_uint16(v___x_796_, sizeof(void*)*3, v_optionFlags_781_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*3 + 2, v_suppressElabErrors_782_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*3 + 3, v_isRecordingDeps_783_);
v___x_797_ = lean_nat_add(v_n_794_, v_one_789_);
lean_dec(v_n_794_);
lean_inc_ref(v_p_768_);
v___x_798_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_768_, v___x_797_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v___x_796_, v_a_776_);
lean_dec(v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
if (lean_obj_tag(v_a_799_) == 0)
{
lean_dec_ref_known(v___x_796_, 3);
lean_dec_ref(v_p_768_);
return v___x_798_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_801_; 
lean_inc_ref(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v_val_800_ = lean_ctor_get(v_a_799_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v_a_799_, 1);
v___x_801_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_800_, v_p_768_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v___x_796_, v_a_776_);
lean_dec_ref_known(v___x_796_, 3);
return v___x_801_;
}
}
else
{
lean_dec_ref_known(v___x_796_, 3);
lean_dec_ref(v_p_768_);
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC___boxed(lean_object* v_p_807_, lean_object* v_k_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_807_, v_k_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_k_808_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_pow(lean_object* v_p_818_, lean_object* v_k_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
uint8_t v_commutative_828_; 
v_commutative_828_ = lean_ctor_get_uint8(v_a_820_, sizeof(void*)*3 + 1);
if (v_commutative_828_ == 0)
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_818_, v_k_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_818_, v_k_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_pow___boxed(lean_object* v_p_831_, lean_object* v_k_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_p_831_, v_k_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_k_832_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg(lean_object* v_k_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg___boxed(lean_object* v_k_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg(v_k_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27(lean_object* v_k_860_, lean_object* v_x_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_860_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___boxed(lean_object* v_k_870_, lean_object* v_x_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27(v_k_870_, v_x_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec_ref(v_x_871_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(lean_object* v_x_880_, lean_object* v_k_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_maxDegree_x3f_900_; 
v_maxDegree_x3f_900_ = lean_ctor_get(v_a_882_, 2);
if (lean_obj_tag(v_maxDegree_x3f_900_) == 1)
{
lean_object* v_val_901_; uint8_t v___x_902_; 
v_val_901_ = lean_ctor_get(v_maxDegree_x3f_900_, 0);
v___x_902_ = lean_nat_dec_lt(v_val_901_, v_k_881_);
if (v___x_902_ == 0)
{
goto v___jp_890_;
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec(v_x_880_);
v___x_903_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2);
v___x_904_ = l_Nat_reprFast(v_k_881_);
v___x_905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
v___x_906_ = l_Lean_MessageData_ofFormat(v___x_905_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_903_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_inc(v_val_901_);
v___x_910_ = l_Nat_reprFast(v_val_901_);
v___x_911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
v___x_912_ = l_Lean_MessageData_ofFormat(v___x_911_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_909_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_883_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; uint8_t v_verbose_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v_verbose_918_ = lean_ctor_get_uint8(v_a_917_, 0);
lean_dec(v_a_917_);
if (v_verbose_918_ == 0)
{
lean_dec_ref_known(v___x_915_, 2);
goto v___jp_897_;
}
else
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Meta_Sym_reportIssue(v___x_915_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_dec_ref_known(v___x_919_, 1);
goto v___jp_897_;
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref_known(v___x_915_, 2);
v_a_928_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_916_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_916_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
else
{
goto v___jp_890_;
}
v___jp_890_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_x_880_);
lean_ctor_set(v___x_891_, 1, v_k_881_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_893_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
v___jp_897_:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_box(0);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar___boxed(lean_object* v_x_936_, lean_object* v_k_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_x_936_, v_k_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg(lean_object* v_n_947_, lean_object* v_a_948_){
_start:
{
uint8_t v_semiring_950_; 
v_semiring_950_ = lean_ctor_get_uint8(v_a_948_, sizeof(void*)*3);
if (v_semiring_950_ == 0)
{
lean_object* v___x_951_; lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_968_; 
v___x_951_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_n_947_, v_a_948_);
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_968_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_968_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_968_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_val_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_967_; 
v_val_956_ = lean_ctor_get(v_a_952_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_967_ == 0)
{
v___x_958_ = v_a_952_;
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_val_956_);
lean_dec(v_a_952_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_val_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_962_);
v___x_964_ = v___x_954_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_969_ = lean_nat_abs(v_n_947_);
lean_dec(v_n_947_);
v___x_970_ = lean_nat_to_int(v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg___boxed(lean_object* v_n_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg(v_n_974_, v_a_975_);
lean_dec_ref(v_a_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode(lean_object* v_n_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_Sym_Arith_SafePoly_numNode___redArg(v_n_978_, v_a_979_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_numNode___boxed(lean_object* v_n_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Meta_Sym_Arith_SafePoly_numNode(v_n_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec_ref(v_a_989_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(lean_object* v_k_998_, lean_object* v_n_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; 
lean_inc(v_k_998_);
v___x_1008_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_998_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1052_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1052_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1052_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
if (lean_obj_tag(v_a_1009_) == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
lean_dec(v_k_998_);
v___x_1013_ = lean_box(0);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1050_; 
v_isSharedCheck_1050_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v_a_1009_, 0);
lean_dec(v_unused_1051_);
v___x_1018_ = v_a_1009_;
v_isShared_1019_ = v_isSharedCheck_1050_;
goto v_resetjp_1017_;
}
else
{
lean_dec(v_a_1009_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1050_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint8_t v_semiring_1020_; 
v_semiring_1020_ = lean_ctor_get_uint8(v_a_1000_, sizeof(void*)*3);
if (v_semiring_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1039_; 
lean_del_object(v___x_1018_);
lean_del_object(v___x_1011_);
v___x_1021_ = l_Int_pow(v_n_999_, v_k_998_);
lean_dec(v_k_998_);
v___x_1022_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1021_, v_a_1000_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_val_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1038_; 
v_val_1027_ = lean_ctor_get(v_a_1023_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_1023_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1029_ = v_a_1023_;
v_isShared_1030_ = v_isSharedCheck_1038_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_val_1027_);
lean_dec(v_a_1023_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1038_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_val_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1033_);
v___x_1035_ = v___x_1025_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1040_ = lean_nat_abs(v_n_999_);
v___x_1041_ = lean_nat_to_int(v___x_1040_);
v___x_1042_ = l_Int_pow(v___x_1041_, v_k_998_);
lean_dec(v_k_998_);
lean_dec(v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1043_);
v___x_1045_ = v___x_1018_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1045_);
v___x_1047_ = v___x_1011_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
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
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_k_998_);
v_a_1053_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1008_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1008_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow___boxed(lean_object* v_k_1061_, lean_object* v_n_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(v_k_1061_, v_n_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_n_1062_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_powNode(lean_object* v_a_1072_, lean_object* v_pa_1073_, lean_object* v_k_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_nat_dec_eq(v_k_1074_, v___x_1083_);
if (v___x_1084_ == 0)
{
switch(lean_obj_tag(v_a_1072_))
{
case 0:
{
lean_object* v_k_1085_; lean_object* v___x_1086_; 
lean_dec_ref(v_pa_1073_);
v_k_1085_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_k_1085_);
lean_dec_ref_known(v_a_1072_, 1);
v___x_1086_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(v_k_1074_, v_k_1085_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_k_1085_);
return v___x_1086_;
}
case 2:
{
lean_object* v_k_1087_; lean_object* v___x_1088_; 
lean_dec_ref(v_pa_1073_);
v_k_1087_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_k_1087_);
lean_dec_ref_known(v_a_1072_, 1);
v___x_1088_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(v_k_1074_, v_k_1087_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_k_1087_);
return v___x_1088_;
}
case 1:
{
lean_object* v_k_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec_ref(v_pa_1073_);
v_k_1089_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_k_1089_);
lean_dec_ref_known(v_a_1072_, 1);
v___x_1090_ = lean_nat_to_int(v_k_1089_);
v___x_1091_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNode_numPow(v_k_1074_, v___x_1090_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v___x_1090_);
return v___x_1091_;
}
case 3:
{
lean_object* v_i_1092_; lean_object* v___x_1093_; 
lean_dec_ref(v_pa_1073_);
v_i_1092_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_i_1092_);
lean_dec_ref_known(v_a_1072_, 1);
v___x_1093_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1092_, v_k_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
return v___x_1093_;
}
default: 
{
lean_object* v___x_1094_; 
lean_dec_ref(v_a_1072_);
v___x_1094_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_pa_1073_, v_k_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_k_1074_);
return v___x_1094_;
}
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_k_1074_);
lean_dec_ref(v_pa_1073_);
lean_dec_ref(v_a_1072_);
v___x_1095_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_powNode___boxed(lean_object* v_a_1097_, lean_object* v_pa_1098_, lean_object* v_k_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Meta_Sym_Arith_SafePoly_powNode(v_a_1097_, v_pa_1098_, v_k_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0);
v___x_1110_ = lean_int_neg(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(lean_object* v_e_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_n_1121_; lean_object* v___y_1122_; 
switch(lean_obj_tag(v_e_1111_))
{
case 1:
{
lean_object* v_k_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1190_; 
v_k_1153_ = lean_ctor_get(v_e_1111_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_e_1111_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1155_ = v_e_1111_;
v_isShared_1156_ = v_isSharedCheck_1190_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_k_1153_);
lean_dec(v_e_1111_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1190_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_nat_to_int(v_k_1153_);
v___x_1158_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1157_, v_a_1112_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1181_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1181_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1181_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
if (lean_obj_tag(v_a_1159_) == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_del_object(v___x_1155_);
v___x_1163_ = lean_box(0);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
else
{
lean_object* v_val_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1180_; 
v_val_1167_ = lean_ctor_get(v_a_1159_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_a_1159_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1169_ = v_a_1159_;
v_isShared_1170_ = v_isSharedCheck_1180_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_val_1167_);
lean_dec(v_a_1159_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1180_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 0);
lean_ctor_set(v___x_1155_, 0, v_val_1167_);
v___x_1172_ = v___x_1155_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_val_1167_);
v___x_1172_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1176_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1174_);
v___x_1176_ = v___x_1161_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_del_object(v___x_1155_);
v_a_1182_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1158_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1158_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1200_; 
v_i_1191_ = lean_ctor_get(v_e_1111_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_e_1111_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1193_ = v_e_1111_;
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_i_1191_);
lean_dec(v_e_1111_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_1191_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 1);
lean_ctor_set(v___x_1193_, 0, v___x_1195_);
v___x_1197_ = v___x_1193_;
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
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
case 4:
{
lean_object* v_a_1201_; lean_object* v___x_1202_; 
v_a_1201_ = lean_ctor_get(v_e_1111_, 0);
lean_inc_ref(v_a_1201_);
lean_dec_ref_known(v_e_1111_, 1);
v___x_1202_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1201_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
if (lean_obj_tag(v_a_1203_) == 0)
{
return v___x_1202_;
}
else
{
lean_object* v_val_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc_ref(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v_val_1204_ = lean_ctor_get(v_a_1203_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v_a_1203_, 1);
v___x_1205_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0);
v___x_1206_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v___x_1205_, v_val_1204_, v_a_1112_);
return v___x_1206_;
}
}
else
{
return v___x_1202_;
}
}
case 5:
{
lean_object* v_a_1207_; lean_object* v_b_1208_; lean_object* v___x_1209_; 
v_a_1207_ = lean_ctor_get(v_e_1111_, 0);
lean_inc_ref(v_a_1207_);
v_b_1208_ = lean_ctor_get(v_e_1111_, 1);
lean_inc_ref(v_b_1208_);
lean_dec_ref_known(v_e_1111_, 2);
v___x_1209_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1207_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
if (lean_obj_tag(v_a_1210_) == 0)
{
lean_dec_ref(v_b_1208_);
return v___x_1209_;
}
else
{
lean_object* v_val_1211_; lean_object* v___x_1212_; 
lean_inc_ref(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v_val_1211_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_a_1210_, 1);
v___x_1212_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1208_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
if (lean_obj_tag(v_a_1213_) == 0)
{
lean_dec(v_val_1211_);
return v___x_1212_;
}
else
{
lean_object* v_val_1214_; lean_object* v___x_1215_; 
lean_inc_ref(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v_val_1214_ = lean_ctor_get(v_a_1213_, 0);
lean_inc(v_val_1214_);
lean_dec_ref_known(v_a_1213_, 1);
v___x_1215_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1211_, v_val_1214_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
return v___x_1215_;
}
}
else
{
lean_dec(v_val_1211_);
return v___x_1212_;
}
}
}
else
{
lean_dec_ref(v_b_1208_);
return v___x_1209_;
}
}
case 6:
{
lean_object* v_a_1216_; lean_object* v_b_1217_; lean_object* v___x_1218_; 
v_a_1216_ = lean_ctor_get(v_e_1111_, 0);
lean_inc_ref(v_a_1216_);
v_b_1217_ = lean_ctor_get(v_e_1111_, 1);
lean_inc_ref(v_b_1217_);
lean_dec_ref_known(v_e_1111_, 2);
v___x_1218_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1216_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
if (lean_obj_tag(v_a_1219_) == 0)
{
lean_dec_ref(v_b_1217_);
return v___x_1218_;
}
else
{
lean_object* v_val_1220_; lean_object* v___x_1221_; 
lean_inc_ref(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v_val_1220_ = lean_ctor_get(v_a_1219_, 0);
lean_inc(v_val_1220_);
lean_dec_ref_known(v_a_1219_, 1);
v___x_1221_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1217_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
if (lean_obj_tag(v_a_1222_) == 0)
{
lean_dec(v_val_1220_);
return v___x_1221_;
}
else
{
lean_object* v_val_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_inc_ref(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v_val_1223_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v_a_1222_, 1);
v___x_1224_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0);
v___x_1225_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v___x_1224_, v_val_1223_, v_a_1112_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
if (lean_obj_tag(v_a_1226_) == 0)
{
lean_dec(v_val_1220_);
return v___x_1225_;
}
else
{
lean_object* v_val_1227_; lean_object* v___x_1228_; 
lean_inc_ref(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_val_1227_ = lean_ctor_get(v_a_1226_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_a_1226_, 1);
v___x_1228_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1220_, v_val_1227_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
return v___x_1228_;
}
}
else
{
lean_dec(v_val_1220_);
return v___x_1225_;
}
}
}
else
{
lean_dec(v_val_1220_);
return v___x_1221_;
}
}
}
else
{
lean_dec_ref(v_b_1217_);
return v___x_1218_;
}
}
case 7:
{
lean_object* v_a_1229_; lean_object* v_b_1230_; lean_object* v___x_1231_; 
v_a_1229_ = lean_ctor_get(v_e_1111_, 0);
lean_inc_ref(v_a_1229_);
v_b_1230_ = lean_ctor_get(v_e_1111_, 1);
lean_inc_ref(v_b_1230_);
lean_dec_ref_known(v_e_1111_, 2);
v___x_1231_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1229_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_dec_ref(v_b_1230_);
return v___x_1231_;
}
else
{
lean_object* v_val_1233_; lean_object* v___x_1234_; 
lean_inc_ref(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v_val_1233_ = lean_ctor_get(v_a_1232_, 0);
lean_inc(v_val_1233_);
lean_dec_ref_known(v_a_1232_, 1);
v___x_1234_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1230_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
if (lean_obj_tag(v_a_1235_) == 0)
{
lean_dec(v_val_1233_);
return v___x_1234_;
}
else
{
lean_object* v_val_1236_; lean_object* v___x_1237_; 
lean_inc_ref(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v_val_1236_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_val_1236_);
lean_dec_ref_known(v_a_1235_, 1);
v___x_1237_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_1233_, v_val_1236_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
return v___x_1237_;
}
}
else
{
lean_dec(v_val_1233_);
return v___x_1234_;
}
}
}
else
{
lean_dec_ref(v_b_1230_);
return v___x_1231_;
}
}
case 8:
{
lean_object* v_a_1238_; lean_object* v_k_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_a_1238_ = lean_ctor_get(v_e_1111_, 0);
lean_inc_ref(v_a_1238_);
v_k_1239_ = lean_ctor_get(v_e_1111_, 1);
lean_inc(v_k_1239_);
lean_dec_ref_known(v_e_1111_, 2);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_nat_dec_eq(v_k_1239_, v___x_1240_);
if (v___x_1241_ == 0)
{
switch(lean_obj_tag(v_a_1238_))
{
case 0:
{
lean_object* v_k_1242_; lean_object* v___x_1243_; 
v_k_1242_ = lean_ctor_get(v_a_1238_, 0);
lean_inc(v_k_1242_);
lean_dec_ref_known(v_a_1238_, 1);
lean_inc(v_k_1239_);
v___x_1243_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1239_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1290_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1290_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1290_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
if (lean_obj_tag(v_a_1244_) == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_dec(v_k_1242_);
lean_dec(v_k_1239_);
v___x_1248_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
else
{
lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1288_; 
lean_del_object(v___x_1246_);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_a_1244_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_a_1244_, 0);
lean_dec(v_unused_1289_);
v___x_1253_ = v_a_1244_;
v_isShared_1254_ = v_isSharedCheck_1288_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v_a_1244_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1288_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = l_Int_pow(v_k_1242_, v_k_1239_);
lean_dec(v_k_1239_);
lean_dec(v_k_1242_);
v___x_1256_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1255_, v_a_1112_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1279_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1279_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1279_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
if (lean_obj_tag(v_a_1257_) == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
lean_del_object(v___x_1253_);
v___x_1261_ = lean_box(0);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
else
{
lean_object* v_val_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1278_; 
v_val_1265_ = lean_ctor_get(v_a_1257_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_a_1257_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1267_ = v_a_1257_;
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_val_1265_);
lean_dec(v_a_1257_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 0);
lean_ctor_set(v___x_1253_, 0, v_val_1265_);
v___x_1270_ = v___x_1253_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_val_1265_);
v___x_1270_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1270_);
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1272_);
v___x_1274_ = v___x_1259_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_del_object(v___x_1253_);
v_a_1280_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1256_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1256_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_k_1242_);
lean_dec(v_k_1239_);
v_a_1291_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1243_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1243_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
case 3:
{
lean_object* v_i_1299_; lean_object* v___x_1300_; 
v_i_1299_ = lean_ctor_get(v_a_1238_, 0);
lean_inc(v_i_1299_);
lean_dec_ref_known(v_a_1238_, 1);
v___x_1300_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1299_, v_k_1239_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
return v___x_1300_;
}
default: 
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1238_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
if (lean_obj_tag(v_a_1302_) == 0)
{
lean_dec(v_k_1239_);
return v___x_1301_;
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1304_; 
lean_inc_ref(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v_val_1303_ = lean_ctor_get(v_a_1302_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v_a_1302_, 1);
v___x_1304_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_val_1303_, v_k_1239_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_k_1239_);
return v___x_1304_;
}
}
else
{
lean_dec(v_k_1239_);
return v___x_1301_;
}
}
}
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v_k_1239_);
lean_dec_ref(v_a_1238_);
v___x_1305_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
default: 
{
lean_object* v_k_1307_; 
v_k_1307_ = lean_ctor_get(v_e_1111_, 0);
lean_inc(v_k_1307_);
lean_dec_ref(v_e_1111_);
v_n_1121_ = v_k_1307_;
v___y_1122_ = v_a_1112_;
goto v___jp_1120_;
}
}
v___jp_1120_:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_n_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1144_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1144_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1144_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
if (lean_obj_tag(v_a_1124_) == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = lean_box(0);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1128_);
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_object* v_val_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1143_; 
v_val_1132_ = lean_ctor_get(v_a_1124_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_a_1124_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1134_ = v_a_1124_;
v_isShared_1135_ = v_isSharedCheck_1143_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_val_1132_);
lean_dec(v_a_1124_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1143_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_val_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1138_);
v___x_1140_ = v___x_1126_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
v_a_1145_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1123_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1123_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___boxed(lean_object* v_e_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0, &l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(lean_object* v_e_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
switch(lean_obj_tag(v_e_1320_))
{
case 0:
{
lean_object* v_k_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1340_; 
v_k_1329_ = lean_ctor_get(v_e_1320_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_e_1320_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1331_ = v_e_1320_;
v_isShared_1332_ = v_isSharedCheck_1340_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_k_1329_);
lean_dec(v_e_1320_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1340_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1333_ = lean_nat_abs(v_k_1329_);
lean_dec(v_k_1329_);
v___x_1334_ = lean_nat_to_int(v___x_1333_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1334_);
v___x_1336_ = v___x_1331_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
}
case 1:
{
lean_object* v_k_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1351_; 
v_k_1341_ = lean_ctor_get(v_e_1320_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_e_1320_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1343_ = v_e_1320_;
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_k_1341_);
lean_dec(v_e_1320_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = lean_nat_to_int(v_k_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set_tag(v___x_1343_, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1345_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
}
case 3:
{
lean_object* v_i_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1361_; 
v_i_1352_ = lean_ctor_get(v_e_1320_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_e_1320_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1354_ = v_e_1320_;
v_isShared_1355_ = v_isSharedCheck_1361_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_i_1352_);
lean_dec(v_e_1320_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1361_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 1);
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
}
case 5:
{
lean_object* v_a_1362_; lean_object* v_b_1363_; lean_object* v___x_1364_; 
v_a_1362_ = lean_ctor_get(v_e_1320_, 0);
lean_inc_ref(v_a_1362_);
v_b_1363_ = lean_ctor_get(v_e_1320_, 1);
lean_inc_ref(v_b_1363_);
lean_dec_ref_known(v_e_1320_, 2);
v___x_1364_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1362_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
if (lean_obj_tag(v_a_1365_) == 0)
{
lean_dec_ref(v_b_1363_);
return v___x_1364_;
}
else
{
lean_object* v_val_1366_; lean_object* v___x_1367_; 
lean_inc_ref(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v_val_1366_ = lean_ctor_get(v_a_1365_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v_a_1365_, 1);
v___x_1367_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_b_1363_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
if (lean_obj_tag(v_a_1368_) == 0)
{
lean_dec(v_val_1366_);
return v___x_1367_;
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1370_; 
lean_inc_ref(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v_val_1369_ = lean_ctor_get(v_a_1368_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v_a_1368_, 1);
v___x_1370_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1366_, v_val_1369_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1370_;
}
}
else
{
lean_dec(v_val_1366_);
return v___x_1367_;
}
}
}
else
{
lean_dec_ref(v_b_1363_);
return v___x_1364_;
}
}
case 7:
{
lean_object* v_a_1371_; lean_object* v_b_1372_; lean_object* v___x_1373_; 
v_a_1371_ = lean_ctor_get(v_e_1320_, 0);
lean_inc_ref(v_a_1371_);
v_b_1372_ = lean_ctor_get(v_e_1320_, 1);
lean_inc_ref(v_b_1372_);
lean_dec_ref_known(v_e_1320_, 2);
v___x_1373_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1371_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
if (lean_obj_tag(v_a_1374_) == 0)
{
lean_dec_ref(v_b_1372_);
return v___x_1373_;
}
else
{
lean_object* v_val_1375_; lean_object* v___x_1376_; 
lean_inc_ref(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v_val_1375_ = lean_ctor_get(v_a_1374_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v_a_1374_, 1);
v___x_1376_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_b_1372_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
if (lean_obj_tag(v_a_1377_) == 0)
{
lean_dec(v_val_1375_);
return v___x_1376_;
}
else
{
lean_object* v_val_1378_; lean_object* v___x_1379_; 
lean_inc_ref(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v_val_1378_ = lean_ctor_get(v_a_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref_known(v_a_1377_, 1);
v___x_1379_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_1375_, v_val_1378_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1379_;
}
}
else
{
lean_dec(v_val_1375_);
return v___x_1376_;
}
}
}
else
{
lean_dec_ref(v_b_1372_);
return v___x_1373_;
}
}
case 8:
{
lean_object* v_a_1380_; lean_object* v_k_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_a_1380_ = lean_ctor_get(v_e_1320_, 0);
lean_inc_ref(v_a_1380_);
v_k_1381_ = lean_ctor_get(v_e_1320_, 1);
lean_inc(v_k_1381_);
lean_dec_ref_known(v_e_1320_, 2);
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = lean_nat_dec_eq(v_k_1381_, v___x_1382_);
if (v___x_1383_ == 0)
{
switch(lean_obj_tag(v_a_1380_))
{
case 0:
{
lean_object* v_k_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1423_; 
v_k_1384_ = lean_ctor_get(v_a_1380_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_a_1380_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1386_ = v_a_1380_;
v_isShared_1387_ = v_isSharedCheck_1423_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_k_1384_);
lean_dec(v_a_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1423_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; 
lean_inc(v_k_1381_);
v___x_1388_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1381_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1414_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1414_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1414_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
if (lean_obj_tag(v_a_1389_) == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_del_object(v___x_1386_);
lean_dec(v_k_1384_);
lean_dec(v_k_1381_);
v___x_1393_ = lean_box(0);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1412_; 
v_isSharedCheck_1412_ = !lean_is_exclusive(v_a_1389_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_a_1389_, 0);
lean_dec(v_unused_1413_);
v___x_1398_ = v_a_1389_;
v_isShared_1399_ = v_isSharedCheck_1412_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v_a_1389_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1412_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1400_ = lean_nat_abs(v_k_1384_);
lean_dec(v_k_1384_);
v___x_1401_ = lean_nat_to_int(v___x_1400_);
v___x_1402_ = l_Int_pow(v___x_1401_, v_k_1381_);
lean_dec(v_k_1381_);
lean_dec(v___x_1401_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1402_);
v___x_1404_ = v___x_1386_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1406_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1404_);
v___x_1406_ = v___x_1398_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1406_);
v___x_1408_ = v___x_1391_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_del_object(v___x_1386_);
lean_dec(v_k_1384_);
lean_dec(v_k_1381_);
v_a_1415_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1388_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1388_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1424_; lean_object* v___x_1425_; 
v_i_1424_ = lean_ctor_get(v_a_1380_, 0);
lean_inc(v_i_1424_);
lean_dec_ref_known(v_a_1380_, 1);
v___x_1425_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1424_, v_k_1381_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1425_;
}
default: 
{
lean_object* v___x_1426_; 
v___x_1426_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1380_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
if (lean_obj_tag(v_a_1427_) == 0)
{
lean_dec(v_k_1381_);
return v___x_1426_;
}
else
{
lean_object* v_val_1428_; lean_object* v___x_1429_; 
lean_inc_ref(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v_val_1428_ = lean_ctor_get(v_a_1427_, 0);
lean_inc(v_val_1428_);
lean_dec_ref_known(v_a_1427_, 1);
v___x_1429_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_val_1428_, v_k_1381_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_k_1381_);
return v___x_1429_;
}
}
else
{
lean_dec(v_k_1381_);
return v___x_1426_;
}
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v_k_1381_);
lean_dec_ref(v_a_1380_);
v___x_1430_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
default: 
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v_e_1320_);
v___x_1432_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___boxed(lean_object* v_e_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f(lean_object* v_e_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
uint8_t v_semiring_1453_; 
v_semiring_1453_ = lean_ctor_get_uint8(v_a_1445_, sizeof(void*)*3);
if (v_semiring_1453_ == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f___boxed(lean_object* v_e_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Meta_Sym_Arith_toPoly_x3f(v_e_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec_ref(v_a_1457_);
return v_res_1465_;
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
