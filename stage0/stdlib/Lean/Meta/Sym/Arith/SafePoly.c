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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_numTerms(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
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
lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___redArg(lean_object* v_x_1_, lean_object* v_cfg_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_PolyM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_cfg_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_res_11_;
v_res_11_ = l_Lean_Meta_Sym_Arith_PolyM_run___redArg(v_x_1_, v_cfg_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___redArg___boxed(lean_object* v_x_12_, lean_object* v_cfg_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_Sym_Arith_PolyM_run___redArg(v_x_12_, v_cfg_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_a_17_);
lean_dec_ref(v_a_16_);
lean_dec(v_a_15_);
lean_dec_ref(v_a_14_);
return v_res_21_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_PolyM_run(lean_object* v_00_u03b1_22_, lean_object* v_x_23_, lean_object* v_cfg_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v___x_32_; 
lean_inc(v_a_30_);
lean_inc_ref(v_a_29_);
lean_inc(v_a_28_);
lean_inc_ref(v_a_27_);
lean_inc(v_a_26_);
lean_inc_ref(v_a_25_);
v___x_32_ = lean_apply_8(v_x_23_, v_cfg_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, lean_box(0));
return v___x_32_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_PolyM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_23_ = stack[1].m_obj;
lean_object* v_cfg_24_ = stack[2].m_obj;
lean_object* v_a_25_ = stack[3].m_obj;
lean_object* v_a_26_ = stack[4].m_obj;
lean_object* v_a_27_ = stack[5].m_obj;
lean_object* v_a_28_ = stack[6].m_obj;
lean_object* v_a_29_ = stack[7].m_obj;
lean_object* v_a_30_ = stack[8].m_obj;
lean_object* v_res_33_;
v_res_33_ = l_Lean_Meta_Sym_Arith_PolyM_run(lean_box(0), v_x_23_, v_cfg_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_PolyM_run___boxed(lean_object* v_00_u03b1_34_, lean_object* v_x_35_, lean_object* v_cfg_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Sym_Arith_PolyM_run(v_00_u03b1_34_, v_x_35_, v_cfg_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar_spec__0(lean_object* v_a_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_nat_to_int(v_a_45_);
return v___x_46_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_char_x3f_50_; 
v_char_x3f_50_ = lean_ctor_get(v_a_48_, 0);
if (lean_obj_tag(v_char_x3f_50_) == 1)
{
lean_object* v_val_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_val_51_ = lean_ctor_get(v_char_x3f_50_, 0);
lean_inc(v_val_51_);
v___x_52_ = lean_nat_to_int(v_val_51_);
v___x_53_ = lean_int_emod(v_a_47_, v___x_52_);
lean_dec(v___x_52_);
lean_dec(v_a_47_);
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_56_, 0, v_a_47_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_47_ = stack[0].m_obj;
lean_object* v_a_48_ = stack[1].m_obj;
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_a_47_, v_a_48_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg___boxed(lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_a_59_, v_a_60_);
lean_dec_ref(v_a_60_);
return v_res_62_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar(lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_a_63_, v_a_64_);
return v___x_72_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_63_ = stack[0].m_obj;
lean_object* v_a_64_ = stack[1].m_obj;
lean_object* v_a_65_ = stack[2].m_obj;
lean_object* v_a_66_ = stack[3].m_obj;
lean_object* v_a_67_ = stack[4].m_obj;
lean_object* v_a_68_ = stack[5].m_obj;
lean_object* v_a_69_ = stack[6].m_obj;
lean_object* v_a_70_ = stack[7].m_obj;
lean_object* v_res_73_;
v_res_73_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar(v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___boxed(lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar(v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec_ref(v_a_75_);
return v_res_83_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__1));
v___x_88_ = l_Lean_stringToMessageData(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__3));
v___x_91_ = l_Lean_stringToMessageData(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__5));
v___x_94_ = l_Lean_stringToMessageData(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__7));
v___x_97_ = l_Lean_stringToMessageData(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__9));
v___x_100_ = l_Lean_stringToMessageData(v___x_99_);
return v___x_100_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(lean_object* v_p_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_maxTerms_x3f_116_; lean_object* v_maxDegree_x3f_117_; lean_object* v___y_119_; lean_object* v___y_120_; lean_object* v___y_121_; lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v___y_124_; 
v_maxTerms_x3f_116_ = lean_ctor_get(v_a_102_, 1);
v_maxDegree_x3f_117_ = lean_ctor_get(v_a_102_, 2);
if (lean_obj_tag(v_maxTerms_x3f_116_) == 1)
{
lean_object* v_val_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_val_165_ = lean_ctor_get(v_maxTerms_x3f_116_, 0);
v___x_166_ = l_Lean_Grind_CommRing_Poly_numTerms(v_p_101_);
v___x_167_ = lean_nat_dec_lt(v_val_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_dec(v___x_166_);
v___y_119_ = v_a_103_;
v___y_120_ = v_a_104_;
v___y_121_ = v_a_105_;
v___y_122_ = v_a_106_;
v___y_123_ = v_a_107_;
v___y_124_ = v_a_108_;
goto v___jp_118_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__8);
v___x_169_ = l_Nat_reprFast(v___x_166_);
v___x_170_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
v___x_171_ = l_Lean_MessageData_ofFormat(v___x_170_);
v___x_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_168_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__10);
v___x_174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
lean_inc(v_val_165_);
v___x_175_ = l_Nat_reprFast(v_val_165_);
v___x_176_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = l_Lean_MessageData_ofFormat(v___x_176_);
v___x_178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_174_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6);
v___x_180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_103_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; uint8_t v_verbose_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v_verbose_183_ = lean_ctor_get_uint8(v_a_182_, 0);
lean_dec(v_a_182_);
if (v_verbose_183_ == 0)
{
lean_dec_ref_known(v___x_180_, 2);
goto v___jp_110_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Sym_reportIssue(v___x_180_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_dec_ref_known(v___x_184_, 1);
goto v___jp_110_;
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref_known(v___x_180_, 2);
v_a_193_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_181_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_181_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
v___y_119_ = v_a_103_;
v___y_120_ = v_a_104_;
v___y_121_ = v_a_105_;
v___y_122_ = v_a_106_;
v___y_123_ = v_a_107_;
v___y_124_ = v_a_108_;
goto v___jp_118_;
}
v___jp_110_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_box(0);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
v___jp_113_:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_box(0);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
v___jp_118_:
{
if (lean_obj_tag(v_maxDegree_x3f_117_) == 1)
{
lean_object* v_val_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_val_125_ = lean_ctor_get(v_maxDegree_x3f_117_, 0);
v___x_126_ = l_Lean_Grind_CommRing_Poly_degree(v_p_101_);
v___x_127_ = lean_nat_dec_lt(v_val_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v___x_126_);
v___x_128_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__0));
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_130_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2);
v___x_131_ = l_Nat_reprFast(v___x_126_);
v___x_132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
v___x_133_ = l_Lean_MessageData_ofFormat(v___x_132_);
v___x_134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_130_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4);
v___x_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
lean_inc(v_val_125_);
v___x_137_ = l_Nat_reprFast(v_val_125_);
v___x_138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
v___x_139_ = l_Lean_MessageData_ofFormat(v___x_138_);
v___x_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_136_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_119_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; uint8_t v_verbose_145_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_a_144_);
lean_dec_ref_known(v___x_143_, 1);
v_verbose_145_ = lean_ctor_get_uint8(v_a_144_, 0);
lean_dec(v_a_144_);
if (v_verbose_145_ == 0)
{
lean_dec_ref_known(v___x_142_, 2);
goto v___jp_113_;
}
else
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Sym_reportIssue(v___x_142_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_dec_ref_known(v___x_146_, 1);
goto v___jp_113_;
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref_known(v___x_142_, 2);
v_a_155_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_143_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_143_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__0));
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_101_ = stack[0].m_obj;
lean_object* v_a_102_ = stack[1].m_obj;
lean_object* v_a_103_ = stack[2].m_obj;
lean_object* v_a_104_ = stack[3].m_obj;
lean_object* v_a_105_ = stack[4].m_obj;
lean_object* v_a_106_ = stack[5].m_obj;
lean_object* v_a_107_ = stack[6].m_obj;
lean_object* v_a_108_ = stack[7].m_obj;
lean_object* v_res_201_;
v_res_201_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(v_p_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___boxed(lean_object* v_p_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(v_p_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec_ref(v_p_202_);
return v_res_211_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(lean_object* v_p_212_, lean_object* v_k_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_char_x3f_216_; 
v_char_x3f_216_ = lean_ctor_get(v_a_214_, 0);
if (lean_obj_tag(v_char_x3f_216_) == 1)
{
lean_object* v_val_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_val_217_ = lean_ctor_get(v_char_x3f_216_, 0);
lean_inc(v_val_217_);
v___x_218_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_212_, v_k_213_, v_val_217_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_212_, v_k_213_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_212_ = stack[0].m_obj;
lean_object* v_k_213_ = stack[1].m_obj;
lean_object* v_a_214_ = stack[2].m_obj;
lean_object* v_res_224_;
v_res_224_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_212_, v_k_213_, v_a_214_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg___boxed(lean_object* v_p_225_, lean_object* v_k_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_225_, v_k_226_, v_a_227_);
lean_dec_ref(v_a_227_);
lean_dec(v_k_226_);
return v_res_229_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst(lean_object* v_p_230_, lean_object* v_k_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_230_, v_k_231_, v_a_232_);
return v___x_240_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_addConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_230_ = stack[0].m_obj;
lean_object* v_k_231_ = stack[1].m_obj;
lean_object* v_a_232_ = stack[2].m_obj;
lean_object* v_a_233_ = stack[3].m_obj;
lean_object* v_a_234_ = stack[4].m_obj;
lean_object* v_a_235_ = stack[5].m_obj;
lean_object* v_a_236_ = stack[6].m_obj;
lean_object* v_a_237_ = stack[7].m_obj;
lean_object* v_a_238_ = stack[8].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst(v_p_230_, v_k_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_addConst___boxed(lean_object* v_p_242_, lean_object* v_k_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst(v_p_242_, v_k_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_k_243_);
return v_res_252_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(lean_object* v_k_253_, lean_object* v_p_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_char_x3f_257_; 
v_char_x3f_257_ = lean_ctor_get(v_a_255_, 0);
if (lean_obj_tag(v_char_x3f_257_) == 1)
{
lean_object* v_val_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_val_258_ = lean_ctor_get(v_char_x3f_257_, 0);
lean_inc(v_val_258_);
v___x_259_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_253_, v_p_254_, v_val_258_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_253_, v_p_254_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_253_ = stack[0].m_obj;
lean_object* v_p_254_ = stack[1].m_obj;
lean_object* v_a_255_ = stack[2].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_253_, v_p_254_, v_a_255_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg___boxed(lean_object* v_k_266_, lean_object* v_p_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_266_, v_p_267_, v_a_268_);
lean_dec_ref(v_a_268_);
lean_dec(v_k_266_);
return v_res_270_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst(lean_object* v_k_271_, lean_object* v_p_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_271_, v_p_272_, v_a_273_);
return v___x_281_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_mulConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_271_ = stack[0].m_obj;
lean_object* v_p_272_ = stack[1].m_obj;
lean_object* v_a_273_ = stack[2].m_obj;
lean_object* v_a_274_ = stack[3].m_obj;
lean_object* v_a_275_ = stack[4].m_obj;
lean_object* v_a_276_ = stack[5].m_obj;
lean_object* v_a_277_ = stack[6].m_obj;
lean_object* v_a_278_ = stack[7].m_obj;
lean_object* v_a_279_ = stack[8].m_obj;
lean_object* v_res_282_;
v_res_282_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst(v_k_271_, v_p_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulConst___boxed(lean_object* v_k_283_, lean_object* v_p_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst(v_k_283_, v_p_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_k_283_);
return v_res_293_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(lean_object* v_k_294_, lean_object* v_m_295_, lean_object* v_p_296_, lean_object* v_a_297_){
_start:
{
uint8_t v_commutative_299_; 
v_commutative_299_ = lean_ctor_get_uint8(v_a_297_, sizeof(void*)*3 + 1);
if (v_commutative_299_ == 0)
{
lean_object* v_char_x3f_300_; 
v_char_x3f_300_ = lean_ctor_get(v_a_297_, 0);
if (lean_obj_tag(v_char_x3f_300_) == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_294_, v_m_295_, v_p_296_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
else
{
lean_object* v_val_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_val_304_ = lean_ctor_get(v_char_x3f_300_, 0);
lean_inc(v_val_304_);
v___x_305_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_294_, v_m_295_, v_p_296_, v_val_304_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
else
{
lean_object* v_char_x3f_308_; 
v_char_x3f_308_ = lean_ctor_get(v_a_297_, 0);
if (lean_obj_tag(v_char_x3f_308_) == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_294_, v_m_295_, v_p_296_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_val_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_val_312_ = lean_ctor_get(v_char_x3f_308_, 0);
lean_inc(v_val_312_);
v___x_313_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_294_, v_m_295_, v_p_296_, v_val_312_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_294_ = stack[0].m_obj;
lean_object* v_m_295_ = stack[1].m_obj;
lean_object* v_p_296_ = stack[2].m_obj;
lean_object* v_a_297_ = stack[3].m_obj;
lean_object* v_res_316_;
v_res_316_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_294_, v_m_295_, v_p_296_, v_a_297_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg___boxed(lean_object* v_k_317_, lean_object* v_m_318_, lean_object* v_p_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_317_, v_m_318_, v_p_319_, v_a_320_);
lean_dec_ref(v_a_320_);
lean_dec(v_k_317_);
return v_res_322_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon(lean_object* v_k_323_, lean_object* v_m_324_, lean_object* v_p_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_323_, v_m_324_, v_p_325_, v_a_326_);
return v___x_334_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_mulMon_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_323_ = stack[0].m_obj;
lean_object* v_m_324_ = stack[1].m_obj;
lean_object* v_p_325_ = stack[2].m_obj;
lean_object* v_a_326_ = stack[3].m_obj;
lean_object* v_a_327_ = stack[4].m_obj;
lean_object* v_a_328_ = stack[5].m_obj;
lean_object* v_a_329_ = stack[6].m_obj;
lean_object* v_a_330_ = stack[7].m_obj;
lean_object* v_a_331_ = stack[8].m_obj;
lean_object* v_a_332_ = stack[9].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon(v_k_323_, v_m_324_, v_p_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mulMon___boxed(lean_object* v_k_336_, lean_object* v_m_337_, lean_object* v_p_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon(v_k_336_, v_m_337_, v_p_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_k_336_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = l_Lean_maxRecDepthErrorMessage;
v___x_354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__3);
v___x_356_ = l_Lean_MessageData_ofFormat(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__4);
v___x_358_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__2));
v___x_359_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
return v___x_359_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(lean_object* v_ref_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___closed__5);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_ref_360_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_360_ = stack[0].m_obj;
lean_object* v_res_365_;
v_res_365_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_360_);
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg___boxed(lean_object* v_ref_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_366_);
return v_res_368_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0(lean_object* v_00_u03b1_369_, lean_object* v_ref_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_370_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_370_ = stack[1].m_obj;
lean_object* v___y_371_ = stack[2].m_obj;
lean_object* v___y_372_ = stack[3].m_obj;
lean_object* v___y_373_ = stack[4].m_obj;
lean_object* v___y_374_ = stack[5].m_obj;
lean_object* v___y_375_ = stack[6].m_obj;
lean_object* v___y_376_ = stack[7].m_obj;
lean_object* v___y_377_ = stack[8].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0(lean_box(0), v_ref_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___boxed(lean_object* v_00_u03b1_381_, lean_object* v_ref_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0(v_00_u03b1_381_, v_ref_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_391_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_nat_to_int(v___x_392_);
return v___x_393_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(lean_object* v_p_u2081_394_, lean_object* v_p_u2082_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_toCold_404_; lean_object* v_currRecDepth_405_; lean_object* v_ref_406_; uint16_t v_optionFlags_407_; uint8_t v_suppressElabErrors_408_; uint8_t v_isRecordingDeps_409_; lean_object* v_maxRecDepth_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_toCold_404_ = lean_ctor_get(v_a_401_, 0);
lean_inc_ref(v_toCold_404_);
v_currRecDepth_405_ = lean_ctor_get(v_a_401_, 1);
lean_inc(v_currRecDepth_405_);
v_ref_406_ = lean_ctor_get(v_a_401_, 2);
lean_inc(v_ref_406_);
v_optionFlags_407_ = lean_ctor_get_uint16(v_a_401_, sizeof(void*)*3);
v_suppressElabErrors_408_ = lean_ctor_get_uint8(v_a_401_, sizeof(void*)*3 + 2);
v_isRecordingDeps_409_ = lean_ctor_get_uint8(v_a_401_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_401_);
v_maxRecDepth_571_ = lean_ctor_get(v_toCold_404_, 3);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_nat_dec_eq(v_maxRecDepth_571_, v___x_572_);
if (v___x_573_ == 0)
{
uint8_t v___x_574_; 
v___x_574_ = lean_nat_dec_eq(v_currRecDepth_405_, v_maxRecDepth_571_);
if (v___x_574_ == 0)
{
goto v___jp_410_;
}
else
{
lean_object* v___x_575_; 
lean_dec(v_currRecDepth_405_);
lean_dec_ref(v_toCold_404_);
lean_dec_ref(v_p_u2082_395_);
lean_dec_ref(v_p_u2081_394_);
v___x_575_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_406_);
return v___x_575_;
}
}
else
{
goto v___jp_410_;
}
v___jp_410_:
{
if (lean_obj_tag(v_p_u2081_394_) == 0)
{
lean_dec(v_ref_406_);
lean_dec(v_currRecDepth_405_);
lean_dec_ref(v_toCold_404_);
if (lean_obj_tag(v_p_u2082_395_) == 0)
{
lean_object* v_k_411_; lean_object* v_k_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_449_; 
v_k_411_ = lean_ctor_get(v_p_u2081_394_, 0);
lean_inc(v_k_411_);
lean_dec_ref_known(v_p_u2081_394_, 1);
v_k_412_ = lean_ctor_get(v_p_u2082_395_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_p_u2082_395_);
if (v_isSharedCheck_449_ == 0)
{
v___x_414_ = v_p_u2082_395_;
v_isShared_415_ = v_isSharedCheck_449_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_k_412_);
lean_dec(v_p_u2082_395_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_449_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_int_add(v_k_411_, v_k_412_);
lean_dec(v_k_412_);
lean_dec(v_k_411_);
v___x_417_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_416_, v_a_396_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_440_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_440_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_440_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_440_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
if (lean_obj_tag(v_a_418_) == 0)
{
lean_object* v___x_422_; lean_object* v___x_424_; 
lean_del_object(v___x_414_);
v___x_422_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_439_; 
v_val_426_ = lean_ctor_get(v_a_418_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_439_ == 0)
{
v___x_428_ = v_a_418_;
v_isShared_429_ = v_isSharedCheck_439_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v_a_418_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_439_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_val_426_);
v___x_431_ = v___x_414_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_val_426_);
v___x_431_ = v_reuseFailAlloc_438_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_431_);
v___x_433_ = v___x_428_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_437_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_433_);
v___x_435_ = v___x_420_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_del_object(v___x_414_);
v_a_441_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_417_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_417_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
else
{
lean_object* v_k_450_; lean_object* v___x_451_; 
v_k_450_ = lean_ctor_get(v_p_u2081_394_, 0);
lean_inc(v_k_450_);
lean_dec_ref_known(v_p_u2081_394_, 1);
v___x_451_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_u2082_395_, v_k_450_, v_a_396_);
lean_dec(v_k_450_);
return v___x_451_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_395_) == 0)
{
lean_object* v_k_452_; lean_object* v___x_453_; 
lean_dec(v_ref_406_);
lean_dec(v_currRecDepth_405_);
lean_dec_ref(v_toCold_404_);
v_k_452_ = lean_ctor_get(v_p_u2082_395_, 0);
lean_inc(v_k_452_);
lean_dec_ref_known(v_p_u2082_395_, 1);
v___x_453_ = l_Lean_Meta_Sym_Arith_SafePoly_addConst___redArg(v_p_u2081_394_, v_k_452_, v_a_396_);
lean_dec(v_k_452_);
return v___x_453_;
}
else
{
lean_object* v_k_454_; lean_object* v_v_455_; lean_object* v_p_456_; lean_object* v_k_457_; lean_object* v_v_458_; lean_object* v_p_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_k_454_ = lean_ctor_get(v_p_u2081_394_, 0);
v_v_455_ = lean_ctor_get(v_p_u2081_394_, 1);
v_p_456_ = lean_ctor_get(v_p_u2081_394_, 2);
v_k_457_ = lean_ctor_get(v_p_u2082_395_, 0);
v_v_458_ = lean_ctor_get(v_p_u2082_395_, 1);
v_p_459_ = lean_ctor_get(v_p_u2082_395_, 2);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_add(v_currRecDepth_405_, v___x_460_);
lean_dec(v_currRecDepth_405_);
v___x_462_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_462_, 0, v_toCold_404_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_ctor_set(v___x_462_, 2, v_ref_406_);
lean_ctor_set_uint16(v___x_462_, sizeof(void*)*3, v_optionFlags_407_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*3 + 2, v_suppressElabErrors_408_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*3 + 3, v_isRecordingDeps_409_);
v___x_463_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_455_, v_v_458_);
switch(v___x_463_)
{
case 0:
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_488_; 
lean_inc_ref(v_p_459_);
lean_inc(v_v_458_);
lean_inc(v_k_457_);
v_isSharedCheck_488_ = !lean_is_exclusive(v_p_u2082_395_);
if (v_isSharedCheck_488_ == 0)
{
lean_object* v_unused_489_; lean_object* v_unused_490_; lean_object* v_unused_491_; 
v_unused_489_ = lean_ctor_get(v_p_u2082_395_, 2);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_p_u2082_395_, 1);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_p_u2082_395_, 0);
lean_dec(v_unused_491_);
v___x_465_ = v_p_u2082_395_;
v_isShared_466_ = v_isSharedCheck_488_;
goto v_resetjp_464_;
}
else
{
lean_dec(v_p_u2082_395_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_488_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_394_, v_p_459_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v___x_462_, v_a_402_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
if (lean_obj_tag(v_a_468_) == 0)
{
lean_del_object(v___x_465_);
lean_dec(v_v_458_);
lean_dec(v_k_457_);
return v___x_467_;
}
else
{
lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_486_; 
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v___x_467_, 0);
lean_dec(v_unused_487_);
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_486_;
goto v_resetjp_469_;
}
else
{
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_486_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_val_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_485_; 
v_val_472_ = lean_ctor_get(v_a_468_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_485_ == 0)
{
v___x_474_ = v_a_468_;
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_val_472_);
lean_dec(v_a_468_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 2, v_val_472_);
v___x_477_ = v___x_465_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_k_457_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_v_458_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_val_472_);
v___x_477_ = v_reuseFailAlloc_484_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_479_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_477_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_483_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_479_);
v___x_481_ = v___x_470_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_465_);
lean_dec(v_v_458_);
lean_dec(v_k_457_);
return v___x_467_;
}
}
}
case 1:
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_539_; 
lean_inc_ref(v_p_459_);
lean_inc(v_k_457_);
lean_inc_ref(v_p_456_);
lean_inc(v_v_455_);
lean_inc(v_k_454_);
lean_dec_ref_known(v_p_u2081_394_, 3);
v_isSharedCheck_539_ = !lean_is_exclusive(v_p_u2082_395_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; lean_object* v_unused_542_; 
v_unused_540_ = lean_ctor_get(v_p_u2082_395_, 2);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_p_u2082_395_, 1);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_p_u2082_395_, 0);
lean_dec(v_unused_542_);
v___x_493_ = v_p_u2082_395_;
v_isShared_494_ = v_isSharedCheck_539_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_p_u2082_395_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_539_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_int_add(v_k_454_, v_k_457_);
lean_dec(v_k_457_);
lean_dec(v_k_454_);
v___x_496_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_495_, v_a_396_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_530_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_530_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_530_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_530_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
if (lean_obj_tag(v_a_497_) == 0)
{
lean_object* v___x_501_; lean_object* v___x_503_; 
lean_del_object(v___x_493_);
lean_dec_ref_known(v___x_462_, 3);
lean_dec_ref(v_p_459_);
lean_dec_ref(v_p_456_);
lean_dec(v_v_455_);
v___x_501_ = lean_box(0);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_object* v_val_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
lean_del_object(v___x_499_);
v_val_505_ = lean_ctor_get(v_a_497_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_a_497_, 1);
v___x_506_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0);
v___x_507_ = lean_int_dec_eq(v_val_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_456_, v_p_459_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v___x_462_, v_a_402_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
if (lean_obj_tag(v_a_509_) == 0)
{
lean_dec(v_val_505_);
lean_del_object(v___x_493_);
lean_dec(v_v_455_);
return v___x_508_;
}
else
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_527_; 
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v___x_508_, 0);
lean_dec(v_unused_528_);
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_527_;
goto v_resetjp_510_;
}
else
{
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_527_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_526_; 
v_val_513_ = lean_ctor_get(v_a_509_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_a_509_);
if (v_isSharedCheck_526_ == 0)
{
v___x_515_ = v_a_509_;
v_isShared_516_ = v_isSharedCheck_526_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_dec(v_a_509_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_526_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 2, v_val_513_);
lean_ctor_set(v___x_493_, 1, v_v_455_);
lean_ctor_set(v___x_493_, 0, v_val_505_);
v___x_518_ = v___x_493_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_val_505_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_v_455_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_val_513_);
v___x_518_ = v_reuseFailAlloc_525_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_518_);
v___x_520_ = v___x_515_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_520_);
v___x_522_ = v___x_511_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
}
else
{
lean_dec(v_val_505_);
lean_del_object(v___x_493_);
lean_dec(v_v_455_);
return v___x_508_;
}
}
else
{
lean_dec(v_val_505_);
lean_del_object(v___x_493_);
lean_dec(v_v_455_);
v_p_u2081_394_ = v_p_456_;
v_p_u2082_395_ = v_p_459_;
v_a_401_ = v___x_462_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_493_);
lean_dec_ref_known(v___x_462_, 3);
lean_dec_ref(v_p_459_);
lean_dec_ref(v_p_456_);
lean_dec(v_v_455_);
v_a_531_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_496_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_496_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
default: 
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_567_; 
lean_inc_ref(v_p_456_);
lean_inc(v_v_455_);
lean_inc(v_k_454_);
v_isSharedCheck_567_ = !lean_is_exclusive(v_p_u2081_394_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_568_ = lean_ctor_get(v_p_u2081_394_, 2);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_p_u2081_394_, 1);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_p_u2081_394_, 0);
lean_dec(v_unused_570_);
v___x_544_ = v_p_u2081_394_;
v_isShared_545_ = v_isSharedCheck_567_;
goto v_resetjp_543_;
}
else
{
lean_dec(v_p_u2081_394_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_567_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_456_, v_p_u2082_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v___x_462_, v_a_402_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
if (lean_obj_tag(v_a_547_) == 0)
{
lean_del_object(v___x_544_);
lean_dec(v_v_455_);
lean_dec(v_k_454_);
return v___x_546_;
}
else
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_565_; 
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v___x_546_, 0);
lean_dec(v_unused_566_);
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_565_;
goto v_resetjp_548_;
}
else
{
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_565_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v_val_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_564_; 
v_val_551_ = lean_ctor_get(v_a_547_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v_a_547_);
if (v_isSharedCheck_564_ == 0)
{
v___x_553_ = v_a_547_;
v_isShared_554_ = v_isSharedCheck_564_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_val_551_);
lean_dec(v_a_547_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_564_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 2, v_val_551_);
v___x_556_ = v___x_544_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_k_454_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_v_455_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_val_551_);
v___x_556_ = v_reuseFailAlloc_563_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_556_);
v___x_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_558_);
v___x_560_ = v___x_549_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_544_);
lean_dec(v_v_455_);
lean_dec(v_k_454_);
return v___x_546_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_394_ = stack[0].m_obj;
lean_object* v_p_u2082_395_ = stack[1].m_obj;
lean_object* v_a_396_ = stack[2].m_obj;
lean_object* v_a_397_ = stack[3].m_obj;
lean_object* v_a_398_ = stack[4].m_obj;
lean_object* v_a_399_ = stack[5].m_obj;
lean_object* v_a_400_ = stack[6].m_obj;
lean_object* v_a_401_ = stack[7].m_obj;
lean_object* v_a_402_ = stack[8].m_obj;
lean_object* v_res_576_;
v_res_576_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_394_, v_p_u2082_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___boxed(lean_object* v_p_u2081_577_, lean_object* v_p_u2082_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_577_, v_p_u2082_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec_ref(v_a_579_);
return v_res_587_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine(lean_object* v_p_u2081_588_, lean_object* v_p_u2082_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_598_; 
lean_inc_ref(v_a_595_);
v___x_598_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore(v_p_u2081_588_, v_p_u2082_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
if (lean_obj_tag(v_a_599_) == 0)
{
return v___x_598_;
}
else
{
lean_object* v_val_600_; lean_object* v___x_601_; 
lean_inc_ref(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v_val_600_ = lean_ctor_get(v_a_599_, 0);
v___x_601_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget(v_val_600_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_613_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_613_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
if (lean_obj_tag(v_a_602_) == 0)
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec_ref_known(v_a_599_, 1);
v___x_606_ = lean_box(0);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
lean_object* v___x_611_; 
lean_dec_ref_known(v_a_602_, 1);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_a_599_);
v___x_611_ = v___x_604_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_599_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref_known(v_a_599_, 1);
v_a_614_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_601_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_601_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
else
{
return v___x_598_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_combine_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_588_ = stack[0].m_obj;
lean_object* v_p_u2082_589_ = stack[1].m_obj;
lean_object* v_a_590_ = stack[2].m_obj;
lean_object* v_a_591_ = stack[3].m_obj;
lean_object* v_a_592_ = stack[4].m_obj;
lean_object* v_a_593_ = stack[5].m_obj;
lean_object* v_a_594_ = stack[6].m_obj;
lean_object* v_a_595_ = stack[7].m_obj;
lean_object* v_a_596_ = stack[8].m_obj;
lean_object* v_res_622_;
v_res_622_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_p_u2081_588_, v_p_u2082_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
stack->m_obj
 = v_res_622_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_combine___boxed(lean_object* v_p_u2081_623_, lean_object* v_p_u2082_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_p_u2081_623_, v_p_u2082_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec_ref(v_a_625_);
return v_res_633_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(lean_object* v_p_u2082_635_, lean_object* v_p_u2081_636_, lean_object* v_acc_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_toCold_646_; lean_object* v_currRecDepth_647_; lean_object* v_ref_648_; uint16_t v_optionFlags_649_; uint8_t v_suppressElabErrors_650_; uint8_t v_isRecordingDeps_651_; lean_object* v_maxRecDepth_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_toCold_646_ = lean_ctor_get(v_a_643_, 0);
lean_inc_ref(v_toCold_646_);
v_currRecDepth_647_ = lean_ctor_get(v_a_643_, 1);
lean_inc(v_currRecDepth_647_);
v_ref_648_ = lean_ctor_get(v_a_643_, 2);
lean_inc(v_ref_648_);
v_optionFlags_649_ = lean_ctor_get_uint16(v_a_643_, sizeof(void*)*3);
v_suppressElabErrors_650_ = lean_ctor_get_uint8(v_a_643_, sizeof(void*)*3 + 2);
v_isRecordingDeps_651_ = lean_ctor_get_uint8(v_a_643_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_643_);
v_maxRecDepth_681_ = lean_ctor_get(v_toCold_646_, 3);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_nat_dec_eq(v_maxRecDepth_681_, v___x_682_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; 
v___x_684_ = lean_nat_dec_eq(v_currRecDepth_647_, v_maxRecDepth_681_);
if (v___x_684_ == 0)
{
goto v___jp_652_;
}
else
{
lean_object* v___x_685_; 
lean_dec(v_currRecDepth_647_);
lean_dec_ref(v_toCold_646_);
lean_dec_ref(v_acc_637_);
lean_dec_ref(v_p_u2081_636_);
lean_dec_ref(v_p_u2082_635_);
v___x_685_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_648_);
return v___x_685_;
}
}
else
{
goto v___jp_652_;
}
v___jp_652_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v_currRecDepth_647_, v___x_653_);
lean_dec(v_currRecDepth_647_);
v___x_655_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_655_, 0, v_toCold_646_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
lean_ctor_set(v___x_655_, 2, v_ref_648_);
lean_ctor_set_uint16(v___x_655_, sizeof(void*)*3, v_optionFlags_649_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 2, v_suppressElabErrors_650_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 3, v_isRecordingDeps_651_);
if (lean_obj_tag(v_p_u2081_636_) == 0)
{
lean_object* v_k_656_; lean_object* v___x_657_; lean_object* v_a_658_; lean_object* v_val_659_; lean_object* v___x_660_; 
v_k_656_ = lean_ctor_get(v_p_u2081_636_, 0);
lean_inc(v_k_656_);
lean_dec_ref_known(v_p_u2081_636_, 1);
v___x_657_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v_k_656_, v_p_u2082_635_, v_a_638_);
lean_dec(v_k_656_);
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
v_val_659_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_val_659_);
lean_dec(v_a_658_);
v___x_660_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_acc_637_, v_val_659_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v___x_655_, v_a_644_);
lean_dec_ref_known(v___x_655_, 3);
return v___x_660_;
}
else
{
lean_object* v_k_661_; lean_object* v_v_662_; lean_object* v_p_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_k_661_ = lean_ctor_get(v_p_u2081_636_, 0);
lean_inc(v_k_661_);
v_v_662_ = lean_ctor_get(v_p_u2081_636_, 1);
lean_inc(v_v_662_);
v_p_663_ = lean_ctor_get(v_p_u2081_636_, 2);
lean_inc_ref(v_p_663_);
lean_dec_ref_known(v_p_u2081_636_, 3);
v___x_664_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___closed__0));
v___x_665_ = l_Lean_Core_checkSystem(v___x_664_, v___x_655_, v_a_644_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; lean_object* v_a_667_; lean_object* v_val_668_; lean_object* v___x_669_; 
lean_dec_ref_known(v___x_665_, 1);
lean_inc_ref(v_p_u2082_635_);
v___x_666_ = l_Lean_Meta_Sym_Arith_SafePoly_mulMon___redArg(v_k_661_, v_v_662_, v_p_u2082_635_, v_a_638_);
lean_dec(v_k_661_);
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v_val_668_ = lean_ctor_get(v_a_667_, 0);
lean_inc(v_val_668_);
lean_dec(v_a_667_);
v___x_669_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_acc_637_, v_val_668_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v___x_655_, v_a_644_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
if (lean_obj_tag(v_a_670_) == 0)
{
lean_dec_ref(v_p_663_);
lean_dec_ref_known(v___x_655_, 3);
lean_dec_ref(v_p_u2082_635_);
return v___x_669_;
}
else
{
lean_object* v_val_671_; 
lean_inc_ref(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v_val_671_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_a_670_, 1);
v_p_u2081_636_ = v_p_663_;
v_acc_637_ = v_val_671_;
v_a_643_ = v___x_655_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_663_);
lean_dec_ref_known(v___x_655_, 3);
lean_dec_ref(v_p_u2082_635_);
return v___x_669_;
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_p_663_);
lean_dec(v_v_662_);
lean_dec(v_k_661_);
lean_dec_ref_known(v___x_655_, 3);
lean_dec_ref(v_acc_637_);
lean_dec_ref(v_p_u2082_635_);
v_a_673_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_665_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_665_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2082_635_ = stack[0].m_obj;
lean_object* v_p_u2081_636_ = stack[1].m_obj;
lean_object* v_acc_637_ = stack[2].m_obj;
lean_object* v_a_638_ = stack[3].m_obj;
lean_object* v_a_639_ = stack[4].m_obj;
lean_object* v_a_640_ = stack[5].m_obj;
lean_object* v_a_641_ = stack[6].m_obj;
lean_object* v_a_642_ = stack[7].m_obj;
lean_object* v_a_643_ = stack[8].m_obj;
lean_object* v_a_644_ = stack[9].m_obj;
lean_object* v_res_686_;
v_res_686_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(v_p_u2082_635_, v_p_u2081_636_, v_acc_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
stack->m_obj
 = v_res_686_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go___boxed(lean_object* v_p_u2082_687_, lean_object* v_p_u2081_688_, lean_object* v_acc_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(v_p_u2082_687_, v_p_u2081_688_, v_acc_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec_ref(v_a_690_);
return v_res_698_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore___closed__0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul(lean_object* v_p_u2081_701_, lean_object* v_p_u2082_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0, &l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0);
lean_inc_ref(v_a_708_);
v___x_712_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mul_go(v_p_u2082_702_, v_p_u2081_701_, v___x_711_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
return v___x_712_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_mul_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_701_ = stack[0].m_obj;
lean_object* v_p_u2082_702_ = stack[1].m_obj;
lean_object* v_a_703_ = stack[2].m_obj;
lean_object* v_a_704_ = stack[3].m_obj;
lean_object* v_a_705_ = stack[4].m_obj;
lean_object* v_a_706_ = stack[5].m_obj;
lean_object* v_a_707_ = stack[6].m_obj;
lean_object* v_a_708_ = stack[7].m_obj;
lean_object* v_a_709_ = stack[8].m_obj;
lean_object* v_res_713_;
v_res_713_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_u2081_701_, v_p_u2082_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_mul___boxed(lean_object* v_p_u2081_714_, lean_object* v_p_u2082_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_u2081_714_, v_p_u2082_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec_ref(v_a_716_);
return v_res_724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_to_int(v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__1);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(lean_object* v_p_731_, lean_object* v_k_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_toCold_741_; lean_object* v_currRecDepth_742_; lean_object* v_ref_743_; uint16_t v_optionFlags_744_; uint8_t v_suppressElabErrors_745_; uint8_t v_isRecordingDeps_746_; lean_object* v_maxRecDepth_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_toCold_741_ = lean_ctor_get(v_a_738_, 0);
v_currRecDepth_742_ = lean_ctor_get(v_a_738_, 1);
v_ref_743_ = lean_ctor_get(v_a_738_, 2);
v_optionFlags_744_ = lean_ctor_get_uint16(v_a_738_, sizeof(void*)*3);
v_suppressElabErrors_745_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*3 + 2);
v_isRecordingDeps_746_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*3 + 3);
v_maxRecDepth_769_ = lean_ctor_get(v_toCold_741_, 3);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_nat_dec_eq(v_maxRecDepth_769_, v___x_770_);
if (v___x_771_ == 0)
{
uint8_t v___x_772_; 
v___x_772_ = lean_nat_dec_eq(v_currRecDepth_742_, v_maxRecDepth_769_);
if (v___x_772_ == 0)
{
goto v___jp_747_;
}
else
{
lean_object* v___x_773_; 
lean_dec_ref(v_p_731_);
lean_inc(v_ref_743_);
v___x_773_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_743_);
return v___x_773_;
}
}
else
{
goto v___jp_747_;
}
v___jp_747_:
{
lean_object* v_zero_748_; uint8_t v_isZero_749_; 
v_zero_748_ = lean_unsigned_to_nat(0u);
v_isZero_749_ = lean_nat_dec_eq(v_k_732_, v_zero_748_);
if (v_isZero_749_ == 1)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref(v_p_731_);
v___x_750_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
else
{
lean_object* v_one_752_; lean_object* v_n_753_; uint8_t v_isZero_754_; 
v_one_752_ = lean_unsigned_to_nat(1u);
v_n_753_ = lean_nat_sub(v_k_732_, v_one_752_);
v_isZero_754_ = lean_nat_dec_eq(v_n_753_, v_zero_748_);
if (v_isZero_754_ == 1)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec(v_n_753_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_p_731_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
else
{
lean_object* v_n_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v_isZero_760_; 
v_n_757_ = lean_nat_sub(v_n_753_, v_one_752_);
lean_dec(v_n_753_);
v___x_758_ = lean_nat_add(v_currRecDepth_742_, v_one_752_);
lean_inc(v_ref_743_);
lean_inc_ref(v_toCold_741_);
v___x_759_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_759_, 0, v_toCold_741_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
lean_ctor_set(v___x_759_, 2, v_ref_743_);
lean_ctor_set_uint16(v___x_759_, sizeof(void*)*3, v_optionFlags_744_);
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*3 + 2, v_suppressElabErrors_745_);
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*3 + 3, v_isRecordingDeps_746_);
v_isZero_760_ = lean_nat_dec_eq(v_n_757_, v_zero_748_);
if (v_isZero_760_ == 1)
{
lean_object* v___x_761_; 
lean_dec(v_n_757_);
lean_inc_ref(v_p_731_);
v___x_761_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_731_, v_p_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v___x_759_, v_a_739_);
lean_dec_ref_known(v___x_759_, 3);
return v___x_761_;
}
else
{
lean_object* v_n_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_n_762_ = lean_nat_sub(v_n_757_, v_one_752_);
lean_dec(v_n_757_);
v___x_763_ = lean_unsigned_to_nat(2u);
v___x_764_ = lean_nat_add(v_n_762_, v___x_763_);
lean_dec(v_n_762_);
lean_inc_ref(v_p_731_);
v___x_765_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_731_, v___x_764_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v___x_759_, v_a_739_);
lean_dec(v___x_764_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
if (lean_obj_tag(v_a_766_) == 0)
{
lean_dec_ref_known(v___x_759_, 3);
lean_dec_ref(v_p_731_);
return v___x_765_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_768_; 
lean_inc_ref(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v_val_767_ = lean_ctor_get(v_a_766_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v_a_766_, 1);
v___x_768_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_p_731_, v_val_767_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v___x_759_, v_a_739_);
lean_dec_ref_known(v___x_759_, 3);
return v___x_768_;
}
}
else
{
lean_dec_ref_known(v___x_759_, 3);
lean_dec_ref(v_p_731_);
return v___x_765_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_731_ = stack[0].m_obj;
lean_object* v_k_732_ = stack[1].m_obj;
lean_object* v_a_733_ = stack[2].m_obj;
lean_object* v_a_734_ = stack[3].m_obj;
lean_object* v_a_735_ = stack[4].m_obj;
lean_object* v_a_736_ = stack[5].m_obj;
lean_object* v_a_737_ = stack[6].m_obj;
lean_object* v_a_738_ = stack[7].m_obj;
lean_object* v_a_739_ = stack[8].m_obj;
lean_object* v_res_774_;
v_res_774_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_731_, v_k_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___boxed(lean_object* v_p_775_, lean_object* v_k_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_775_, v_k_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_k_776_);
return v_res_785_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(lean_object* v_p_786_, lean_object* v_k_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_toCold_796_; lean_object* v_currRecDepth_797_; lean_object* v_ref_798_; uint16_t v_optionFlags_799_; uint8_t v_suppressElabErrors_800_; uint8_t v_isRecordingDeps_801_; lean_object* v_maxRecDepth_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_toCold_796_ = lean_ctor_get(v_a_793_, 0);
v_currRecDepth_797_ = lean_ctor_get(v_a_793_, 1);
v_ref_798_ = lean_ctor_get(v_a_793_, 2);
v_optionFlags_799_ = lean_ctor_get_uint16(v_a_793_, sizeof(void*)*3);
v_suppressElabErrors_800_ = lean_ctor_get_uint8(v_a_793_, sizeof(void*)*3 + 2);
v_isRecordingDeps_801_ = lean_ctor_get_uint8(v_a_793_, sizeof(void*)*3 + 3);
v_maxRecDepth_820_ = lean_ctor_get(v_toCold_796_, 3);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_nat_dec_eq(v_maxRecDepth_820_, v___x_821_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_eq(v_currRecDepth_797_, v_maxRecDepth_820_);
if (v___x_823_ == 0)
{
goto v___jp_802_;
}
else
{
lean_object* v___x_824_; 
lean_dec_ref(v_p_786_);
lean_inc(v_ref_798_);
v___x_824_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_combineCore_spec__0___redArg(v_ref_798_);
return v___x_824_;
}
}
else
{
goto v___jp_802_;
}
v___jp_802_:
{
lean_object* v_zero_803_; uint8_t v_isZero_804_; 
v_zero_803_ = lean_unsigned_to_nat(0u);
v_isZero_804_ = lean_nat_dec_eq(v_k_787_, v_zero_803_);
if (v_isZero_804_ == 1)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_p_786_);
v___x_805_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
else
{
lean_object* v_one_807_; lean_object* v_n_808_; uint8_t v_isZero_809_; 
v_one_807_ = lean_unsigned_to_nat(1u);
v_n_808_ = lean_nat_sub(v_k_787_, v_one_807_);
v_isZero_809_ = lean_nat_dec_eq(v_n_808_, v_zero_803_);
if (v_isZero_809_ == 1)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_n_808_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v_p_786_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
else
{
lean_object* v_n_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_n_812_ = lean_nat_sub(v_n_808_, v_one_807_);
lean_dec(v_n_808_);
v___x_813_ = lean_nat_add(v_currRecDepth_797_, v_one_807_);
lean_inc(v_ref_798_);
lean_inc_ref(v_toCold_796_);
v___x_814_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_814_, 0, v_toCold_796_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
lean_ctor_set(v___x_814_, 2, v_ref_798_);
lean_ctor_set_uint16(v___x_814_, sizeof(void*)*3, v_optionFlags_799_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*3 + 2, v_suppressElabErrors_800_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*3 + 3, v_isRecordingDeps_801_);
v___x_815_ = lean_nat_add(v_n_812_, v_one_807_);
lean_dec(v_n_812_);
lean_inc_ref(v_p_786_);
v___x_816_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_786_, v___x_815_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v___x_814_, v_a_794_);
lean_dec(v___x_815_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
if (lean_obj_tag(v_a_817_) == 0)
{
lean_dec_ref_known(v___x_814_, 3);
lean_dec_ref(v_p_786_);
return v___x_816_;
}
else
{
lean_object* v_val_818_; lean_object* v___x_819_; 
lean_inc_ref(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v_val_818_ = lean_ctor_get(v_a_817_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v_a_817_, 1);
v___x_819_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_818_, v_p_786_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v___x_814_, v_a_794_);
lean_dec_ref_known(v___x_814_, 3);
return v___x_819_;
}
}
else
{
lean_dec_ref_known(v___x_814_, 3);
lean_dec_ref(v_p_786_);
return v___x_816_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_786_ = stack[0].m_obj;
lean_object* v_k_787_ = stack[1].m_obj;
lean_object* v_a_788_ = stack[2].m_obj;
lean_object* v_a_789_ = stack[3].m_obj;
lean_object* v_a_790_ = stack[4].m_obj;
lean_object* v_a_791_ = stack[5].m_obj;
lean_object* v_a_792_ = stack[6].m_obj;
lean_object* v_a_793_ = stack[7].m_obj;
lean_object* v_a_794_ = stack[8].m_obj;
lean_object* v_res_825_;
v_res_825_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_786_, v_k_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC___boxed(lean_object* v_p_826_, lean_object* v_k_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_826_, v_k_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_k_827_);
return v_res_836_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_SafePoly_pow(lean_object* v_p_837_, lean_object* v_k_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
uint8_t v_commutative_847_; 
v_commutative_847_ = lean_ctor_get_uint8(v_a_839_, sizeof(void*)*3 + 1);
if (v_commutative_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powNC(v_p_837_, v_k_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm(v_p_837_, v_k_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_849_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_SafePoly_pow_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_837_ = stack[0].m_obj;
lean_object* v_k_838_ = stack[1].m_obj;
lean_object* v_a_839_ = stack[2].m_obj;
lean_object* v_a_840_ = stack[3].m_obj;
lean_object* v_a_841_ = stack[4].m_obj;
lean_object* v_a_842_ = stack[5].m_obj;
lean_object* v_a_843_ = stack[6].m_obj;
lean_object* v_a_844_ = stack[7].m_obj;
lean_object* v_a_845_ = stack[8].m_obj;
lean_object* v_res_850_;
v_res_850_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_p_837_, v_k_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_SafePoly_pow___boxed(lean_object* v_p_851_, lean_object* v_k_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_p_851_, v_k_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_k_852_);
return v_res_861_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg(lean_object* v_k_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v___x_870_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_862_ = stack[0].m_obj;
lean_object* v_a_863_ = stack[1].m_obj;
lean_object* v_a_864_ = stack[2].m_obj;
lean_object* v_a_865_ = stack[3].m_obj;
lean_object* v_a_866_ = stack[4].m_obj;
lean_object* v_a_867_ = stack[5].m_obj;
lean_object* v_a_868_ = stack[6].m_obj;
lean_object* v_res_871_;
v_res_871_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg(v_k_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
stack->m_obj
 = v_res_871_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg___boxed(lean_object* v_k_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___redArg(v_k_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
return v_res_880_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27(lean_object* v_k_881_, lean_object* v_x_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_881_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
return v___x_890_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_881_ = stack[0].m_obj;
lean_object* v_x_882_ = stack[1].m_obj;
lean_object* v_a_883_ = stack[2].m_obj;
lean_object* v_a_884_ = stack[3].m_obj;
lean_object* v_a_885_ = stack[4].m_obj;
lean_object* v_a_886_ = stack[5].m_obj;
lean_object* v_a_887_ = stack[6].m_obj;
lean_object* v_a_888_ = stack[7].m_obj;
lean_object* v_res_891_;
v_res_891_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27(v_k_881_, v_x_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27___boxed(lean_object* v_k_892_, lean_object* v_x_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkExp_x27(v_k_892_, v_x_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec_ref(v_x_893_);
return v_res_901_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(lean_object* v_x_902_, lean_object* v_k_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_maxDegree_x3f_922_; 
v_maxDegree_x3f_922_ = lean_ctor_get(v_a_904_, 2);
if (lean_obj_tag(v_maxDegree_x3f_922_) == 1)
{
lean_object* v_val_923_; uint8_t v___x_924_; 
v_val_923_ = lean_ctor_get(v_maxDegree_x3f_922_, 0);
v___x_924_ = lean_nat_dec_lt(v_val_923_, v_k_903_);
if (v___x_924_ == 0)
{
goto v___jp_912_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_x_902_);
v___x_925_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__2);
v___x_926_ = l_Nat_reprFast(v_k_903_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = l_Lean_MessageData_ofFormat(v___x_927_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_925_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__4);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
lean_inc(v_val_923_);
v___x_932_ = l_Nat_reprFast(v_val_923_);
v___x_933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
v___x_934_ = l_Lean_MessageData_ofFormat(v___x_933_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_931_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_checkBudget___closed__6);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_905_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; uint8_t v_verbose_940_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v_verbose_940_ = lean_ctor_get_uint8(v_a_939_, 0);
lean_dec(v_a_939_);
if (v_verbose_940_ == 0)
{
lean_dec_ref_known(v___x_937_, 2);
goto v___jp_919_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Meta_Sym_reportIssue(v___x_937_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_dec_ref_known(v___x_941_, 1);
goto v___jp_919_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
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
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref_known(v___x_937_, 2);
v_a_950_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_938_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_938_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
else
{
goto v___jp_912_;
}
v___jp_912_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_x_902_);
lean_ctor_set(v___x_913_, 1, v_k_903_);
v___x_914_ = lean_box(0);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_915_);
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
v___jp_919_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_box(0);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_902_ = stack[0].m_obj;
lean_object* v_k_903_ = stack[1].m_obj;
lean_object* v_a_904_ = stack[2].m_obj;
lean_object* v_a_905_ = stack[3].m_obj;
lean_object* v_a_906_ = stack[4].m_obj;
lean_object* v_a_907_ = stack[5].m_obj;
lean_object* v_a_908_ = stack[6].m_obj;
lean_object* v_a_909_ = stack[7].m_obj;
lean_object* v_a_910_ = stack[8].m_obj;
lean_object* v_res_958_;
v_res_958_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_x_902_, v_k_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar___boxed(lean_object* v_x_959_, lean_object* v_k_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_x_959_, v_k_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec_ref(v_a_961_);
return v_res_969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0);
v___x_971_ = lean_int_neg(v___x_970_);
return v___x_971_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(lean_object* v_e_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_n_982_; lean_object* v___y_983_; 
switch(lean_obj_tag(v_e_972_))
{
case 1:
{
lean_object* v_k_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1051_; 
v_k_1014_ = lean_ctor_get(v_e_972_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_e_972_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1016_ = v_e_972_;
v_isShared_1017_ = v_isSharedCheck_1051_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_k_1014_);
lean_dec(v_e_972_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1051_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_nat_to_int(v_k_1014_);
v___x_1019_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1018_, v_a_973_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1042_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1042_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1042_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
if (lean_obj_tag(v_a_1020_) == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
lean_del_object(v___x_1016_);
v___x_1024_ = lean_box(0);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
else
{
lean_object* v_val_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1041_; 
v_val_1028_ = lean_ctor_get(v_a_1020_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_a_1020_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1030_ = v_a_1020_;
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_val_1028_);
lean_dec(v_a_1020_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 0);
lean_ctor_set(v___x_1016_, 0, v_val_1028_);
v___x_1033_ = v___x_1016_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_val_1028_);
v___x_1033_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1033_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1035_);
v___x_1037_ = v___x_1022_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_del_object(v___x_1016_);
v_a_1043_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1019_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1019_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
case 3:
{
lean_object* v_i_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1061_; 
v_i_1052_ = lean_ctor_get(v_e_972_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_e_972_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1054_ = v_e_972_;
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_i_1052_);
lean_dec(v_e_972_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
case 4:
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_a_1062_ = lean_ctor_get(v_e_972_, 0);
lean_inc_ref(v_a_1062_);
lean_dec_ref_known(v_e_972_, 1);
v___x_1063_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1062_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
if (lean_obj_tag(v_a_1064_) == 0)
{
return v___x_1063_;
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_inc_ref(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v_val_1065_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v_a_1064_, 1);
v___x_1066_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0);
v___x_1067_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v___x_1066_, v_val_1065_, v_a_973_);
return v___x_1067_;
}
}
else
{
return v___x_1063_;
}
}
case 5:
{
lean_object* v_a_1068_; lean_object* v_b_1069_; lean_object* v___x_1070_; 
v_a_1068_ = lean_ctor_get(v_e_972_, 0);
lean_inc_ref(v_a_1068_);
v_b_1069_ = lean_ctor_get(v_e_972_, 1);
lean_inc_ref(v_b_1069_);
lean_dec_ref_known(v_e_972_, 2);
v___x_1070_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1068_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
if (lean_obj_tag(v_a_1071_) == 0)
{
lean_dec_ref(v_b_1069_);
return v___x_1070_;
}
else
{
lean_object* v_val_1072_; lean_object* v___x_1073_; 
lean_inc_ref(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v_val_1072_ = lean_ctor_get(v_a_1071_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v_a_1071_, 1);
v___x_1073_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1069_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
if (lean_obj_tag(v_a_1074_) == 0)
{
lean_dec(v_val_1072_);
return v___x_1073_;
}
else
{
lean_object* v_val_1075_; lean_object* v___x_1076_; 
lean_inc_ref(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_val_1075_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v_a_1074_, 1);
v___x_1076_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1072_, v_val_1075_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_1076_;
}
}
else
{
lean_dec(v_val_1072_);
return v___x_1073_;
}
}
}
else
{
lean_dec_ref(v_b_1069_);
return v___x_1070_;
}
}
case 6:
{
lean_object* v_a_1077_; lean_object* v_b_1078_; lean_object* v___x_1079_; 
v_a_1077_ = lean_ctor_get(v_e_972_, 0);
lean_inc_ref(v_a_1077_);
v_b_1078_ = lean_ctor_get(v_e_972_, 1);
lean_inc_ref(v_b_1078_);
lean_dec_ref_known(v_e_972_, 2);
v___x_1079_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1077_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
if (lean_obj_tag(v_a_1080_) == 0)
{
lean_dec_ref(v_b_1078_);
return v___x_1079_;
}
else
{
lean_object* v_val_1081_; lean_object* v___x_1082_; 
lean_inc_ref(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v_val_1081_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v_a_1080_, 1);
v___x_1082_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1078_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
if (lean_obj_tag(v_a_1083_) == 0)
{
lean_dec(v_val_1081_);
return v___x_1082_;
}
else
{
lean_object* v_val_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_inc_ref(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v_val_1084_ = lean_ctor_get(v_a_1083_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_a_1083_, 1);
v___x_1085_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0);
v___x_1086_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v___x_1085_, v_val_1084_, v_a_973_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
if (lean_obj_tag(v_a_1087_) == 0)
{
lean_dec(v_val_1081_);
return v___x_1086_;
}
else
{
lean_object* v_val_1088_; lean_object* v___x_1089_; 
lean_inc_ref(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v_val_1088_ = lean_ctor_get(v_a_1087_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_a_1087_, 1);
v___x_1089_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1081_, v_val_1088_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_1089_;
}
}
else
{
lean_dec(v_val_1081_);
return v___x_1086_;
}
}
}
else
{
lean_dec(v_val_1081_);
return v___x_1082_;
}
}
}
else
{
lean_dec_ref(v_b_1078_);
return v___x_1079_;
}
}
case 7:
{
lean_object* v_a_1090_; lean_object* v_b_1091_; lean_object* v___x_1092_; 
v_a_1090_ = lean_ctor_get(v_e_972_, 0);
lean_inc_ref(v_a_1090_);
v_b_1091_ = lean_ctor_get(v_e_972_, 1);
lean_inc_ref(v_b_1091_);
lean_dec_ref_known(v_e_972_, 2);
v___x_1092_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1090_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
if (lean_obj_tag(v_a_1093_) == 0)
{
lean_dec_ref(v_b_1091_);
return v___x_1092_;
}
else
{
lean_object* v_val_1094_; lean_object* v___x_1095_; 
lean_inc_ref(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v_val_1094_ = lean_ctor_get(v_a_1093_, 0);
lean_inc(v_val_1094_);
lean_dec_ref_known(v_a_1093_, 1);
v___x_1095_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1091_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
if (lean_obj_tag(v_a_1096_) == 0)
{
lean_dec(v_val_1094_);
return v___x_1095_;
}
else
{
lean_object* v_val_1097_; lean_object* v___x_1098_; 
lean_inc_ref(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v_val_1097_ = lean_ctor_get(v_a_1096_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v_a_1096_, 1);
v___x_1098_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_1094_, v_val_1097_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_1098_;
}
}
else
{
lean_dec(v_val_1094_);
return v___x_1095_;
}
}
}
else
{
lean_dec_ref(v_b_1091_);
return v___x_1092_;
}
}
case 8:
{
lean_object* v_a_1099_; lean_object* v_k_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_a_1099_ = lean_ctor_get(v_e_972_, 0);
lean_inc_ref(v_a_1099_);
v_k_1100_ = lean_ctor_get(v_e_972_, 1);
lean_inc(v_k_1100_);
lean_dec_ref_known(v_e_972_, 2);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_nat_dec_eq(v_k_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
switch(lean_obj_tag(v_a_1099_))
{
case 0:
{
lean_object* v_k_1103_; lean_object* v___x_1104_; 
v_k_1103_ = lean_ctor_get(v_a_1099_, 0);
lean_inc(v_k_1103_);
lean_dec_ref_known(v_a_1099_, 1);
lean_inc(v_k_1100_);
v___x_1104_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1100_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1151_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1151_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1151_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
if (lean_obj_tag(v_a_1105_) == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_dec(v_k_1103_);
lean_dec(v_k_1100_);
v___x_1109_ = lean_box(0);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
else
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1149_; 
lean_del_object(v___x_1107_);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_a_1105_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v_a_1105_, 0);
lean_dec(v_unused_1150_);
v___x_1114_ = v_a_1105_;
v_isShared_1115_ = v_isSharedCheck_1149_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v_a_1105_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1149_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = l_Int_pow(v_k_1103_, v_k_1100_);
lean_dec(v_k_1100_);
lean_dec(v_k_1103_);
v___x_1117_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1116_, v_a_973_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1140_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1140_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1140_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
if (lean_obj_tag(v_a_1118_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_del_object(v___x_1114_);
v___x_1122_ = lean_box(0);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1139_; 
v_val_1126_ = lean_ctor_get(v_a_1118_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_a_1118_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1128_ = v_a_1118_;
v_isShared_1129_ = v_isSharedCheck_1139_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_val_1126_);
lean_dec(v_a_1118_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1139_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 0);
lean_ctor_set(v___x_1114_, 0, v_val_1126_);
v___x_1131_ = v___x_1114_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_val_1126_);
v___x_1131_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1135_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1133_);
v___x_1135_ = v___x_1120_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_del_object(v___x_1114_);
v_a_1141_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1117_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1117_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_k_1103_);
lean_dec(v_k_1100_);
v_a_1152_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1104_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1104_);
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
case 3:
{
lean_object* v_i_1160_; lean_object* v___x_1161_; 
v_i_1160_ = lean_ctor_get(v_a_1099_, 0);
lean_inc(v_i_1160_);
lean_dec_ref_known(v_a_1099_, 1);
v___x_1161_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1160_, v_k_1100_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_1161_;
}
default: 
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1099_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
if (lean_obj_tag(v_a_1163_) == 0)
{
lean_dec(v_k_1100_);
return v___x_1162_;
}
else
{
lean_object* v_val_1164_; lean_object* v___x_1165_; 
lean_inc_ref(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v_val_1164_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_val_1164_);
lean_dec_ref_known(v_a_1163_, 1);
v___x_1165_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_val_1164_, v_k_1100_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_k_1100_);
return v___x_1165_;
}
}
else
{
lean_dec(v_k_1100_);
return v___x_1162_;
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec(v_k_1100_);
lean_dec_ref(v_a_1099_);
v___x_1166_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
default: 
{
lean_object* v_k_1168_; 
v_k_1168_ = lean_ctor_get(v_e_972_, 0);
lean_inc(v_k_1168_);
lean_dec_ref(v_e_972_);
v_n_982_ = v_k_1168_;
v___y_983_ = v_a_973_;
goto v___jp_981_;
}
}
v___jp_981_:
{
lean_object* v___x_984_; 
v___x_984_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_n_982_, v___y_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1005_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_1005_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1005_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
if (lean_obj_tag(v_a_985_) == 0)
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
lean_object* v_val_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1004_; 
v_val_993_ = lean_ctor_get(v_a_985_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_985_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_995_ = v_a_985_;
v_isShared_996_ = v_isSharedCheck_1004_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_val_993_);
lean_dec(v_a_985_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1004_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v_val_993_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_999_ = v___x_995_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_999_);
v___x_1001_ = v___x_987_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_984_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_984_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_972_ = stack[0].m_obj;
lean_object* v_a_973_ = stack[1].m_obj;
lean_object* v_a_974_ = stack[2].m_obj;
lean_object* v_a_975_ = stack[3].m_obj;
lean_object* v_a_976_ = stack[4].m_obj;
lean_object* v_a_977_ = stack[5].m_obj;
lean_object* v_a_978_ = stack[6].m_obj;
lean_object* v_a_979_ = stack[7].m_obj;
lean_object* v_res_1169_;
v_res_1169_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
stack->m_obj
 = v_res_1169_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___boxed(lean_object* v_e_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0, &l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0);
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(lean_object* v_e_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
switch(lean_obj_tag(v_e_1182_))
{
case 0:
{
lean_object* v_k_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1202_; 
v_k_1191_ = lean_ctor_get(v_e_1182_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_e_1182_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1193_ = v_e_1182_;
v_isShared_1194_ = v_isSharedCheck_1202_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_k_1191_);
lean_dec(v_e_1182_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1202_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_nat_abs(v_k_1191_);
lean_dec(v_k_1191_);
v___x_1196_ = lean_nat_to_int(v___x_1195_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
}
case 1:
{
lean_object* v_k_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1213_; 
v_k_1203_ = lean_ctor_get(v_e_1182_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_e_1182_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1205_ = v_e_1182_;
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_k_1203_);
lean_dec(v_e_1182_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_nat_to_int(v_k_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1207_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
}
case 3:
{
lean_object* v_i_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1223_; 
v_i_1214_ = lean_ctor_get(v_e_1182_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_e_1182_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1216_ = v_e_1182_;
v_isShared_1217_ = v_isSharedCheck_1223_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_i_1214_);
lean_dec(v_e_1182_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1223_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_1214_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 1);
lean_ctor_set(v___x_1216_, 0, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
case 5:
{
lean_object* v_a_1224_; lean_object* v_b_1225_; lean_object* v___x_1226_; 
v_a_1224_ = lean_ctor_get(v_e_1182_, 0);
lean_inc_ref(v_a_1224_);
v_b_1225_ = lean_ctor_get(v_e_1182_, 1);
lean_inc_ref(v_b_1225_);
lean_dec_ref_known(v_e_1182_, 2);
v___x_1226_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1224_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
if (lean_obj_tag(v_a_1227_) == 0)
{
lean_dec_ref(v_b_1225_);
return v___x_1226_;
}
else
{
lean_object* v_val_1228_; lean_object* v___x_1229_; 
lean_inc_ref(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v_val_1228_ = lean_ctor_get(v_a_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v_a_1227_, 1);
v___x_1229_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_b_1225_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
if (lean_obj_tag(v_a_1230_) == 0)
{
lean_dec(v_val_1228_);
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
v___x_1232_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1228_, v_val_1231_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v___x_1232_;
}
}
else
{
lean_dec(v_val_1228_);
return v___x_1229_;
}
}
}
else
{
lean_dec_ref(v_b_1225_);
return v___x_1226_;
}
}
case 7:
{
lean_object* v_a_1233_; lean_object* v_b_1234_; lean_object* v___x_1235_; 
v_a_1233_ = lean_ctor_get(v_e_1182_, 0);
lean_inc_ref(v_a_1233_);
v_b_1234_ = lean_ctor_get(v_e_1182_, 1);
lean_inc_ref(v_b_1234_);
lean_dec_ref_known(v_e_1182_, 2);
v___x_1235_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1233_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
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
v___x_1238_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_b_1234_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
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
v___x_1241_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_1237_, v_val_1240_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
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
v_a_1242_ = lean_ctor_get(v_e_1182_, 0);
lean_inc_ref(v_a_1242_);
v_k_1243_ = lean_ctor_get(v_e_1182_, 1);
lean_inc(v_k_1243_);
lean_dec_ref_known(v_e_1182_, 2);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_nat_dec_eq(v_k_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
switch(lean_obj_tag(v_a_1242_))
{
case 0:
{
lean_object* v_k_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1285_; 
v_k_1246_ = lean_ctor_get(v_a_1242_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_a_1242_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1248_ = v_a_1242_;
v_isShared_1249_ = v_isSharedCheck_1285_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_k_1246_);
lean_dec(v_a_1242_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1285_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; 
lean_inc(v_k_1243_);
v___x_1250_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1243_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1276_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1276_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1276_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
if (lean_obj_tag(v_a_1251_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
lean_del_object(v___x_1248_);
lean_dec(v_k_1246_);
lean_dec(v_k_1243_);
v___x_1255_ = lean_box(0);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1255_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
else
{
lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1274_; 
v_isSharedCheck_1274_ = !lean_is_exclusive(v_a_1251_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v_a_1251_, 0);
lean_dec(v_unused_1275_);
v___x_1260_ = v_a_1251_;
v_isShared_1261_ = v_isSharedCheck_1274_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v_a_1251_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1274_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1262_ = lean_nat_abs(v_k_1246_);
lean_dec(v_k_1246_);
v___x_1263_ = lean_nat_to_int(v___x_1262_);
v___x_1264_ = l_Int_pow(v___x_1263_, v_k_1243_);
lean_dec(v_k_1243_);
lean_dec(v___x_1263_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1264_);
v___x_1266_ = v___x_1248_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1266_);
v___x_1268_ = v___x_1260_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1268_);
v___x_1270_ = v___x_1253_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_del_object(v___x_1248_);
lean_dec(v_k_1246_);
lean_dec(v_k_1243_);
v_a_1277_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1250_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1250_);
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
case 3:
{
lean_object* v_i_1286_; lean_object* v___x_1287_; 
v_i_1286_ = lean_ctor_get(v_a_1242_, 0);
lean_inc(v_i_1286_);
lean_dec_ref_known(v_a_1242_, 1);
v___x_1287_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1286_, v_k_1243_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v___x_1287_;
}
default: 
{
lean_object* v___x_1288_; 
v___x_1288_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1242_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
if (lean_obj_tag(v_a_1289_) == 0)
{
lean_dec(v_k_1243_);
return v___x_1288_;
}
else
{
lean_object* v_val_1290_; lean_object* v___x_1291_; 
lean_inc_ref(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v_val_1290_ = lean_ctor_get(v_a_1289_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v_a_1289_, 1);
v___x_1291_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_val_1290_, v_k_1243_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
lean_dec(v_k_1243_);
return v___x_1291_;
}
}
else
{
lean_dec(v_k_1243_);
return v___x_1288_;
}
}
}
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec(v_k_1243_);
lean_dec_ref(v_a_1242_);
v___x_1292_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
return v___x_1293_;
}
}
default: 
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v_e_1182_);
v___x_1294_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1182_ = stack[0].m_obj;
lean_object* v_a_1183_ = stack[1].m_obj;
lean_object* v_a_1184_ = stack[2].m_obj;
lean_object* v_a_1185_ = stack[3].m_obj;
lean_object* v_a_1186_ = stack[4].m_obj;
lean_object* v_a_1187_ = stack[5].m_obj;
lean_object* v_a_1188_ = stack[6].m_obj;
lean_object* v_a_1189_ = stack[7].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___boxed(lean_object* v_e_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_a_1298_);
return v_res_1306_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f(lean_object* v_e_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v_semiring_1316_; 
v_semiring_1316_ = lean_ctor_get_uint8(v_a_1308_, sizeof(void*)*3);
if (v_semiring_1316_ == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1318_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_toPoly_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1307_ = stack[0].m_obj;
lean_object* v_a_1308_ = stack[1].m_obj;
lean_object* v_a_1309_ = stack[2].m_obj;
lean_object* v_a_1310_ = stack[3].m_obj;
lean_object* v_a_1311_ = stack[4].m_obj;
lean_object* v_a_1312_ = stack[5].m_obj;
lean_object* v_a_1313_ = stack[6].m_obj;
lean_object* v_a_1314_ = stack[7].m_obj;
lean_object* v_res_1319_;
v_res_1319_ = l_Lean_Meta_Sym_Arith_toPoly_x3f(v_e_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
stack->m_obj
 = v_res_1319_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f___boxed(lean_object* v_e_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Meta_Sym_Arith_toPoly_x3f(v_e_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec_ref(v_a_1321_);
return v_res_1329_;
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
