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
lean_inc(v_a_585_);
if (lean_obj_tag(v_a_585_) == 0)
{
return v___x_584_;
}
else
{
lean_object* v_val_586_; lean_object* v___x_587_; 
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
lean_inc(v_a_655_);
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
lean_inc(v_a_749_);
if (lean_obj_tag(v_a_749_) == 0)
{
lean_dec_ref_known(v___x_742_, 3);
lean_dec_ref(v_p_714_);
return v___x_748_;
}
else
{
lean_object* v_val_750_; lean_object* v___x_751_; 
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
lean_inc(v_a_799_);
if (lean_obj_tag(v_a_799_) == 0)
{
lean_dec_ref_known(v___x_796_, 3);
lean_dec_ref(v_p_768_);
return v___x_798_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_801_; 
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
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__0);
v___x_948_ = lean_int_neg(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(lean_object* v_e_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_n_959_; lean_object* v___y_960_; 
switch(lean_obj_tag(v_e_949_))
{
case 1:
{
lean_object* v_k_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1028_; 
v_k_991_ = lean_ctor_get(v_e_949_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_e_949_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_993_ = v_e_949_;
v_isShared_994_ = v_isSharedCheck_1028_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_k_991_);
lean_dec(v_e_949_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1028_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_nat_to_int(v_k_991_);
v___x_996_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_995_, v_a_950_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1019_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1019_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1019_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
if (lean_obj_tag(v_a_997_) == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_del_object(v___x_993_);
v___x_1001_ = lean_box(0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
else
{
lean_object* v_val_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1018_; 
v_val_1005_ = lean_ctor_get(v_a_997_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_a_997_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1007_ = v_a_997_;
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_val_1005_);
lean_dec(v_a_997_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 0);
lean_ctor_set(v___x_993_, 0, v_val_1005_);
v___x_1010_ = v___x_993_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_val_1005_);
v___x_1010_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1012_);
v___x_1014_ = v___x_999_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_del_object(v___x_993_);
v_a_1020_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_996_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_996_);
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
case 3:
{
lean_object* v_i_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1038_; 
v_i_1029_ = lean_ctor_get(v_e_949_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_e_949_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1031_ = v_e_949_;
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_i_1029_);
lean_dec(v_e_949_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 1);
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
case 4:
{
lean_object* v_a_1039_; lean_object* v___x_1040_; 
v_a_1039_ = lean_ctor_get(v_e_949_, 0);
lean_inc_ref(v_a_1039_);
lean_dec_ref_known(v_e_949_, 1);
v___x_1040_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1039_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
if (lean_obj_tag(v_a_1041_) == 0)
{
return v___x_1040_;
}
else
{
lean_object* v_val_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref_known(v___x_1040_, 1);
v_val_1042_ = lean_ctor_get(v_a_1041_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v_a_1041_, 1);
v___x_1043_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0);
v___x_1044_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v___x_1043_, v_val_1042_, v_a_950_);
return v___x_1044_;
}
}
else
{
return v___x_1040_;
}
}
case 5:
{
lean_object* v_a_1045_; lean_object* v_b_1046_; lean_object* v___x_1047_; 
v_a_1045_ = lean_ctor_get(v_e_949_, 0);
lean_inc_ref(v_a_1045_);
v_b_1046_ = lean_ctor_get(v_e_949_, 1);
lean_inc_ref(v_b_1046_);
lean_dec_ref_known(v_e_949_, 2);
v___x_1047_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1045_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
if (lean_obj_tag(v_a_1048_) == 0)
{
lean_dec_ref(v_b_1046_);
return v___x_1047_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1050_; 
lean_dec_ref_known(v___x_1047_, 1);
v_val_1049_ = lean_ctor_get(v_a_1048_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v_a_1048_, 1);
v___x_1050_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1046_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
if (lean_obj_tag(v_a_1051_) == 0)
{
lean_dec(v_val_1049_);
return v___x_1050_;
}
else
{
lean_object* v_val_1052_; lean_object* v___x_1053_; 
lean_dec_ref_known(v___x_1050_, 1);
v_val_1052_ = lean_ctor_get(v_a_1051_, 0);
lean_inc(v_val_1052_);
lean_dec_ref_known(v_a_1051_, 1);
v___x_1053_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1049_, v_val_1052_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_1053_;
}
}
else
{
lean_dec(v_val_1049_);
return v___x_1050_;
}
}
}
else
{
lean_dec_ref(v_b_1046_);
return v___x_1047_;
}
}
case 6:
{
lean_object* v_a_1054_; lean_object* v_b_1055_; lean_object* v___x_1056_; 
v_a_1054_ = lean_ctor_get(v_e_949_, 0);
lean_inc_ref(v_a_1054_);
v_b_1055_ = lean_ctor_get(v_e_949_, 1);
lean_inc_ref(v_b_1055_);
lean_dec_ref_known(v_e_949_, 2);
v___x_1056_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1054_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
if (lean_obj_tag(v_a_1057_) == 0)
{
lean_dec_ref(v_b_1055_);
return v___x_1056_;
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1059_; 
lean_dec_ref_known(v___x_1056_, 1);
v_val_1058_ = lean_ctor_get(v_a_1057_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v_a_1057_, 1);
v___x_1059_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1055_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
if (lean_obj_tag(v_a_1060_) == 0)
{
lean_dec(v_val_1058_);
return v___x_1059_;
}
else
{
lean_object* v_val_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref_known(v___x_1059_, 1);
v_val_1061_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v_a_1060_, 1);
v___x_1062_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___closed__0);
v___x_1063_ = l_Lean_Meta_Sym_Arith_SafePoly_mulConst___redArg(v___x_1062_, v_val_1061_, v_a_950_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
if (lean_obj_tag(v_a_1064_) == 0)
{
lean_dec(v_val_1058_);
return v___x_1063_;
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1066_; 
lean_dec_ref_known(v___x_1063_, 1);
v_val_1065_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v_a_1064_, 1);
v___x_1066_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1058_, v_val_1065_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_1066_;
}
}
else
{
lean_dec(v_val_1058_);
return v___x_1063_;
}
}
}
else
{
lean_dec(v_val_1058_);
return v___x_1059_;
}
}
}
else
{
lean_dec_ref(v_b_1055_);
return v___x_1056_;
}
}
case 7:
{
lean_object* v_a_1067_; lean_object* v_b_1068_; lean_object* v___x_1069_; 
v_a_1067_ = lean_ctor_get(v_e_949_, 0);
lean_inc_ref(v_a_1067_);
v_b_1068_ = lean_ctor_get(v_e_949_, 1);
lean_inc_ref(v_b_1068_);
lean_dec_ref_known(v_e_949_, 2);
v___x_1069_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1067_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
if (lean_obj_tag(v_a_1070_) == 0)
{
lean_dec_ref(v_b_1068_);
return v___x_1069_;
}
else
{
lean_object* v_val_1071_; lean_object* v___x_1072_; 
lean_dec_ref_known(v___x_1069_, 1);
v_val_1071_ = lean_ctor_get(v_a_1070_, 0);
lean_inc(v_val_1071_);
lean_dec_ref_known(v_a_1070_, 1);
v___x_1072_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_b_1068_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
if (lean_obj_tag(v_a_1073_) == 0)
{
lean_dec(v_val_1071_);
return v___x_1072_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1075_; 
lean_dec_ref_known(v___x_1072_, 1);
v_val_1074_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_val_1074_);
lean_dec_ref_known(v_a_1073_, 1);
v___x_1075_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_1071_, v_val_1074_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_1075_;
}
}
else
{
lean_dec(v_val_1071_);
return v___x_1072_;
}
}
}
else
{
lean_dec_ref(v_b_1068_);
return v___x_1069_;
}
}
case 8:
{
lean_object* v_a_1076_; lean_object* v_k_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_a_1076_ = lean_ctor_get(v_e_949_, 0);
lean_inc_ref(v_a_1076_);
v_k_1077_ = lean_ctor_get(v_e_949_, 1);
lean_inc(v_k_1077_);
lean_dec_ref_known(v_e_949_, 2);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_nat_dec_eq(v_k_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
switch(lean_obj_tag(v_a_1076_))
{
case 0:
{
lean_object* v_k_1080_; lean_object* v___x_1081_; 
v_k_1080_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_k_1080_);
lean_dec_ref_known(v_a_1076_, 1);
lean_inc(v_k_1077_);
v___x_1081_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1077_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1128_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1128_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1128_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
if (lean_obj_tag(v_a_1082_) == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_dec(v_k_1080_);
lean_dec(v_k_1077_);
v___x_1086_ = lean_box(0);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
else
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1126_; 
lean_del_object(v___x_1084_);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1082_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_a_1082_, 0);
lean_dec(v_unused_1127_);
v___x_1091_ = v_a_1082_;
v_isShared_1092_ = v_isSharedCheck_1126_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v_a_1082_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1126_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = l_Int_pow(v_k_1080_, v_k_1077_);
lean_dec(v_k_1077_);
lean_dec(v_k_1080_);
v___x_1094_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v___x_1093_, v_a_950_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1117_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1117_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1117_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
if (lean_obj_tag(v_a_1095_) == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_del_object(v___x_1091_);
v___x_1099_ = lean_box(0);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1099_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1116_; 
v_val_1103_ = lean_ctor_get(v_a_1095_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_a_1095_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1105_ = v_a_1095_;
v_isShared_1106_ = v_isSharedCheck_1116_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_val_1103_);
lean_dec(v_a_1095_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1116_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 0);
lean_ctor_set(v___x_1091_, 0, v_val_1103_);
v___x_1108_ = v___x_1091_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_val_1103_);
v___x_1108_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1110_);
v___x_1112_ = v___x_1097_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_del_object(v___x_1091_);
v_a_1118_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1094_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1094_);
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
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_k_1080_);
lean_dec(v_k_1077_);
v_a_1129_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1081_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1081_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
case 3:
{
lean_object* v_i_1137_; lean_object* v___x_1138_; 
v_i_1137_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_i_1137_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1138_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1137_, v_k_1077_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_1138_;
}
default: 
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_a_1076_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
if (lean_obj_tag(v_a_1140_) == 0)
{
lean_dec(v_k_1077_);
return v___x_1139_;
}
else
{
lean_object* v_val_1141_; lean_object* v___x_1142_; 
lean_dec_ref_known(v___x_1139_, 1);
v_val_1141_ = lean_ctor_get(v_a_1140_, 0);
lean_inc(v_val_1141_);
lean_dec_ref_known(v_a_1140_, 1);
v___x_1142_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_val_1141_, v_k_1077_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_k_1077_);
return v___x_1142_;
}
}
else
{
lean_dec(v_k_1077_);
return v___x_1139_;
}
}
}
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v_k_1077_);
lean_dec_ref(v_a_1076_);
v___x_1143_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
default: 
{
lean_object* v_k_1145_; 
v_k_1145_ = lean_ctor_get(v_e_949_, 0);
lean_inc(v_k_1145_);
lean_dec_ref(v_e_949_);
v_n_959_ = v_k_1145_;
v___y_960_ = v_a_950_;
goto v___jp_958_;
}
}
v___jp_958_:
{
lean_object* v___x_961_; 
v___x_961_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_applyChar___redArg(v_n_959_, v___y_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_982_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_982_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_982_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_982_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
if (lean_obj_tag(v_a_962_) == 0)
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_968_ = v___x_964_;
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
else
{
lean_object* v_val_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_981_; 
v_val_970_ = lean_ctor_get(v_a_962_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_a_962_);
if (v_isSharedCheck_981_ == 0)
{
v___x_972_ = v_a_962_;
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_val_970_);
lean_dec(v_a_962_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_val_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_980_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_978_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_976_);
v___x_978_ = v___x_964_;
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
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_961_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_961_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing___boxed(lean_object* v_e_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec_ref(v_a_1147_);
return v_res_1155_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0, &l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_SafePoly_mul___closed__0);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(lean_object* v_e_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
switch(lean_obj_tag(v_e_1158_))
{
case 0:
{
lean_object* v_k_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1178_; 
v_k_1167_ = lean_ctor_get(v_e_1158_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_e_1158_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1169_ = v_e_1158_;
v_isShared_1170_ = v_isSharedCheck_1178_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_k_1167_);
lean_dec(v_e_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1178_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = lean_nat_abs(v_k_1167_);
lean_dec(v_k_1167_);
v___x_1172_ = lean_nat_to_int(v___x_1171_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
case 1:
{
lean_object* v_k_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1189_; 
v_k_1179_ = lean_ctor_get(v_e_1158_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_e_1158_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1181_ = v_e_1158_;
v_isShared_1182_ = v_isSharedCheck_1189_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_k_1179_);
lean_dec(v_e_1158_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1189_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_nat_to_int(v_k_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
}
case 3:
{
lean_object* v_i_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1199_; 
v_i_1190_ = lean_ctor_get(v_e_1158_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_e_1158_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1192_ = v_e_1158_;
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_i_1190_);
lean_dec(v_e_1158_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set_tag(v___x_1192_, 1);
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
}
case 5:
{
lean_object* v_a_1200_; lean_object* v_b_1201_; lean_object* v___x_1202_; 
v_a_1200_ = lean_ctor_get(v_e_1158_, 0);
lean_inc_ref(v_a_1200_);
v_b_1201_ = lean_ctor_get(v_e_1158_, 1);
lean_inc_ref(v_b_1201_);
lean_dec_ref_known(v_e_1158_, 2);
v___x_1202_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1200_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
if (lean_obj_tag(v_a_1203_) == 0)
{
lean_dec_ref(v_b_1201_);
return v___x_1202_;
}
else
{
lean_object* v_val_1204_; lean_object* v___x_1205_; 
lean_dec_ref_known(v___x_1202_, 1);
v_val_1204_ = lean_ctor_get(v_a_1203_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v_a_1203_, 1);
v___x_1205_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_b_1201_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
if (lean_obj_tag(v_a_1206_) == 0)
{
lean_dec(v_val_1204_);
return v___x_1205_;
}
else
{
lean_object* v_val_1207_; lean_object* v___x_1208_; 
lean_dec_ref_known(v___x_1205_, 1);
v_val_1207_ = lean_ctor_get(v_a_1206_, 0);
lean_inc(v_val_1207_);
lean_dec_ref_known(v_a_1206_, 1);
v___x_1208_ = l_Lean_Meta_Sym_Arith_SafePoly_combine(v_val_1204_, v_val_1207_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1208_;
}
}
else
{
lean_dec(v_val_1204_);
return v___x_1205_;
}
}
}
else
{
lean_dec_ref(v_b_1201_);
return v___x_1202_;
}
}
case 7:
{
lean_object* v_a_1209_; lean_object* v_b_1210_; lean_object* v___x_1211_; 
v_a_1209_ = lean_ctor_get(v_e_1158_, 0);
lean_inc_ref(v_a_1209_);
v_b_1210_ = lean_ctor_get(v_e_1158_, 1);
lean_inc_ref(v_b_1210_);
lean_dec_ref_known(v_e_1158_, 2);
v___x_1211_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1209_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
if (lean_obj_tag(v_a_1212_) == 0)
{
lean_dec_ref(v_b_1210_);
return v___x_1211_;
}
else
{
lean_object* v_val_1213_; lean_object* v___x_1214_; 
lean_dec_ref_known(v___x_1211_, 1);
v_val_1213_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_val_1213_);
lean_dec_ref_known(v_a_1212_, 1);
v___x_1214_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_b_1210_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
if (lean_obj_tag(v_a_1215_) == 0)
{
lean_dec(v_val_1213_);
return v___x_1214_;
}
else
{
lean_object* v_val_1216_; lean_object* v___x_1217_; 
lean_dec_ref_known(v___x_1214_, 1);
v_val_1216_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_val_1216_);
lean_dec_ref_known(v_a_1215_, 1);
v___x_1217_ = l_Lean_Meta_Sym_Arith_SafePoly_mul(v_val_1213_, v_val_1216_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1217_;
}
}
else
{
lean_dec(v_val_1213_);
return v___x_1214_;
}
}
}
else
{
lean_dec_ref(v_b_1210_);
return v___x_1211_;
}
}
case 8:
{
lean_object* v_a_1218_; lean_object* v_k_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v_a_1218_ = lean_ctor_get(v_e_1158_, 0);
lean_inc_ref(v_a_1218_);
v_k_1219_ = lean_ctor_get(v_e_1158_, 1);
lean_inc(v_k_1219_);
lean_dec_ref_known(v_e_1158_, 2);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_nat_dec_eq(v_k_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
switch(lean_obj_tag(v_a_1218_))
{
case 0:
{
lean_object* v_k_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1261_; 
v_k_1222_ = lean_ctor_get(v_a_1218_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1224_ = v_a_1218_;
v_isShared_1225_ = v_isSharedCheck_1261_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_k_1222_);
lean_dec(v_a_1218_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1261_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; 
lean_inc(v_k_1219_);
v___x_1226_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_1219_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1252_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1252_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1252_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
if (lean_obj_tag(v_a_1227_) == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
lean_del_object(v___x_1224_);
lean_dec(v_k_1222_);
lean_dec(v_k_1219_);
v___x_1231_ = lean_box(0);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
else
{
lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v_a_1227_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v_a_1227_, 0);
lean_dec(v_unused_1251_);
v___x_1236_ = v_a_1227_;
v_isShared_1237_ = v_isSharedCheck_1250_;
goto v_resetjp_1235_;
}
else
{
lean_dec(v_a_1227_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1250_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1238_ = lean_nat_abs(v_k_1222_);
lean_dec(v_k_1222_);
v___x_1239_ = lean_nat_to_int(v___x_1238_);
v___x_1240_ = l_Int_pow(v___x_1239_, v_k_1219_);
lean_dec(v_k_1219_);
lean_dec(v___x_1239_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1240_);
v___x_1242_ = v___x_1224_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1242_);
v___x_1244_ = v___x_1236_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1244_);
v___x_1246_ = v___x_1229_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
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
lean_del_object(v___x_1224_);
lean_dec(v_k_1222_);
lean_dec(v_k_1219_);
v_a_1253_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1226_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1226_);
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
case 3:
{
lean_object* v_i_1262_; lean_object* v___x_1263_; 
v_i_1262_ = lean_ctor_get(v_a_1218_, 0);
lean_inc(v_i_1262_);
lean_dec_ref_known(v_a_1218_, 1);
v___x_1263_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_mkPowVar(v_i_1262_, v_k_1219_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1263_;
}
default: 
{
lean_object* v___x_1264_; 
v___x_1264_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_a_1218_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
if (lean_obj_tag(v_a_1265_) == 0)
{
lean_dec(v_k_1219_);
return v___x_1264_;
}
else
{
lean_object* v_val_1266_; lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1264_, 1);
v_val_1266_ = lean_ctor_get(v_a_1265_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v_a_1265_, 1);
v___x_1267_ = l_Lean_Meta_Sym_Arith_SafePoly_pow(v_val_1266_, v_k_1219_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_k_1219_);
return v___x_1267_;
}
}
else
{
lean_dec(v_k_1219_);
return v___x_1264_;
}
}
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v_k_1219_);
lean_dec_ref(v_a_1218_);
v___x_1268_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_powComm___closed__2);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
default: 
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_e_1158_);
v___x_1270_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0, &l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___closed__0);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring___boxed(lean_object* v_e_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_a_1273_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f(lean_object* v_e_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
uint8_t v_semiring_1291_; 
v_semiring_1291_ = lean_ctor_get_uint8(v_a_1283_, sizeof(void*)*3);
if (v_semiring_1291_ == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolyRing(v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Lean_Meta_Sym_Arith_SafePoly_0__Lean_Meta_Sym_Arith_SafePoly_toPolySemiring(v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_toPoly_x3f___boxed(lean_object* v_e_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Meta_Sym_Arith_toPoly_x3f(v_e_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec_ref(v_a_1295_);
return v_res_1303_;
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
