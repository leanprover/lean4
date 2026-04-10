// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "error while initializing `grind ring` operators:\ninstance for `"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "\nis not definitionally equal to the expected one "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "\nwhen only reducible definitions and instances are reduced"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 4, 252, 84, 28, 16, 24, 6)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInv"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 152, 64, 108, 234, 163, 46, 107)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`grind` internal error, type is not a field"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object* v_declName_59_, lean_object* v_inst_60_, lean_object* v_inst_x27_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
lean_inc_ref(v_inst_x27_61_);
lean_inc_ref(v_inst_60_);
v___x_67_ = l_Lean_Meta_isDefEqI(v_inst_60_, v_inst_x27_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_91_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_91_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_91_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_91_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; 
v___x_72_ = lean_unbox(v_a_68_);
lean_dec(v_a_68_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
lean_del_object(v___x_70_);
v___x_73_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1);
v___x_74_ = l_Lean_MessageData_ofName(v_declName_59_);
v___x_75_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3);
v___x_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = l_Lean_indentExpr(v_inst_60_);
v___x_79_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5);
v___x_81_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = l_Lean_indentExpr(v_inst_x27_61_);
v___x_83_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v___x_85_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_89_; 
lean_dec_ref(v_inst_x27_61_);
lean_dec_ref(v_inst_60_);
lean_dec(v_declName_59_);
v___x_87_ = lean_box(0);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_87_);
v___x_89_ = v___x_70_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref(v_inst_x27_61_);
lean_dec_ref(v_inst_60_);
lean_dec(v_declName_59_);
v_a_92_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_67_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_67_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed(lean_object* v_declName_100_, lean_object* v_inst_101_, lean_object* v_inst_x27_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_100_, v_inst_101_, v_inst_x27_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(lean_object* v_00_u03b1_109_, lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v_msg_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___boxed(lean_object* v_00_u03b1_117_, lean_object* v_msg_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(v_00_u03b1_117_, v_msg_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0(lean_object* v_inst_125_, lean_object* v_declName_126_, lean_object* v___x_127_, lean_object* v_type_128_, lean_object* v_inst_129_, lean_object* v_____r_130_){
_start:
{
lean_object* v_canonExpr_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_canonExpr_131_ = lean_ctor_get(v_inst_125_, 0);
lean_inc(v_canonExpr_131_);
lean_dec_ref(v_inst_125_);
v___x_132_ = l_Lean_mkConst(v_declName_126_, v___x_127_);
v___x_133_ = l_Lean_mkAppB(v___x_132_, v_type_128_, v_inst_129_);
v___x_134_ = lean_apply_1(v_canonExpr_131_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1(lean_object* v_inst_135_, lean_object* v_declName_136_, lean_object* v___x_137_, lean_object* v_type_138_, lean_object* v_expectedInst_139_, lean_object* v_inst_140_, lean_object* v_toBind_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
lean_inc_ref(v_inst_142_);
lean_inc(v_declName_136_);
v___f_143_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_143_, 0, v_inst_135_);
lean_closure_set(v___f_143_, 1, v_declName_136_);
lean_closure_set(v___f_143_, 2, v___x_137_);
lean_closure_set(v___f_143_, 3, v_type_138_);
lean_closure_set(v___f_143_, 4, v_inst_142_);
v___x_144_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_144_, 0, v_declName_136_);
lean_closure_set(v___x_144_, 1, v_inst_142_);
lean_closure_set(v___x_144_, 2, v_expectedInst_139_);
v___x_145_ = lean_apply_2(v_inst_140_, lean_box(0), v___x_144_);
v___x_146_ = lean_apply_4(v_toBind_141_, lean_box(0), lean_box(0), v___x_145_, v___f_143_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_type_151_, lean_object* v_u_152_, lean_object* v_instDeclName_153_, lean_object* v_declName_154_, lean_object* v_expectedInst_155_){
_start:
{
lean_object* v_toBind_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_toBind_156_ = lean_ctor_get(v_inst_149_, 1);
lean_inc_n(v_toBind_156_, 2);
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v_u_152_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
lean_inc_ref(v_type_151_);
lean_inc_ref(v___x_158_);
lean_inc_ref(v_inst_150_);
v___f_159_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_159_, 0, v_inst_150_);
lean_closure_set(v___f_159_, 1, v_declName_154_);
lean_closure_set(v___f_159_, 2, v___x_158_);
lean_closure_set(v___f_159_, 3, v_type_151_);
lean_closure_set(v___f_159_, 4, v_expectedInst_155_);
lean_closure_set(v___f_159_, 5, v_inst_147_);
lean_closure_set(v___f_159_, 6, v_toBind_156_);
v___x_160_ = l_Lean_mkConst(v_instDeclName_153_, v___x_158_);
v___x_161_ = l_Lean_Expr_app___override(v___x_160_, v_type_151_);
v___x_162_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_149_, v_inst_148_, v_inst_150_, v___x_161_);
v___x_163_ = lean_apply_4(v_toBind_156_, lean_box(0), lean_box(0), v___x_162_, v___f_159_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn(lean_object* v_m_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_type_169_, lean_object* v_u_170_, lean_object* v_instDeclName_171_, lean_object* v_declName_172_, lean_object* v_expectedInst_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(v_inst_165_, v_inst_166_, v_inst_167_, v_inst_168_, v_type_169_, v_u_170_, v_instDeclName_171_, v_declName_172_, v_expectedInst_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_175_, lean_object* v_declName_176_, lean_object* v___x_177_, lean_object* v_type_178_, lean_object* v_inst_179_, lean_object* v_____r_180_){
_start:
{
lean_object* v_canonExpr_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_canonExpr_181_ = lean_ctor_get(v_inst_175_, 0);
lean_inc(v_canonExpr_181_);
lean_dec_ref(v_inst_175_);
v___x_182_ = l_Lean_mkConst(v_declName_176_, v___x_177_);
lean_inc_ref_n(v_type_178_, 2);
v___x_183_ = l_Lean_mkApp4(v___x_182_, v_type_178_, v_type_178_, v_type_178_, v_inst_179_);
v___x_184_ = lean_apply_1(v_canonExpr_181_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_185_, lean_object* v_declName_186_, lean_object* v___x_187_, lean_object* v_type_188_, lean_object* v_expectedInst_189_, lean_object* v_inst_190_, lean_object* v_toBind_191_, lean_object* v_inst_192_){
_start:
{
lean_object* v___f_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
lean_inc_ref(v_inst_192_);
lean_inc(v_declName_186_);
v___f_193_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_193_, 0, v_inst_185_);
lean_closure_set(v___f_193_, 1, v_declName_186_);
lean_closure_set(v___f_193_, 2, v___x_187_);
lean_closure_set(v___f_193_, 3, v_type_188_);
lean_closure_set(v___f_193_, 4, v_inst_192_);
v___x_194_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_194_, 0, v_declName_186_);
lean_closure_set(v___x_194_, 1, v_inst_192_);
lean_closure_set(v___x_194_, 2, v_expectedInst_189_);
v___x_195_ = lean_apply_2(v_inst_190_, lean_box(0), v___x_194_);
v___x_196_ = lean_apply_4(v_toBind_191_, lean_box(0), lean_box(0), v___x_195_, v___f_193_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_type_201_, lean_object* v_u_202_, lean_object* v_instDeclName_203_, lean_object* v_declName_204_, lean_object* v_expectedInst_205_){
_start:
{
lean_object* v_toBind_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_toBind_206_ = lean_ctor_get(v_inst_199_, 1);
lean_inc_n(v_toBind_206_, 2);
v___x_207_ = lean_box(0);
lean_inc_n(v_u_202_, 2);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v_u_202_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v_u_202_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v_u_202_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
lean_inc_ref_n(v_type_201_, 3);
lean_inc_ref(v___x_210_);
lean_inc_ref(v_inst_200_);
v___f_211_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_211_, 0, v_inst_200_);
lean_closure_set(v___f_211_, 1, v_declName_204_);
lean_closure_set(v___f_211_, 2, v___x_210_);
lean_closure_set(v___f_211_, 3, v_type_201_);
lean_closure_set(v___f_211_, 4, v_expectedInst_205_);
lean_closure_set(v___f_211_, 5, v_inst_197_);
lean_closure_set(v___f_211_, 6, v_toBind_206_);
v___x_212_ = l_Lean_mkConst(v_instDeclName_203_, v___x_210_);
v___x_213_ = l_Lean_mkApp3(v___x_212_, v_type_201_, v_type_201_, v_type_201_);
v___x_214_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_199_, v_inst_198_, v_inst_200_, v___x_213_);
v___x_215_ = lean_apply_4(v_toBind_206_, lean_box(0), lean_box(0), v___x_214_, v___f_211_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn(lean_object* v_m_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_type_221_, lean_object* v_u_222_, lean_object* v_instDeclName_223_, lean_object* v_declName_224_, lean_object* v_expectedInst_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_217_, v_inst_218_, v_inst_219_, v_inst_220_, v_type_221_, v_u_222_, v_instDeclName_223_, v_declName_224_, v_expectedInst_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0(lean_object* v_inst_227_, lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v_type_230_, lean_object* v___x_231_, lean_object* v_inst_232_, lean_object* v_____r_233_){
_start:
{
lean_object* v_canonExpr_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_canonExpr_234_ = lean_ctor_get(v_inst_227_, 0);
lean_inc(v_canonExpr_234_);
lean_dec_ref(v_inst_227_);
v___x_235_ = l_Lean_mkConst(v___x_228_, v___x_229_);
lean_inc_ref(v_type_230_);
v___x_236_ = l_Lean_mkApp4(v___x_235_, v_type_230_, v___x_231_, v_type_230_, v_inst_232_);
v___x_237_ = lean_apply_1(v_canonExpr_234_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1(lean_object* v___x_248_, lean_object* v_type_249_, lean_object* v_semiringInst_250_, lean_object* v___x_251_, lean_object* v_inst_252_, lean_object* v___x_253_, lean_object* v___x_254_, lean_object* v_inst_255_, lean_object* v_toBind_256_, lean_object* v_inst_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_inst_x27_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_258_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4));
v___x_259_ = l_Lean_mkConst(v___x_258_, v___x_248_);
lean_inc_ref(v_type_249_);
v_inst_x27_260_ = l_Lean_mkAppB(v___x_259_, v_type_249_, v_semiringInst_250_);
v___x_261_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5));
v___x_262_ = l_Lean_Name_mkStr2(v___x_251_, v___x_261_);
lean_inc_ref(v_inst_257_);
lean_inc(v___x_262_);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_263_, 0, v_inst_252_);
lean_closure_set(v___f_263_, 1, v___x_262_);
lean_closure_set(v___f_263_, 2, v___x_253_);
lean_closure_set(v___f_263_, 3, v_type_249_);
lean_closure_set(v___f_263_, 4, v___x_254_);
lean_closure_set(v___f_263_, 5, v_inst_257_);
v___x_264_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_264_, 0, v___x_262_);
lean_closure_set(v___x_264_, 1, v_inst_257_);
lean_closure_set(v___x_264_, 2, v_inst_x27_260_);
v___x_265_ = lean_apply_2(v_inst_255_, lean_box(0), v___x_264_);
v___x_266_ = lean_apply_4(v_toBind_256_, lean_box(0), lean_box(0), v___x_265_, v___f_263_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = l_Lean_Level_ofNat(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_u_276_, lean_object* v_type_277_, lean_object* v_semiringInst_278_){
_start:
{
lean_object* v_toBind_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_toBind_279_ = lean_ctor_get(v_inst_274_, 1);
lean_inc_n(v_toBind_279_, 2);
v___x_280_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0));
v___x_281_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1));
v___x_282_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2);
v___x_283_ = lean_box(0);
lean_inc(v_u_276_);
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v_u_276_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
lean_inc_ref(v___x_284_);
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_282_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_286_, 0, v_u_276_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_inc_ref(v___x_286_);
v___x_287_ = l_Lean_mkConst(v___x_281_, v___x_286_);
v___x_288_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_275_);
lean_inc_ref_n(v_type_277_, 2);
v___f_289_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_289_, 0, v___x_284_);
lean_closure_set(v___f_289_, 1, v_type_277_);
lean_closure_set(v___f_289_, 2, v_semiringInst_278_);
lean_closure_set(v___f_289_, 3, v___x_280_);
lean_closure_set(v___f_289_, 4, v_inst_275_);
lean_closure_set(v___f_289_, 5, v___x_286_);
lean_closure_set(v___f_289_, 6, v___x_288_);
lean_closure_set(v___f_289_, 7, v_inst_272_);
lean_closure_set(v___f_289_, 8, v_toBind_279_);
v___x_290_ = l_Lean_mkApp3(v___x_287_, v_type_277_, v___x_288_, v_type_277_);
v___x_291_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_274_, v_inst_273_, v_inst_275_, v___x_290_);
v___x_292_ = lean_apply_4(v_toBind_279_, lean_box(0), lean_box(0), v___x_291_, v___f_289_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn(lean_object* v_m_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_u_298_, lean_object* v_type_299_, lean_object* v_semiringInst_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_294_, v_inst_295_, v_inst_296_, v_inst_297_, v_u_298_, v_type_299_, v_semiringInst_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0(lean_object* v___x_302_, lean_object* v___x_303_, lean_object* v___x_304_, lean_object* v_type_305_, lean_object* v_canonExpr_306_, lean_object* v_inst_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = l_Lean_Name_mkStr2(v___x_302_, v___x_303_);
v___x_309_ = l_Lean_mkConst(v___x_308_, v___x_304_);
v___x_310_ = l_Lean_mkAppB(v___x_309_, v_type_305_, v_inst_307_);
v___x_311_ = lean_apply_1(v_canonExpr_306_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1(lean_object* v___f_312_, lean_object* v_inst_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_apply_1(v___f_312_, v_inst_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_315_, lean_object* v_val_316_, lean_object* v_toBind_317_, lean_object* v___f_318_, lean_object* v_____r_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_apply_2(v_toPure_315_, lean_box(0), v_val_316_);
v___x_321_ = lean_apply_4(v_toBind_317_, lean_box(0), lean_box(0), v___x_320_, v___f_318_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_322_, lean_object* v_inst_x27_323_, lean_object* v_toBind_324_, lean_object* v___f_325_, lean_object* v___f_326_, lean_object* v___x_327_, lean_object* v___x_328_, lean_object* v_inst_329_, lean_object* v_____do__lift_330_){
_start:
{
if (lean_obj_tag(v_____do__lift_330_) == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_inst_329_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v___x_327_);
lean_dec(v___f_326_);
v___x_331_ = lean_apply_2(v_toPure_322_, lean_box(0), v_inst_x27_323_);
v___x_332_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v___x_331_, v___f_325_);
return v___x_332_;
}
else
{
lean_object* v_val_333_; lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v___f_325_);
v_val_333_ = lean_ctor_get(v_____do__lift_330_, 0);
lean_inc_n(v_val_333_, 2);
lean_dec_ref(v_____do__lift_330_);
lean_inc(v_toBind_324_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_334_, 0, v_toPure_322_);
lean_closure_set(v___f_334_, 1, v_val_333_);
lean_closure_set(v___f_334_, 2, v_toBind_324_);
lean_closure_set(v___f_334_, 3, v___f_326_);
v___x_335_ = l_Lean_Name_mkStr2(v___x_327_, v___x_328_);
v___x_336_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_336_, 0, v___x_335_);
lean_closure_set(v___x_336_, 1, v_val_333_);
lean_closure_set(v___x_336_, 2, v_inst_x27_323_);
v___x_337_ = lean_apply_2(v_inst_329_, lean_box(0), v___x_336_);
v___x_338_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v___x_337_, v___f_334_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_u_351_, lean_object* v_type_352_, lean_object* v_semiringInst_353_){
_start:
{
lean_object* v_toApplicative_354_; lean_object* v_toBind_355_; lean_object* v_canonExpr_356_; lean_object* v_synthInstance_x3f_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_379_; 
v_toApplicative_354_ = lean_ctor_get(v_inst_349_, 0);
lean_inc_ref(v_toApplicative_354_);
v_toBind_355_ = lean_ctor_get(v_inst_349_, 1);
lean_inc(v_toBind_355_);
lean_dec_ref(v_inst_349_);
v_canonExpr_356_ = lean_ctor_get(v_inst_350_, 0);
v_synthInstance_x3f_357_ = lean_ctor_get(v_inst_350_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_inst_350_);
if (v_isSharedCheck_379_ == 0)
{
v___x_359_ = v_inst_350_;
v_isShared_360_ = v_isSharedCheck_379_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_synthInstance_x3f_357_);
lean_inc(v_canonExpr_356_);
lean_dec(v_inst_350_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_379_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_toPure_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v_toPure_361_ = lean_ctor_get(v_toApplicative_354_, 1);
lean_inc(v_toPure_361_);
lean_dec_ref(v_toApplicative_354_);
v___x_362_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0));
v___x_363_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1));
v___x_364_ = lean_box(0);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
lean_ctor_set(v___x_359_, 1, v___x_364_);
lean_ctor_set(v___x_359_, 0, v_u_351_);
v___x_366_ = v___x_359_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_u_351_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_378_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v_inst_x27_368_; lean_object* v___x_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_instType_374_; lean_object* v___x_375_; lean_object* v___f_376_; lean_object* v___x_377_; 
lean_inc_ref_n(v___x_366_, 2);
v___x_367_ = l_Lean_mkConst(v___x_363_, v___x_366_);
lean_inc_ref_n(v_type_352_, 2);
v_inst_x27_368_ = l_Lean_mkAppB(v___x_367_, v_type_352_, v_semiringInst_353_);
v___x_369_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2));
v___f_370_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_370_, 0, v___x_369_);
lean_closure_set(v___f_370_, 1, v___x_362_);
lean_closure_set(v___f_370_, 2, v___x_366_);
lean_closure_set(v___f_370_, 3, v_type_352_);
lean_closure_set(v___f_370_, 4, v_canonExpr_356_);
v___f_371_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_371_, 0, v___f_370_);
v___x_372_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3));
v___x_373_ = l_Lean_mkConst(v___x_372_, v___x_366_);
v_instType_374_ = l_Lean_Expr_app___override(v___x_373_, v_type_352_);
v___x_375_ = lean_apply_1(v_synthInstance_x3f_357_, v_instType_374_);
lean_inc_ref(v___f_371_);
lean_inc(v_toBind_355_);
v___f_376_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_376_, 0, v_toPure_361_);
lean_closure_set(v___f_376_, 1, v_inst_x27_368_);
lean_closure_set(v___f_376_, 2, v_toBind_355_);
lean_closure_set(v___f_376_, 3, v___f_371_);
lean_closure_set(v___f_376_, 4, v___f_371_);
lean_closure_set(v___f_376_, 5, v___x_369_);
lean_closure_set(v___f_376_, 6, v___x_362_);
lean_closure_set(v___f_376_, 7, v_inst_348_);
v___x_377_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v___x_375_, v___f_376_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn(lean_object* v_m_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_u_384_, lean_object* v_type_385_, lean_object* v_semiringInst_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_381_, v_inst_382_, v_inst_383_, v_u_384_, v_type_385_, v_semiringInst_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0(lean_object* v_addFn_388_, lean_object* v_s_389_){
_start:
{
lean_object* v_id_390_; lean_object* v_type_391_; lean_object* v_u_392_; lean_object* v_ringInst_393_; lean_object* v_semiringInst_394_; lean_object* v_charInst_x3f_395_; lean_object* v_mulFn_x3f_396_; lean_object* v_subFn_x3f_397_; lean_object* v_negFn_x3f_398_; lean_object* v_powFn_x3f_399_; lean_object* v_intCastFn_x3f_400_; lean_object* v_natCastFn_x3f_401_; lean_object* v_one_x3f_402_; lean_object* v_vars_403_; lean_object* v_varMap_404_; lean_object* v_denote_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_id_390_ = lean_ctor_get(v_s_389_, 0);
v_type_391_ = lean_ctor_get(v_s_389_, 1);
v_u_392_ = lean_ctor_get(v_s_389_, 2);
v_ringInst_393_ = lean_ctor_get(v_s_389_, 3);
v_semiringInst_394_ = lean_ctor_get(v_s_389_, 4);
v_charInst_x3f_395_ = lean_ctor_get(v_s_389_, 5);
v_mulFn_x3f_396_ = lean_ctor_get(v_s_389_, 7);
v_subFn_x3f_397_ = lean_ctor_get(v_s_389_, 8);
v_negFn_x3f_398_ = lean_ctor_get(v_s_389_, 9);
v_powFn_x3f_399_ = lean_ctor_get(v_s_389_, 10);
v_intCastFn_x3f_400_ = lean_ctor_get(v_s_389_, 11);
v_natCastFn_x3f_401_ = lean_ctor_get(v_s_389_, 12);
v_one_x3f_402_ = lean_ctor_get(v_s_389_, 13);
v_vars_403_ = lean_ctor_get(v_s_389_, 14);
v_varMap_404_ = lean_ctor_get(v_s_389_, 15);
v_denote_405_ = lean_ctor_get(v_s_389_, 16);
v_isSharedCheck_413_ = !lean_is_exclusive(v_s_389_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v_s_389_, 6);
lean_dec(v_unused_414_);
v___x_407_ = v_s_389_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_denote_405_);
lean_inc(v_varMap_404_);
lean_inc(v_vars_403_);
lean_inc(v_one_x3f_402_);
lean_inc(v_natCastFn_x3f_401_);
lean_inc(v_intCastFn_x3f_400_);
lean_inc(v_powFn_x3f_399_);
lean_inc(v_negFn_x3f_398_);
lean_inc(v_subFn_x3f_397_);
lean_inc(v_mulFn_x3f_396_);
lean_inc(v_charInst_x3f_395_);
lean_inc(v_semiringInst_394_);
lean_inc(v_ringInst_393_);
lean_inc(v_u_392_);
lean_inc(v_type_391_);
lean_inc(v_id_390_);
lean_dec(v_s_389_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v_addFn_388_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 6, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_id_390_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_type_391_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_u_392_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_ringInst_393_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_semiringInst_394_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v_charInst_x3f_395_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_mulFn_x3f_396_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_subFn_x3f_397_);
lean_ctor_set(v_reuseFailAlloc_412_, 9, v_negFn_x3f_398_);
lean_ctor_set(v_reuseFailAlloc_412_, 10, v_powFn_x3f_399_);
lean_ctor_set(v_reuseFailAlloc_412_, 11, v_intCastFn_x3f_400_);
lean_ctor_set(v_reuseFailAlloc_412_, 12, v_natCastFn_x3f_401_);
lean_ctor_set(v_reuseFailAlloc_412_, 13, v_one_x3f_402_);
lean_ctor_set(v_reuseFailAlloc_412_, 14, v_vars_403_);
lean_ctor_set(v_reuseFailAlloc_412_, 15, v_varMap_404_);
lean_ctor_set(v_reuseFailAlloc_412_, 16, v_denote_405_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1(lean_object* v_toPure_415_, lean_object* v_addFn_416_, lean_object* v_____r_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_apply_2(v_toPure_415_, lean_box(0), v_addFn_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2(lean_object* v_toPure_419_, lean_object* v_modifyRing_420_, lean_object* v_toBind_421_, lean_object* v_addFn_422_){
_start:
{
lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_inc_ref(v_addFn_422_);
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_423_, 0, v_addFn_422_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_424_, 0, v_toPure_419_);
lean_closure_set(v___f_424_, 1, v_addFn_422_);
v___x_425_ = lean_apply_1(v_modifyRing_420_, v___f_423_);
v___x_426_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_425_, v___f_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3(lean_object* v_toPure_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_toBind_448_, lean_object* v___f_449_, lean_object* v_ring_450_){
_start:
{
lean_object* v_addFn_x3f_451_; 
v_addFn_x3f_451_ = lean_ctor_get(v_ring_450_, 6);
if (lean_obj_tag(v_addFn_x3f_451_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_453_; 
lean_inc_ref(v_addFn_x3f_451_);
lean_dec_ref(v_ring_450_);
lean_dec(v___f_449_);
lean_dec(v_toBind_448_);
lean_dec_ref(v_inst_447_);
lean_dec_ref(v_inst_446_);
lean_dec_ref(v_inst_445_);
lean_dec(v_inst_444_);
v_val_452_ = lean_ctor_get(v_addFn_x3f_451_, 0);
lean_inc(v_val_452_);
lean_dec_ref(v_addFn_x3f_451_);
v___x_453_ = lean_apply_2(v_toPure_443_, lean_box(0), v_val_452_);
return v___x_453_;
}
else
{
lean_object* v_type_454_; lean_object* v_u_455_; lean_object* v_semiringInst_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_expectedInst_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_toPure_443_);
v_type_454_ = lean_ctor_get(v_ring_450_, 1);
lean_inc_ref_n(v_type_454_, 3);
v_u_455_ = lean_ctor_get(v_ring_450_, 2);
lean_inc_n(v_u_455_, 2);
v_semiringInst_456_ = lean_ctor_get(v_ring_450_, 4);
lean_inc_ref(v_semiringInst_456_);
lean_dec_ref(v_ring_450_);
v___x_457_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1));
v___x_458_ = lean_box(0);
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v_u_455_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
lean_inc_ref(v___x_459_);
v___x_460_ = l_Lean_mkConst(v___x_457_, v___x_459_);
v___x_461_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3));
v___x_462_ = l_Lean_mkConst(v___x_461_, v___x_459_);
v___x_463_ = l_Lean_mkAppB(v___x_462_, v_type_454_, v_semiringInst_456_);
v_expectedInst_464_ = l_Lean_mkAppB(v___x_460_, v_type_454_, v___x_463_);
v___x_465_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5));
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7));
v___x_467_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_444_, v_inst_445_, v_inst_446_, v_inst_447_, v_type_454_, v_u_455_, v___x_465_, v___x_466_, v_expectedInst_464_);
v___x_468_ = lean_apply_4(v_toBind_448_, lean_box(0), lean_box(0), v___x_467_, v___f_449_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v_toApplicative_474_; lean_object* v_toBind_475_; lean_object* v_getRing_476_; lean_object* v_modifyRing_477_; lean_object* v_toPure_478_; lean_object* v___f_479_; lean_object* v___f_480_; lean_object* v___x_481_; 
v_toApplicative_474_ = lean_ctor_get(v_inst_471_, 0);
v_toBind_475_ = lean_ctor_get(v_inst_471_, 1);
lean_inc_n(v_toBind_475_, 3);
v_getRing_476_ = lean_ctor_get(v_inst_473_, 0);
lean_inc(v_getRing_476_);
v_modifyRing_477_ = lean_ctor_get(v_inst_473_, 1);
lean_inc(v_modifyRing_477_);
lean_dec_ref(v_inst_473_);
v_toPure_478_ = lean_ctor_get(v_toApplicative_474_, 1);
lean_inc_n(v_toPure_478_, 2);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_479_, 0, v_toPure_478_);
lean_closure_set(v___f_479_, 1, v_modifyRing_477_);
lean_closure_set(v___f_479_, 2, v_toBind_475_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_480_, 0, v_toPure_478_);
lean_closure_set(v___f_480_, 1, v_inst_469_);
lean_closure_set(v___f_480_, 2, v_inst_470_);
lean_closure_set(v___f_480_, 3, v_inst_471_);
lean_closure_set(v___f_480_, 4, v_inst_472_);
lean_closure_set(v___f_480_, 5, v_toBind_475_);
lean_closure_set(v___f_480_, 6, v___f_479_);
v___x_481_ = lean_apply_4(v_toBind_475_, lean_box(0), lean_box(0), v_getRing_476_, v___f_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn(lean_object* v_m_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(v_inst_483_, v_inst_484_, v_inst_485_, v_inst_486_, v_inst_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0(lean_object* v_subFn_489_, lean_object* v_s_490_){
_start:
{
lean_object* v_id_491_; lean_object* v_type_492_; lean_object* v_u_493_; lean_object* v_ringInst_494_; lean_object* v_semiringInst_495_; lean_object* v_charInst_x3f_496_; lean_object* v_addFn_x3f_497_; lean_object* v_mulFn_x3f_498_; lean_object* v_negFn_x3f_499_; lean_object* v_powFn_x3f_500_; lean_object* v_intCastFn_x3f_501_; lean_object* v_natCastFn_x3f_502_; lean_object* v_one_x3f_503_; lean_object* v_vars_504_; lean_object* v_varMap_505_; lean_object* v_denote_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
v_id_491_ = lean_ctor_get(v_s_490_, 0);
v_type_492_ = lean_ctor_get(v_s_490_, 1);
v_u_493_ = lean_ctor_get(v_s_490_, 2);
v_ringInst_494_ = lean_ctor_get(v_s_490_, 3);
v_semiringInst_495_ = lean_ctor_get(v_s_490_, 4);
v_charInst_x3f_496_ = lean_ctor_get(v_s_490_, 5);
v_addFn_x3f_497_ = lean_ctor_get(v_s_490_, 6);
v_mulFn_x3f_498_ = lean_ctor_get(v_s_490_, 7);
v_negFn_x3f_499_ = lean_ctor_get(v_s_490_, 9);
v_powFn_x3f_500_ = lean_ctor_get(v_s_490_, 10);
v_intCastFn_x3f_501_ = lean_ctor_get(v_s_490_, 11);
v_natCastFn_x3f_502_ = lean_ctor_get(v_s_490_, 12);
v_one_x3f_503_ = lean_ctor_get(v_s_490_, 13);
v_vars_504_ = lean_ctor_get(v_s_490_, 14);
v_varMap_505_ = lean_ctor_get(v_s_490_, 15);
v_denote_506_ = lean_ctor_get(v_s_490_, 16);
v_isSharedCheck_514_ = !lean_is_exclusive(v_s_490_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v_s_490_, 8);
lean_dec(v_unused_515_);
v___x_508_ = v_s_490_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_denote_506_);
lean_inc(v_varMap_505_);
lean_inc(v_vars_504_);
lean_inc(v_one_x3f_503_);
lean_inc(v_natCastFn_x3f_502_);
lean_inc(v_intCastFn_x3f_501_);
lean_inc(v_powFn_x3f_500_);
lean_inc(v_negFn_x3f_499_);
lean_inc(v_mulFn_x3f_498_);
lean_inc(v_addFn_x3f_497_);
lean_inc(v_charInst_x3f_496_);
lean_inc(v_semiringInst_495_);
lean_inc(v_ringInst_494_);
lean_inc(v_u_493_);
lean_inc(v_type_492_);
lean_inc(v_id_491_);
lean_dec(v_s_490_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v_subFn_489_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 8, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_id_491_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_type_492_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_u_493_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_ringInst_494_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_semiringInst_495_);
lean_ctor_set(v_reuseFailAlloc_513_, 5, v_charInst_x3f_496_);
lean_ctor_set(v_reuseFailAlloc_513_, 6, v_addFn_x3f_497_);
lean_ctor_set(v_reuseFailAlloc_513_, 7, v_mulFn_x3f_498_);
lean_ctor_set(v_reuseFailAlloc_513_, 8, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 9, v_negFn_x3f_499_);
lean_ctor_set(v_reuseFailAlloc_513_, 10, v_powFn_x3f_500_);
lean_ctor_set(v_reuseFailAlloc_513_, 11, v_intCastFn_x3f_501_);
lean_ctor_set(v_reuseFailAlloc_513_, 12, v_natCastFn_x3f_502_);
lean_ctor_set(v_reuseFailAlloc_513_, 13, v_one_x3f_503_);
lean_ctor_set(v_reuseFailAlloc_513_, 14, v_vars_504_);
lean_ctor_set(v_reuseFailAlloc_513_, 15, v_varMap_505_);
lean_ctor_set(v_reuseFailAlloc_513_, 16, v_denote_506_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1(lean_object* v_toPure_516_, lean_object* v_subFn_517_, lean_object* v_____r_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = lean_apply_2(v_toPure_516_, lean_box(0), v_subFn_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2(lean_object* v_toPure_520_, lean_object* v_modifyRing_521_, lean_object* v_toBind_522_, lean_object* v_subFn_523_){
_start:
{
lean_object* v___f_524_; lean_object* v___f_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_inc_ref(v_subFn_523_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_524_, 0, v_subFn_523_);
v___f_525_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_525_, 0, v_toPure_520_);
lean_closure_set(v___f_525_, 1, v_subFn_523_);
v___x_526_ = lean_apply_1(v_modifyRing_521_, v___f_524_);
v___x_527_ = lean_apply_4(v_toBind_522_, lean_box(0), lean_box(0), v___x_526_, v___f_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3(lean_object* v_toPure_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_toBind_550_, lean_object* v___f_551_, lean_object* v_ring_552_){
_start:
{
lean_object* v_subFn_x3f_553_; 
v_subFn_x3f_553_ = lean_ctor_get(v_ring_552_, 8);
if (lean_obj_tag(v_subFn_x3f_553_) == 1)
{
lean_object* v_val_554_; lean_object* v___x_555_; 
lean_inc_ref(v_subFn_x3f_553_);
lean_dec_ref(v_ring_552_);
lean_dec(v___f_551_);
lean_dec(v_toBind_550_);
lean_dec_ref(v_inst_549_);
lean_dec_ref(v_inst_548_);
lean_dec_ref(v_inst_547_);
lean_dec(v_inst_546_);
v_val_554_ = lean_ctor_get(v_subFn_x3f_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref(v_subFn_x3f_553_);
v___x_555_ = lean_apply_2(v_toPure_545_, lean_box(0), v_val_554_);
return v___x_555_;
}
else
{
lean_object* v_type_556_; lean_object* v_u_557_; lean_object* v_ringInst_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_expectedInst_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_toPure_545_);
v_type_556_ = lean_ctor_get(v_ring_552_, 1);
lean_inc_ref_n(v_type_556_, 3);
v_u_557_ = lean_ctor_get(v_ring_552_, 2);
lean_inc_n(v_u_557_, 2);
v_ringInst_558_ = lean_ctor_get(v_ring_552_, 3);
lean_inc_ref(v_ringInst_558_);
lean_dec_ref(v_ring_552_);
v___x_559_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1));
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v_u_557_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
lean_inc_ref(v___x_561_);
v___x_562_ = l_Lean_mkConst(v___x_559_, v___x_561_);
v___x_563_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4));
v___x_564_ = l_Lean_mkConst(v___x_563_, v___x_561_);
v___x_565_ = l_Lean_mkAppB(v___x_564_, v_type_556_, v_ringInst_558_);
v_expectedInst_566_ = l_Lean_mkAppB(v___x_562_, v_type_556_, v___x_565_);
v___x_567_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6));
v___x_568_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8));
v___x_569_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_546_, v_inst_547_, v_inst_548_, v_inst_549_, v_type_556_, v_u_557_, v___x_567_, v___x_568_, v_expectedInst_566_);
v___x_570_ = lean_apply_4(v_toBind_550_, lean_box(0), lean_box(0), v___x_569_, v___f_551_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_){
_start:
{
lean_object* v_toApplicative_576_; lean_object* v_toBind_577_; lean_object* v_getRing_578_; lean_object* v_modifyRing_579_; lean_object* v_toPure_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___x_583_; 
v_toApplicative_576_ = lean_ctor_get(v_inst_573_, 0);
v_toBind_577_ = lean_ctor_get(v_inst_573_, 1);
lean_inc_n(v_toBind_577_, 3);
v_getRing_578_ = lean_ctor_get(v_inst_575_, 0);
lean_inc(v_getRing_578_);
v_modifyRing_579_ = lean_ctor_get(v_inst_575_, 1);
lean_inc(v_modifyRing_579_);
lean_dec_ref(v_inst_575_);
v_toPure_580_ = lean_ctor_get(v_toApplicative_576_, 1);
lean_inc_n(v_toPure_580_, 2);
v___f_581_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_581_, 0, v_toPure_580_);
lean_closure_set(v___f_581_, 1, v_modifyRing_579_);
lean_closure_set(v___f_581_, 2, v_toBind_577_);
v___f_582_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_582_, 0, v_toPure_580_);
lean_closure_set(v___f_582_, 1, v_inst_571_);
lean_closure_set(v___f_582_, 2, v_inst_572_);
lean_closure_set(v___f_582_, 3, v_inst_573_);
lean_closure_set(v___f_582_, 4, v_inst_574_);
lean_closure_set(v___f_582_, 5, v_toBind_577_);
lean_closure_set(v___f_582_, 6, v___f_581_);
v___x_583_ = lean_apply_4(v_toBind_577_, lean_box(0), lean_box(0), v_getRing_578_, v___f_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn(lean_object* v_m_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(v_inst_585_, v_inst_586_, v_inst_587_, v_inst_588_, v_inst_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0(lean_object* v_mulFn_591_, lean_object* v_s_592_){
_start:
{
lean_object* v_id_593_; lean_object* v_type_594_; lean_object* v_u_595_; lean_object* v_ringInst_596_; lean_object* v_semiringInst_597_; lean_object* v_charInst_x3f_598_; lean_object* v_addFn_x3f_599_; lean_object* v_subFn_x3f_600_; lean_object* v_negFn_x3f_601_; lean_object* v_powFn_x3f_602_; lean_object* v_intCastFn_x3f_603_; lean_object* v_natCastFn_x3f_604_; lean_object* v_one_x3f_605_; lean_object* v_vars_606_; lean_object* v_varMap_607_; lean_object* v_denote_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_616_; 
v_id_593_ = lean_ctor_get(v_s_592_, 0);
v_type_594_ = lean_ctor_get(v_s_592_, 1);
v_u_595_ = lean_ctor_get(v_s_592_, 2);
v_ringInst_596_ = lean_ctor_get(v_s_592_, 3);
v_semiringInst_597_ = lean_ctor_get(v_s_592_, 4);
v_charInst_x3f_598_ = lean_ctor_get(v_s_592_, 5);
v_addFn_x3f_599_ = lean_ctor_get(v_s_592_, 6);
v_subFn_x3f_600_ = lean_ctor_get(v_s_592_, 8);
v_negFn_x3f_601_ = lean_ctor_get(v_s_592_, 9);
v_powFn_x3f_602_ = lean_ctor_get(v_s_592_, 10);
v_intCastFn_x3f_603_ = lean_ctor_get(v_s_592_, 11);
v_natCastFn_x3f_604_ = lean_ctor_get(v_s_592_, 12);
v_one_x3f_605_ = lean_ctor_get(v_s_592_, 13);
v_vars_606_ = lean_ctor_get(v_s_592_, 14);
v_varMap_607_ = lean_ctor_get(v_s_592_, 15);
v_denote_608_ = lean_ctor_get(v_s_592_, 16);
v_isSharedCheck_616_ = !lean_is_exclusive(v_s_592_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v_s_592_, 7);
lean_dec(v_unused_617_);
v___x_610_ = v_s_592_;
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_denote_608_);
lean_inc(v_varMap_607_);
lean_inc(v_vars_606_);
lean_inc(v_one_x3f_605_);
lean_inc(v_natCastFn_x3f_604_);
lean_inc(v_intCastFn_x3f_603_);
lean_inc(v_powFn_x3f_602_);
lean_inc(v_negFn_x3f_601_);
lean_inc(v_subFn_x3f_600_);
lean_inc(v_addFn_x3f_599_);
lean_inc(v_charInst_x3f_598_);
lean_inc(v_semiringInst_597_);
lean_inc(v_ringInst_596_);
lean_inc(v_u_595_);
lean_inc(v_type_594_);
lean_inc(v_id_593_);
lean_dec(v_s_592_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v_mulFn_591_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 7, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_id_593_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_type_594_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_u_595_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_ringInst_596_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_semiringInst_597_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_charInst_x3f_598_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_addFn_x3f_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_subFn_x3f_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 9, v_negFn_x3f_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 10, v_powFn_x3f_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 11, v_intCastFn_x3f_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 12, v_natCastFn_x3f_604_);
lean_ctor_set(v_reuseFailAlloc_615_, 13, v_one_x3f_605_);
lean_ctor_set(v_reuseFailAlloc_615_, 14, v_vars_606_);
lean_ctor_set(v_reuseFailAlloc_615_, 15, v_varMap_607_);
lean_ctor_set(v_reuseFailAlloc_615_, 16, v_denote_608_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1(lean_object* v_toPure_618_, lean_object* v_mulFn_619_, lean_object* v_____r_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_apply_2(v_toPure_618_, lean_box(0), v_mulFn_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2(lean_object* v_toPure_622_, lean_object* v_modifyRing_623_, lean_object* v_toBind_624_, lean_object* v_mulFn_625_){
_start:
{
lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_inc_ref(v_mulFn_625_);
v___f_626_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_626_, 0, v_mulFn_625_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_627_, 0, v_toPure_622_);
lean_closure_set(v___f_627_, 1, v_mulFn_625_);
v___x_628_ = lean_apply_1(v_modifyRing_623_, v___f_626_);
v___x_629_ = lean_apply_4(v_toBind_624_, lean_box(0), lean_box(0), v___x_628_, v___f_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3(lean_object* v_toPure_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_toBind_651_, lean_object* v___f_652_, lean_object* v_ring_653_){
_start:
{
lean_object* v_mulFn_x3f_654_; 
v_mulFn_x3f_654_ = lean_ctor_get(v_ring_653_, 7);
if (lean_obj_tag(v_mulFn_x3f_654_) == 1)
{
lean_object* v_val_655_; lean_object* v___x_656_; 
lean_inc_ref(v_mulFn_x3f_654_);
lean_dec_ref(v_ring_653_);
lean_dec(v___f_652_);
lean_dec(v_toBind_651_);
lean_dec_ref(v_inst_650_);
lean_dec_ref(v_inst_649_);
lean_dec_ref(v_inst_648_);
lean_dec(v_inst_647_);
v_val_655_ = lean_ctor_get(v_mulFn_x3f_654_, 0);
lean_inc(v_val_655_);
lean_dec_ref(v_mulFn_x3f_654_);
v___x_656_ = lean_apply_2(v_toPure_646_, lean_box(0), v_val_655_);
return v___x_656_;
}
else
{
lean_object* v_type_657_; lean_object* v_u_658_; lean_object* v_semiringInst_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_expectedInst_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v_toPure_646_);
v_type_657_ = lean_ctor_get(v_ring_653_, 1);
lean_inc_ref_n(v_type_657_, 3);
v_u_658_ = lean_ctor_get(v_ring_653_, 2);
lean_inc_n(v_u_658_, 2);
v_semiringInst_659_ = lean_ctor_get(v_ring_653_, 4);
lean_inc_ref(v_semiringInst_659_);
lean_dec_ref(v_ring_653_);
v___x_660_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1));
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v_u_658_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
lean_inc_ref(v___x_662_);
v___x_663_ = l_Lean_mkConst(v___x_660_, v___x_662_);
v___x_664_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3));
v___x_665_ = l_Lean_mkConst(v___x_664_, v___x_662_);
v___x_666_ = l_Lean_mkAppB(v___x_665_, v_type_657_, v_semiringInst_659_);
v_expectedInst_667_ = l_Lean_mkAppB(v___x_663_, v_type_657_, v___x_666_);
v___x_668_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5));
v___x_669_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7));
v___x_670_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_647_, v_inst_648_, v_inst_649_, v_inst_650_, v_type_657_, v_u_658_, v___x_668_, v___x_669_, v_expectedInst_667_);
v___x_671_ = lean_apply_4(v_toBind_651_, lean_box(0), lean_box(0), v___x_670_, v___f_652_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_inst_676_){
_start:
{
lean_object* v_toApplicative_677_; lean_object* v_toBind_678_; lean_object* v_getRing_679_; lean_object* v_modifyRing_680_; lean_object* v_toPure_681_; lean_object* v___f_682_; lean_object* v___f_683_; lean_object* v___x_684_; 
v_toApplicative_677_ = lean_ctor_get(v_inst_674_, 0);
v_toBind_678_ = lean_ctor_get(v_inst_674_, 1);
lean_inc_n(v_toBind_678_, 3);
v_getRing_679_ = lean_ctor_get(v_inst_676_, 0);
lean_inc(v_getRing_679_);
v_modifyRing_680_ = lean_ctor_get(v_inst_676_, 1);
lean_inc(v_modifyRing_680_);
lean_dec_ref(v_inst_676_);
v_toPure_681_ = lean_ctor_get(v_toApplicative_677_, 1);
lean_inc_n(v_toPure_681_, 2);
v___f_682_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_682_, 0, v_toPure_681_);
lean_closure_set(v___f_682_, 1, v_modifyRing_680_);
lean_closure_set(v___f_682_, 2, v_toBind_678_);
v___f_683_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_683_, 0, v_toPure_681_);
lean_closure_set(v___f_683_, 1, v_inst_672_);
lean_closure_set(v___f_683_, 2, v_inst_673_);
lean_closure_set(v___f_683_, 3, v_inst_674_);
lean_closure_set(v___f_683_, 4, v_inst_675_);
lean_closure_set(v___f_683_, 5, v_toBind_678_);
lean_closure_set(v___f_683_, 6, v___f_682_);
v___x_684_ = lean_apply_4(v_toBind_678_, lean_box(0), lean_box(0), v_getRing_679_, v___f_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn(lean_object* v_m_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(v_inst_686_, v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0(lean_object* v_negFn_692_, lean_object* v_s_693_){
_start:
{
lean_object* v_id_694_; lean_object* v_type_695_; lean_object* v_u_696_; lean_object* v_ringInst_697_; lean_object* v_semiringInst_698_; lean_object* v_charInst_x3f_699_; lean_object* v_addFn_x3f_700_; lean_object* v_mulFn_x3f_701_; lean_object* v_subFn_x3f_702_; lean_object* v_powFn_x3f_703_; lean_object* v_intCastFn_x3f_704_; lean_object* v_natCastFn_x3f_705_; lean_object* v_one_x3f_706_; lean_object* v_vars_707_; lean_object* v_varMap_708_; lean_object* v_denote_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_id_694_ = lean_ctor_get(v_s_693_, 0);
v_type_695_ = lean_ctor_get(v_s_693_, 1);
v_u_696_ = lean_ctor_get(v_s_693_, 2);
v_ringInst_697_ = lean_ctor_get(v_s_693_, 3);
v_semiringInst_698_ = lean_ctor_get(v_s_693_, 4);
v_charInst_x3f_699_ = lean_ctor_get(v_s_693_, 5);
v_addFn_x3f_700_ = lean_ctor_get(v_s_693_, 6);
v_mulFn_x3f_701_ = lean_ctor_get(v_s_693_, 7);
v_subFn_x3f_702_ = lean_ctor_get(v_s_693_, 8);
v_powFn_x3f_703_ = lean_ctor_get(v_s_693_, 10);
v_intCastFn_x3f_704_ = lean_ctor_get(v_s_693_, 11);
v_natCastFn_x3f_705_ = lean_ctor_get(v_s_693_, 12);
v_one_x3f_706_ = lean_ctor_get(v_s_693_, 13);
v_vars_707_ = lean_ctor_get(v_s_693_, 14);
v_varMap_708_ = lean_ctor_get(v_s_693_, 15);
v_denote_709_ = lean_ctor_get(v_s_693_, 16);
v_isSharedCheck_717_ = !lean_is_exclusive(v_s_693_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v_s_693_, 9);
lean_dec(v_unused_718_);
v___x_711_ = v_s_693_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_denote_709_);
lean_inc(v_varMap_708_);
lean_inc(v_vars_707_);
lean_inc(v_one_x3f_706_);
lean_inc(v_natCastFn_x3f_705_);
lean_inc(v_intCastFn_x3f_704_);
lean_inc(v_powFn_x3f_703_);
lean_inc(v_subFn_x3f_702_);
lean_inc(v_mulFn_x3f_701_);
lean_inc(v_addFn_x3f_700_);
lean_inc(v_charInst_x3f_699_);
lean_inc(v_semiringInst_698_);
lean_inc(v_ringInst_697_);
lean_inc(v_u_696_);
lean_inc(v_type_695_);
lean_inc(v_id_694_);
lean_dec(v_s_693_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v_negFn_692_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 9, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_id_694_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_type_695_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_u_696_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_ringInst_697_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_semiringInst_698_);
lean_ctor_set(v_reuseFailAlloc_716_, 5, v_charInst_x3f_699_);
lean_ctor_set(v_reuseFailAlloc_716_, 6, v_addFn_x3f_700_);
lean_ctor_set(v_reuseFailAlloc_716_, 7, v_mulFn_x3f_701_);
lean_ctor_set(v_reuseFailAlloc_716_, 8, v_subFn_x3f_702_);
lean_ctor_set(v_reuseFailAlloc_716_, 9, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 10, v_powFn_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_716_, 11, v_intCastFn_x3f_704_);
lean_ctor_set(v_reuseFailAlloc_716_, 12, v_natCastFn_x3f_705_);
lean_ctor_set(v_reuseFailAlloc_716_, 13, v_one_x3f_706_);
lean_ctor_set(v_reuseFailAlloc_716_, 14, v_vars_707_);
lean_ctor_set(v_reuseFailAlloc_716_, 15, v_varMap_708_);
lean_ctor_set(v_reuseFailAlloc_716_, 16, v_denote_709_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1(lean_object* v_toPure_719_, lean_object* v_negFn_720_, lean_object* v_____r_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_apply_2(v_toPure_719_, lean_box(0), v_negFn_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2(lean_object* v_toPure_723_, lean_object* v_modifyRing_724_, lean_object* v_toBind_725_, lean_object* v_negFn_726_){
_start:
{
lean_object* v___f_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_inc_ref(v_negFn_726_);
v___f_727_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_727_, 0, v_negFn_726_);
v___f_728_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_728_, 0, v_toPure_723_);
lean_closure_set(v___f_728_, 1, v_negFn_726_);
v___x_729_ = lean_apply_1(v_modifyRing_724_, v___f_727_);
v___x_730_ = lean_apply_4(v_toBind_725_, lean_box(0), lean_box(0), v___x_729_, v___f_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3(lean_object* v_toPure_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_toBind_749_, lean_object* v___f_750_, lean_object* v_ring_751_){
_start:
{
lean_object* v_negFn_x3f_752_; 
v_negFn_x3f_752_ = lean_ctor_get(v_ring_751_, 9);
if (lean_obj_tag(v_negFn_x3f_752_) == 1)
{
lean_object* v_val_753_; lean_object* v___x_754_; 
lean_inc_ref(v_negFn_x3f_752_);
lean_dec_ref(v_ring_751_);
lean_dec(v___f_750_);
lean_dec(v_toBind_749_);
lean_dec_ref(v_inst_748_);
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
lean_dec(v_inst_745_);
v_val_753_ = lean_ctor_get(v_negFn_x3f_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref(v_negFn_x3f_752_);
v___x_754_ = lean_apply_2(v_toPure_744_, lean_box(0), v_val_753_);
return v___x_754_;
}
else
{
lean_object* v_type_755_; lean_object* v_u_756_; lean_object* v_ringInst_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_expectedInst_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v_toPure_744_);
v_type_755_ = lean_ctor_get(v_ring_751_, 1);
lean_inc_ref_n(v_type_755_, 2);
v_u_756_ = lean_ctor_get(v_ring_751_, 2);
lean_inc_n(v_u_756_, 2);
v_ringInst_757_ = lean_ctor_get(v_ring_751_, 3);
lean_inc_ref(v_ringInst_757_);
lean_dec_ref(v_ring_751_);
v___x_758_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1));
v___x_759_ = lean_box(0);
v___x_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_760_, 0, v_u_756_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_mkConst(v___x_758_, v___x_760_);
v_expectedInst_762_ = l_Lean_mkAppB(v___x_761_, v_type_755_, v_ringInst_757_);
v___x_763_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3));
v___x_764_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5));
v___x_765_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(v_inst_745_, v_inst_746_, v_inst_747_, v_inst_748_, v_type_755_, v_u_756_, v___x_763_, v___x_764_, v_expectedInst_762_);
v___x_766_ = lean_apply_4(v_toBind_749_, lean_box(0), lean_box(0), v___x_765_, v___f_750_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(lean_object* v_inst_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_){
_start:
{
lean_object* v_toApplicative_772_; lean_object* v_toBind_773_; lean_object* v_getRing_774_; lean_object* v_modifyRing_775_; lean_object* v_toPure_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___x_779_; 
v_toApplicative_772_ = lean_ctor_get(v_inst_769_, 0);
v_toBind_773_ = lean_ctor_get(v_inst_769_, 1);
lean_inc_n(v_toBind_773_, 3);
v_getRing_774_ = lean_ctor_get(v_inst_771_, 0);
lean_inc(v_getRing_774_);
v_modifyRing_775_ = lean_ctor_get(v_inst_771_, 1);
lean_inc(v_modifyRing_775_);
lean_dec_ref(v_inst_771_);
v_toPure_776_ = lean_ctor_get(v_toApplicative_772_, 1);
lean_inc_n(v_toPure_776_, 2);
v___f_777_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_777_, 0, v_toPure_776_);
lean_closure_set(v___f_777_, 1, v_modifyRing_775_);
lean_closure_set(v___f_777_, 2, v_toBind_773_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_778_, 0, v_toPure_776_);
lean_closure_set(v___f_778_, 1, v_inst_767_);
lean_closure_set(v___f_778_, 2, v_inst_768_);
lean_closure_set(v___f_778_, 3, v_inst_769_);
lean_closure_set(v___f_778_, 4, v_inst_770_);
lean_closure_set(v___f_778_, 5, v_toBind_773_);
lean_closure_set(v___f_778_, 6, v___f_777_);
v___x_779_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v_getRing_774_, v___f_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn(lean_object* v_m_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_inst_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(v_inst_781_, v_inst_782_, v_inst_783_, v_inst_784_, v_inst_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0(lean_object* v_powFn_787_, lean_object* v_s_788_){
_start:
{
lean_object* v_id_789_; lean_object* v_type_790_; lean_object* v_u_791_; lean_object* v_ringInst_792_; lean_object* v_semiringInst_793_; lean_object* v_charInst_x3f_794_; lean_object* v_addFn_x3f_795_; lean_object* v_mulFn_x3f_796_; lean_object* v_subFn_x3f_797_; lean_object* v_negFn_x3f_798_; lean_object* v_intCastFn_x3f_799_; lean_object* v_natCastFn_x3f_800_; lean_object* v_one_x3f_801_; lean_object* v_vars_802_; lean_object* v_varMap_803_; lean_object* v_denote_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_id_789_ = lean_ctor_get(v_s_788_, 0);
v_type_790_ = lean_ctor_get(v_s_788_, 1);
v_u_791_ = lean_ctor_get(v_s_788_, 2);
v_ringInst_792_ = lean_ctor_get(v_s_788_, 3);
v_semiringInst_793_ = lean_ctor_get(v_s_788_, 4);
v_charInst_x3f_794_ = lean_ctor_get(v_s_788_, 5);
v_addFn_x3f_795_ = lean_ctor_get(v_s_788_, 6);
v_mulFn_x3f_796_ = lean_ctor_get(v_s_788_, 7);
v_subFn_x3f_797_ = lean_ctor_get(v_s_788_, 8);
v_negFn_x3f_798_ = lean_ctor_get(v_s_788_, 9);
v_intCastFn_x3f_799_ = lean_ctor_get(v_s_788_, 11);
v_natCastFn_x3f_800_ = lean_ctor_get(v_s_788_, 12);
v_one_x3f_801_ = lean_ctor_get(v_s_788_, 13);
v_vars_802_ = lean_ctor_get(v_s_788_, 14);
v_varMap_803_ = lean_ctor_get(v_s_788_, 15);
v_denote_804_ = lean_ctor_get(v_s_788_, 16);
v_isSharedCheck_812_ = !lean_is_exclusive(v_s_788_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_s_788_, 10);
lean_dec(v_unused_813_);
v___x_806_ = v_s_788_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_denote_804_);
lean_inc(v_varMap_803_);
lean_inc(v_vars_802_);
lean_inc(v_one_x3f_801_);
lean_inc(v_natCastFn_x3f_800_);
lean_inc(v_intCastFn_x3f_799_);
lean_inc(v_negFn_x3f_798_);
lean_inc(v_subFn_x3f_797_);
lean_inc(v_mulFn_x3f_796_);
lean_inc(v_addFn_x3f_795_);
lean_inc(v_charInst_x3f_794_);
lean_inc(v_semiringInst_793_);
lean_inc(v_ringInst_792_);
lean_inc(v_u_791_);
lean_inc(v_type_790_);
lean_inc(v_id_789_);
lean_dec(v_s_788_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_powFn_787_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 10, v___x_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_id_789_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_type_790_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_u_791_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v_ringInst_792_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v_semiringInst_793_);
lean_ctor_set(v_reuseFailAlloc_811_, 5, v_charInst_x3f_794_);
lean_ctor_set(v_reuseFailAlloc_811_, 6, v_addFn_x3f_795_);
lean_ctor_set(v_reuseFailAlloc_811_, 7, v_mulFn_x3f_796_);
lean_ctor_set(v_reuseFailAlloc_811_, 8, v_subFn_x3f_797_);
lean_ctor_set(v_reuseFailAlloc_811_, 9, v_negFn_x3f_798_);
lean_ctor_set(v_reuseFailAlloc_811_, 10, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_811_, 11, v_intCastFn_x3f_799_);
lean_ctor_set(v_reuseFailAlloc_811_, 12, v_natCastFn_x3f_800_);
lean_ctor_set(v_reuseFailAlloc_811_, 13, v_one_x3f_801_);
lean_ctor_set(v_reuseFailAlloc_811_, 14, v_vars_802_);
lean_ctor_set(v_reuseFailAlloc_811_, 15, v_varMap_803_);
lean_ctor_set(v_reuseFailAlloc_811_, 16, v_denote_804_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1(lean_object* v_toPure_814_, lean_object* v_powFn_815_, lean_object* v_____r_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = lean_apply_2(v_toPure_814_, lean_box(0), v_powFn_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2(lean_object* v_toPure_818_, lean_object* v_modifyRing_819_, lean_object* v_toBind_820_, lean_object* v_powFn_821_){
_start:
{
lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_inc_ref(v_powFn_821_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_822_, 0, v_powFn_821_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_823_, 0, v_toPure_818_);
lean_closure_set(v___f_823_, 1, v_powFn_821_);
v___x_824_ = lean_apply_1(v_modifyRing_819_, v___f_822_);
v___x_825_ = lean_apply_4(v_toBind_820_, lean_box(0), lean_box(0), v___x_824_, v___f_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3(lean_object* v_toPure_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_toBind_831_, lean_object* v___f_832_, lean_object* v_ring_833_){
_start:
{
lean_object* v_powFn_x3f_834_; 
v_powFn_x3f_834_ = lean_ctor_get(v_ring_833_, 10);
if (lean_obj_tag(v_powFn_x3f_834_) == 1)
{
lean_object* v_val_835_; lean_object* v___x_836_; 
lean_inc_ref(v_powFn_x3f_834_);
lean_dec_ref(v_ring_833_);
lean_dec(v___f_832_);
lean_dec(v_toBind_831_);
lean_dec_ref(v_inst_830_);
lean_dec_ref(v_inst_829_);
lean_dec_ref(v_inst_828_);
lean_dec(v_inst_827_);
v_val_835_ = lean_ctor_get(v_powFn_x3f_834_, 0);
lean_inc(v_val_835_);
lean_dec_ref(v_powFn_x3f_834_);
v___x_836_ = lean_apply_2(v_toPure_826_, lean_box(0), v_val_835_);
return v___x_836_;
}
else
{
lean_object* v_type_837_; lean_object* v_u_838_; lean_object* v_semiringInst_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_toPure_826_);
v_type_837_ = lean_ctor_get(v_ring_833_, 1);
lean_inc_ref(v_type_837_);
v_u_838_ = lean_ctor_get(v_ring_833_, 2);
lean_inc(v_u_838_);
v_semiringInst_839_ = lean_ctor_get(v_ring_833_, 4);
lean_inc_ref(v_semiringInst_839_);
lean_dec_ref(v_ring_833_);
v___x_840_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_827_, v_inst_828_, v_inst_829_, v_inst_830_, v_u_838_, v_type_837_, v_semiringInst_839_);
v___x_841_ = lean_apply_4(v_toBind_831_, lean_box(0), lean_box(0), v___x_840_, v___f_832_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_){
_start:
{
lean_object* v_toApplicative_847_; lean_object* v_toBind_848_; lean_object* v_getRing_849_; lean_object* v_modifyRing_850_; lean_object* v_toPure_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; 
v_toApplicative_847_ = lean_ctor_get(v_inst_844_, 0);
v_toBind_848_ = lean_ctor_get(v_inst_844_, 1);
lean_inc_n(v_toBind_848_, 3);
v_getRing_849_ = lean_ctor_get(v_inst_846_, 0);
lean_inc(v_getRing_849_);
v_modifyRing_850_ = lean_ctor_get(v_inst_846_, 1);
lean_inc(v_modifyRing_850_);
lean_dec_ref(v_inst_846_);
v_toPure_851_ = lean_ctor_get(v_toApplicative_847_, 1);
lean_inc_n(v_toPure_851_, 2);
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_852_, 0, v_toPure_851_);
lean_closure_set(v___f_852_, 1, v_modifyRing_850_);
lean_closure_set(v___f_852_, 2, v_toBind_848_);
v___f_853_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_853_, 0, v_toPure_851_);
lean_closure_set(v___f_853_, 1, v_inst_842_);
lean_closure_set(v___f_853_, 2, v_inst_843_);
lean_closure_set(v___f_853_, 3, v_inst_844_);
lean_closure_set(v___f_853_, 4, v_inst_845_);
lean_closure_set(v___f_853_, 5, v_toBind_848_);
lean_closure_set(v___f_853_, 6, v___f_852_);
v___x_854_ = lean_apply_4(v_toBind_848_, lean_box(0), lean_box(0), v_getRing_849_, v___f_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn(lean_object* v_m_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_inst_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_inst_859_, v_inst_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_862_, lean_object* v_s_863_){
_start:
{
lean_object* v_id_864_; lean_object* v_type_865_; lean_object* v_u_866_; lean_object* v_ringInst_867_; lean_object* v_semiringInst_868_; lean_object* v_charInst_x3f_869_; lean_object* v_addFn_x3f_870_; lean_object* v_mulFn_x3f_871_; lean_object* v_subFn_x3f_872_; lean_object* v_negFn_x3f_873_; lean_object* v_powFn_x3f_874_; lean_object* v_natCastFn_x3f_875_; lean_object* v_one_x3f_876_; lean_object* v_vars_877_; lean_object* v_varMap_878_; lean_object* v_denote_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_887_; 
v_id_864_ = lean_ctor_get(v_s_863_, 0);
v_type_865_ = lean_ctor_get(v_s_863_, 1);
v_u_866_ = lean_ctor_get(v_s_863_, 2);
v_ringInst_867_ = lean_ctor_get(v_s_863_, 3);
v_semiringInst_868_ = lean_ctor_get(v_s_863_, 4);
v_charInst_x3f_869_ = lean_ctor_get(v_s_863_, 5);
v_addFn_x3f_870_ = lean_ctor_get(v_s_863_, 6);
v_mulFn_x3f_871_ = lean_ctor_get(v_s_863_, 7);
v_subFn_x3f_872_ = lean_ctor_get(v_s_863_, 8);
v_negFn_x3f_873_ = lean_ctor_get(v_s_863_, 9);
v_powFn_x3f_874_ = lean_ctor_get(v_s_863_, 10);
v_natCastFn_x3f_875_ = lean_ctor_get(v_s_863_, 12);
v_one_x3f_876_ = lean_ctor_get(v_s_863_, 13);
v_vars_877_ = lean_ctor_get(v_s_863_, 14);
v_varMap_878_ = lean_ctor_get(v_s_863_, 15);
v_denote_879_ = lean_ctor_get(v_s_863_, 16);
v_isSharedCheck_887_ = !lean_is_exclusive(v_s_863_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_s_863_, 11);
lean_dec(v_unused_888_);
v___x_881_ = v_s_863_;
v_isShared_882_ = v_isSharedCheck_887_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_denote_879_);
lean_inc(v_varMap_878_);
lean_inc(v_vars_877_);
lean_inc(v_one_x3f_876_);
lean_inc(v_natCastFn_x3f_875_);
lean_inc(v_powFn_x3f_874_);
lean_inc(v_negFn_x3f_873_);
lean_inc(v_subFn_x3f_872_);
lean_inc(v_mulFn_x3f_871_);
lean_inc(v_addFn_x3f_870_);
lean_inc(v_charInst_x3f_869_);
lean_inc(v_semiringInst_868_);
lean_inc(v_ringInst_867_);
lean_inc(v_u_866_);
lean_inc(v_type_865_);
lean_inc(v_id_864_);
lean_dec(v_s_863_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_887_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v_intCastFn_862_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 11, v___x_883_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_id_864_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_type_865_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_u_866_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_ringInst_867_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_semiringInst_868_);
lean_ctor_set(v_reuseFailAlloc_886_, 5, v_charInst_x3f_869_);
lean_ctor_set(v_reuseFailAlloc_886_, 6, v_addFn_x3f_870_);
lean_ctor_set(v_reuseFailAlloc_886_, 7, v_mulFn_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_886_, 8, v_subFn_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_886_, 9, v_negFn_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_886_, 10, v_powFn_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_886_, 11, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_886_, 12, v_natCastFn_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_886_, 13, v_one_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_886_, 14, v_vars_877_);
lean_ctor_set(v_reuseFailAlloc_886_, 15, v_varMap_878_);
lean_ctor_set(v_reuseFailAlloc_886_, 16, v_denote_879_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1(lean_object* v_toPure_889_, lean_object* v_intCastFn_890_, lean_object* v_____r_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_apply_2(v_toPure_889_, lean_box(0), v_intCastFn_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2(lean_object* v_toPure_893_, lean_object* v_modifyRing_894_, lean_object* v_toBind_895_, lean_object* v_intCastFn_896_){
_start:
{
lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
lean_inc_ref(v_intCastFn_896_);
v___f_897_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_897_, 0, v_intCastFn_896_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_898_, 0, v_toPure_893_);
lean_closure_set(v___f_898_, 1, v_intCastFn_896_);
v___x_899_ = lean_apply_1(v_modifyRing_894_, v___f_897_);
v___x_900_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_899_, v___f_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3(lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v_type_904_, lean_object* v_canonExpr_905_, lean_object* v_toBind_906_, lean_object* v___f_907_, lean_object* v_inst_908_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_909_ = l_Lean_Name_mkStr2(v___x_901_, v___x_902_);
v___x_910_ = l_Lean_mkConst(v___x_909_, v___x_903_);
v___x_911_ = l_Lean_mkAppB(v___x_910_, v_type_904_, v_inst_908_);
v___x_912_ = lean_apply_1(v_canonExpr_905_, v___x_911_);
v___x_913_ = lean_apply_4(v_toBind_906_, lean_box(0), lean_box(0), v___x_912_, v___f_907_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7(lean_object* v_toPure_919_, lean_object* v_inst_x27_920_, lean_object* v_toBind_921_, lean_object* v___f_922_, lean_object* v___f_923_, lean_object* v_inst_924_, lean_object* v_____do__lift_925_){
_start:
{
if (lean_obj_tag(v_____do__lift_925_) == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_inst_924_);
lean_dec(v___f_923_);
v___x_926_ = lean_apply_2(v_toPure_919_, lean_box(0), v_inst_x27_920_);
v___x_927_ = lean_apply_4(v_toBind_921_, lean_box(0), lean_box(0), v___x_926_, v___f_922_);
return v___x_927_;
}
else
{
lean_object* v_val_928_; lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v___f_922_);
v_val_928_ = lean_ctor_get(v_____do__lift_925_, 0);
lean_inc_n(v_val_928_, 2);
lean_dec_ref(v_____do__lift_925_);
lean_inc(v_toBind_921_);
v___f_929_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_929_, 0, v_toPure_919_);
lean_closure_set(v___f_929_, 1, v_val_928_);
lean_closure_set(v___f_929_, 2, v_toBind_921_);
lean_closure_set(v___f_929_, 3, v___f_923_);
v___x_930_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2));
v___x_931_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_931_, 0, v___x_930_);
lean_closure_set(v___x_931_, 1, v_val_928_);
lean_closure_set(v___x_931_, 2, v_inst_x27_920_);
v___x_932_ = lean_apply_2(v_inst_924_, lean_box(0), v___x_931_);
v___x_933_ = lean_apply_4(v_toBind_921_, lean_box(0), lean_box(0), v___x_932_, v___f_929_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4(lean_object* v_toPure_943_, lean_object* v_inst_944_, lean_object* v_toBind_945_, lean_object* v___f_946_, lean_object* v_inst_947_, lean_object* v_ring_948_){
_start:
{
lean_object* v_intCastFn_x3f_949_; 
v_intCastFn_x3f_949_ = lean_ctor_get(v_ring_948_, 11);
if (lean_obj_tag(v_intCastFn_x3f_949_) == 1)
{
lean_object* v_val_950_; lean_object* v___x_951_; 
lean_inc_ref(v_intCastFn_x3f_949_);
lean_dec_ref(v_ring_948_);
lean_dec(v_inst_947_);
lean_dec(v___f_946_);
lean_dec(v_toBind_945_);
lean_dec_ref(v_inst_944_);
v_val_950_ = lean_ctor_get(v_intCastFn_x3f_949_, 0);
lean_inc(v_val_950_);
lean_dec_ref(v_intCastFn_x3f_949_);
v___x_951_ = lean_apply_2(v_toPure_943_, lean_box(0), v_val_950_);
return v___x_951_;
}
else
{
lean_object* v_type_952_; lean_object* v_u_953_; lean_object* v_ringInst_954_; lean_object* v_canonExpr_955_; lean_object* v_synthInstance_x3f_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_977_; 
v_type_952_ = lean_ctor_get(v_ring_948_, 1);
lean_inc_ref(v_type_952_);
v_u_953_ = lean_ctor_get(v_ring_948_, 2);
lean_inc(v_u_953_);
v_ringInst_954_ = lean_ctor_get(v_ring_948_, 3);
lean_inc_ref(v_ringInst_954_);
lean_dec_ref(v_ring_948_);
v_canonExpr_955_ = lean_ctor_get(v_inst_944_, 0);
v_synthInstance_x3f_956_ = lean_ctor_get(v_inst_944_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_inst_944_);
if (v_isSharedCheck_977_ == 0)
{
v___x_958_ = v_inst_944_;
v_isShared_959_ = v_isSharedCheck_977_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_synthInstance_x3f_956_);
lean_inc(v_canonExpr_955_);
lean_dec(v_inst_944_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_977_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_960_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0));
v___x_961_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1));
v___x_962_ = lean_box(0);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 1);
lean_ctor_set(v___x_958_, 1, v___x_962_);
lean_ctor_set(v___x_958_, 0, v_u_953_);
v___x_964_ = v___x_958_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_u_953_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_962_);
v___x_964_ = v_reuseFailAlloc_976_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; lean_object* v_inst_x27_966_; lean_object* v___x_967_; lean_object* v___f_968_; lean_object* v___f_969_; lean_object* v___f_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_instType_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref_n(v___x_964_, 2);
v___x_965_ = l_Lean_mkConst(v___x_961_, v___x_964_);
lean_inc_ref_n(v_type_952_, 2);
v_inst_x27_966_ = l_Lean_mkAppB(v___x_965_, v_type_952_, v_ringInst_954_);
v___x_967_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_945_, 2);
v___f_968_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_968_, 0, v___x_967_);
lean_closure_set(v___f_968_, 1, v___x_960_);
lean_closure_set(v___f_968_, 2, v___x_964_);
lean_closure_set(v___f_968_, 3, v_type_952_);
lean_closure_set(v___f_968_, 4, v_canonExpr_955_);
lean_closure_set(v___f_968_, 5, v_toBind_945_);
lean_closure_set(v___f_968_, 6, v___f_946_);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_969_, 0, v___f_968_);
lean_inc_ref(v___f_969_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_970_, 0, v_toPure_943_);
lean_closure_set(v___f_970_, 1, v_inst_x27_966_);
lean_closure_set(v___f_970_, 2, v_toBind_945_);
lean_closure_set(v___f_970_, 3, v___f_969_);
lean_closure_set(v___f_970_, 4, v___f_969_);
lean_closure_set(v___f_970_, 5, v_inst_947_);
v___x_971_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3));
v___x_972_ = l_Lean_mkConst(v___x_971_, v___x_964_);
v_instType_973_ = l_Lean_Expr_app___override(v___x_972_, v_type_952_);
v___x_974_ = lean_apply_1(v_synthInstance_x3f_956_, v_instType_973_);
v___x_975_ = lean_apply_4(v_toBind_945_, lean_box(0), lean_box(0), v___x_974_, v___f_970_);
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_inst_981_){
_start:
{
lean_object* v_toApplicative_982_; lean_object* v_toBind_983_; lean_object* v_getRing_984_; lean_object* v_modifyRing_985_; lean_object* v_toPure_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___x_989_; 
v_toApplicative_982_ = lean_ctor_get(v_inst_979_, 0);
lean_inc_ref(v_toApplicative_982_);
v_toBind_983_ = lean_ctor_get(v_inst_979_, 1);
lean_inc_n(v_toBind_983_, 3);
lean_dec_ref(v_inst_979_);
v_getRing_984_ = lean_ctor_get(v_inst_981_, 0);
lean_inc(v_getRing_984_);
v_modifyRing_985_ = lean_ctor_get(v_inst_981_, 1);
lean_inc(v_modifyRing_985_);
lean_dec_ref(v_inst_981_);
v_toPure_986_ = lean_ctor_get(v_toApplicative_982_, 1);
lean_inc_n(v_toPure_986_, 2);
lean_dec_ref(v_toApplicative_982_);
v___f_987_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_987_, 0, v_toPure_986_);
lean_closure_set(v___f_987_, 1, v_modifyRing_985_);
lean_closure_set(v___f_987_, 2, v_toBind_983_);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_988_, 0, v_toPure_986_);
lean_closure_set(v___f_988_, 1, v_inst_980_);
lean_closure_set(v___f_988_, 2, v_toBind_983_);
lean_closure_set(v___f_988_, 3, v___f_987_);
lean_closure_set(v___f_988_, 4, v_inst_978_);
v___x_989_ = lean_apply_4(v_toBind_983_, lean_box(0), lean_box(0), v_getRing_984_, v___f_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn(lean_object* v_m_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(v_inst_991_, v_inst_992_, v_inst_993_, v_inst_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_996_, lean_object* v_s_997_){
_start:
{
lean_object* v_id_998_; lean_object* v_type_999_; lean_object* v_u_1000_; lean_object* v_ringInst_1001_; lean_object* v_semiringInst_1002_; lean_object* v_charInst_x3f_1003_; lean_object* v_addFn_x3f_1004_; lean_object* v_mulFn_x3f_1005_; lean_object* v_subFn_x3f_1006_; lean_object* v_negFn_x3f_1007_; lean_object* v_powFn_x3f_1008_; lean_object* v_intCastFn_x3f_1009_; lean_object* v_one_x3f_1010_; lean_object* v_vars_1011_; lean_object* v_varMap_1012_; lean_object* v_denote_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1021_; 
v_id_998_ = lean_ctor_get(v_s_997_, 0);
v_type_999_ = lean_ctor_get(v_s_997_, 1);
v_u_1000_ = lean_ctor_get(v_s_997_, 2);
v_ringInst_1001_ = lean_ctor_get(v_s_997_, 3);
v_semiringInst_1002_ = lean_ctor_get(v_s_997_, 4);
v_charInst_x3f_1003_ = lean_ctor_get(v_s_997_, 5);
v_addFn_x3f_1004_ = lean_ctor_get(v_s_997_, 6);
v_mulFn_x3f_1005_ = lean_ctor_get(v_s_997_, 7);
v_subFn_x3f_1006_ = lean_ctor_get(v_s_997_, 8);
v_negFn_x3f_1007_ = lean_ctor_get(v_s_997_, 9);
v_powFn_x3f_1008_ = lean_ctor_get(v_s_997_, 10);
v_intCastFn_x3f_1009_ = lean_ctor_get(v_s_997_, 11);
v_one_x3f_1010_ = lean_ctor_get(v_s_997_, 13);
v_vars_1011_ = lean_ctor_get(v_s_997_, 14);
v_varMap_1012_ = lean_ctor_get(v_s_997_, 15);
v_denote_1013_ = lean_ctor_get(v_s_997_, 16);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_s_997_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_s_997_, 12);
lean_dec(v_unused_1022_);
v___x_1015_ = v_s_997_;
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_denote_1013_);
lean_inc(v_varMap_1012_);
lean_inc(v_vars_1011_);
lean_inc(v_one_x3f_1010_);
lean_inc(v_intCastFn_x3f_1009_);
lean_inc(v_powFn_x3f_1008_);
lean_inc(v_negFn_x3f_1007_);
lean_inc(v_subFn_x3f_1006_);
lean_inc(v_mulFn_x3f_1005_);
lean_inc(v_addFn_x3f_1004_);
lean_inc(v_charInst_x3f_1003_);
lean_inc(v_semiringInst_1002_);
lean_inc(v_ringInst_1001_);
lean_inc(v_u_1000_);
lean_inc(v_type_999_);
lean_inc(v_id_998_);
lean_dec(v_s_997_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_natCastFn_996_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 12, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_id_998_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_type_999_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_u_1000_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_ringInst_1001_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_semiringInst_1002_);
lean_ctor_set(v_reuseFailAlloc_1020_, 5, v_charInst_x3f_1003_);
lean_ctor_set(v_reuseFailAlloc_1020_, 6, v_addFn_x3f_1004_);
lean_ctor_set(v_reuseFailAlloc_1020_, 7, v_mulFn_x3f_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 8, v_subFn_x3f_1006_);
lean_ctor_set(v_reuseFailAlloc_1020_, 9, v_negFn_x3f_1007_);
lean_ctor_set(v_reuseFailAlloc_1020_, 10, v_powFn_x3f_1008_);
lean_ctor_set(v_reuseFailAlloc_1020_, 11, v_intCastFn_x3f_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 12, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1020_, 13, v_one_x3f_1010_);
lean_ctor_set(v_reuseFailAlloc_1020_, 14, v_vars_1011_);
lean_ctor_set(v_reuseFailAlloc_1020_, 15, v_varMap_1012_);
lean_ctor_set(v_reuseFailAlloc_1020_, 16, v_denote_1013_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1023_, lean_object* v_natCastFn_1024_, lean_object* v_____r_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_apply_2(v_toPure_1023_, lean_box(0), v_natCastFn_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1027_, lean_object* v_modifyRing_1028_, lean_object* v_toBind_1029_, lean_object* v_natCastFn_1030_){
_start:
{
lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_inc_ref(v_natCastFn_1030_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1031_, 0, v_natCastFn_1030_);
v___f_1032_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1032_, 0, v_toPure_1027_);
lean_closure_set(v___f_1032_, 1, v_natCastFn_1030_);
v___x_1033_ = lean_apply_1(v_modifyRing_1028_, v___f_1031_);
v___x_1034_ = lean_apply_4(v_toBind_1029_, lean_box(0), lean_box(0), v___x_1033_, v___f_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_toBind_1039_, lean_object* v___f_1040_, lean_object* v_ring_1041_){
_start:
{
lean_object* v_natCastFn_x3f_1042_; 
v_natCastFn_x3f_1042_ = lean_ctor_get(v_ring_1041_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1042_) == 1)
{
lean_object* v_val_1043_; lean_object* v___x_1044_; 
lean_inc_ref(v_natCastFn_x3f_1042_);
lean_dec_ref(v_ring_1041_);
lean_dec(v___f_1040_);
lean_dec(v_toBind_1039_);
lean_dec_ref(v_inst_1038_);
lean_dec_ref(v_inst_1037_);
lean_dec(v_inst_1036_);
v_val_1043_ = lean_ctor_get(v_natCastFn_x3f_1042_, 0);
lean_inc(v_val_1043_);
lean_dec_ref(v_natCastFn_x3f_1042_);
v___x_1044_ = lean_apply_2(v_toPure_1035_, lean_box(0), v_val_1043_);
return v___x_1044_;
}
else
{
lean_object* v_type_1045_; lean_object* v_u_1046_; lean_object* v_semiringInst_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v_toPure_1035_);
v_type_1045_ = lean_ctor_get(v_ring_1041_, 1);
lean_inc_ref(v_type_1045_);
v_u_1046_ = lean_ctor_get(v_ring_1041_, 2);
lean_inc(v_u_1046_);
v_semiringInst_1047_ = lean_ctor_get(v_ring_1041_, 4);
lean_inc_ref(v_semiringInst_1047_);
lean_dec_ref(v_ring_1041_);
v___x_1048_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_1036_, v_inst_1037_, v_inst_1038_, v_u_1046_, v_type_1045_, v_semiringInst_1047_);
v___x_1049_ = lean_apply_4(v_toBind_1039_, lean_box(0), lean_box(0), v___x_1048_, v___f_1040_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_){
_start:
{
lean_object* v_toApplicative_1054_; lean_object* v_toBind_1055_; lean_object* v_getRing_1056_; lean_object* v_modifyRing_1057_; lean_object* v_toPure_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; 
v_toApplicative_1054_ = lean_ctor_get(v_inst_1051_, 0);
v_toBind_1055_ = lean_ctor_get(v_inst_1051_, 1);
lean_inc_n(v_toBind_1055_, 3);
v_getRing_1056_ = lean_ctor_get(v_inst_1053_, 0);
lean_inc(v_getRing_1056_);
v_modifyRing_1057_ = lean_ctor_get(v_inst_1053_, 1);
lean_inc(v_modifyRing_1057_);
lean_dec_ref(v_inst_1053_);
v_toPure_1058_ = lean_ctor_get(v_toApplicative_1054_, 1);
lean_inc_n(v_toPure_1058_, 2);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1059_, 0, v_toPure_1058_);
lean_closure_set(v___f_1059_, 1, v_modifyRing_1057_);
lean_closure_set(v___f_1059_, 2, v_toBind_1055_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1060_, 0, v_toPure_1058_);
lean_closure_set(v___f_1060_, 1, v_inst_1050_);
lean_closure_set(v___f_1060_, 2, v_inst_1051_);
lean_closure_set(v___f_1060_, 3, v_inst_1052_);
lean_closure_set(v___f_1060_, 4, v_toBind_1055_);
lean_closure_set(v___f_1060_, 5, v___f_1059_);
v___x_1061_ = lean_apply_4(v_toBind_1055_, lean_box(0), lean_box(0), v_getRing_1056_, v___f_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn(lean_object* v_m_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(v_inst_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_1068_; lean_object* v_n_1069_; 
v___x_1068_ = lean_unsigned_to_nat(1u);
v_n_1069_ = l_Lean_mkRawNatLit(v___x_1068_);
return v_n_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object* v_inst_1080_, lean_object* v_u_1081_, lean_object* v_type_1082_, lean_object* v_semiringInst_1083_){
_start:
{
lean_object* v_canonExpr_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1100_; 
v_canonExpr_1084_ = lean_ctor_get(v_inst_1080_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_inst_1080_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v_inst_1080_, 1);
lean_dec(v_unused_1101_);
v___x_1086_ = v_inst_1080_;
v_isShared_1087_ = v_isSharedCheck_1100_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_canonExpr_1084_);
lean_dec(v_inst_1080_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1100_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_n_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v_n_1088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
v___x_1089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2));
v___x_1090_ = lean_box(0);
if (v_isShared_1087_ == 0)
{
lean_ctor_set_tag(v___x_1086_, 1);
lean_ctor_set(v___x_1086_, 1, v___x_1090_);
lean_ctor_set(v___x_1086_, 0, v_u_1081_);
v___x_1092_ = v___x_1086_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_u_1081_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; lean_object* v_ofNatInst_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_inc_ref(v___x_1092_);
v___x_1093_ = l_Lean_mkConst(v___x_1089_, v___x_1092_);
lean_inc_ref(v_type_1082_);
v_ofNatInst_1094_ = l_Lean_mkApp3(v___x_1093_, v_type_1082_, v_semiringInst_1083_, v_n_1088_);
v___x_1095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4));
v___x_1096_ = l_Lean_mkConst(v___x_1095_, v___x_1092_);
v___x_1097_ = l_Lean_mkApp3(v___x_1096_, v_type_1082_, v_n_1088_, v_ofNatInst_1094_);
v___x_1098_ = lean_apply_1(v_canonExpr_1084_, v___x_1097_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object* v_m_1102_, lean_object* v_inst_1103_, lean_object* v_u_1104_, lean_object* v_type_1105_, lean_object* v_semiringInst_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_1103_, v_u_1104_, v_type_1105_, v_semiringInst_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0(lean_object* v_one_1108_, lean_object* v_s_1109_){
_start:
{
lean_object* v_id_1110_; lean_object* v_type_1111_; lean_object* v_u_1112_; lean_object* v_ringInst_1113_; lean_object* v_semiringInst_1114_; lean_object* v_charInst_x3f_1115_; lean_object* v_addFn_x3f_1116_; lean_object* v_mulFn_x3f_1117_; lean_object* v_subFn_x3f_1118_; lean_object* v_negFn_x3f_1119_; lean_object* v_powFn_x3f_1120_; lean_object* v_intCastFn_x3f_1121_; lean_object* v_natCastFn_x3f_1122_; lean_object* v_vars_1123_; lean_object* v_varMap_1124_; lean_object* v_denote_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1133_; 
v_id_1110_ = lean_ctor_get(v_s_1109_, 0);
v_type_1111_ = lean_ctor_get(v_s_1109_, 1);
v_u_1112_ = lean_ctor_get(v_s_1109_, 2);
v_ringInst_1113_ = lean_ctor_get(v_s_1109_, 3);
v_semiringInst_1114_ = lean_ctor_get(v_s_1109_, 4);
v_charInst_x3f_1115_ = lean_ctor_get(v_s_1109_, 5);
v_addFn_x3f_1116_ = lean_ctor_get(v_s_1109_, 6);
v_mulFn_x3f_1117_ = lean_ctor_get(v_s_1109_, 7);
v_subFn_x3f_1118_ = lean_ctor_get(v_s_1109_, 8);
v_negFn_x3f_1119_ = lean_ctor_get(v_s_1109_, 9);
v_powFn_x3f_1120_ = lean_ctor_get(v_s_1109_, 10);
v_intCastFn_x3f_1121_ = lean_ctor_get(v_s_1109_, 11);
v_natCastFn_x3f_1122_ = lean_ctor_get(v_s_1109_, 12);
v_vars_1123_ = lean_ctor_get(v_s_1109_, 14);
v_varMap_1124_ = lean_ctor_get(v_s_1109_, 15);
v_denote_1125_ = lean_ctor_get(v_s_1109_, 16);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_s_1109_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v_s_1109_, 13);
lean_dec(v_unused_1134_);
v___x_1127_ = v_s_1109_;
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_denote_1125_);
lean_inc(v_varMap_1124_);
lean_inc(v_vars_1123_);
lean_inc(v_natCastFn_x3f_1122_);
lean_inc(v_intCastFn_x3f_1121_);
lean_inc(v_powFn_x3f_1120_);
lean_inc(v_negFn_x3f_1119_);
lean_inc(v_subFn_x3f_1118_);
lean_inc(v_mulFn_x3f_1117_);
lean_inc(v_addFn_x3f_1116_);
lean_inc(v_charInst_x3f_1115_);
lean_inc(v_semiringInst_1114_);
lean_inc(v_ringInst_1113_);
lean_inc(v_u_1112_);
lean_inc(v_type_1111_);
lean_inc(v_id_1110_);
lean_dec(v_s_1109_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_one_1108_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 13, v___x_1129_);
v___x_1131_ = v___x_1127_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_id_1110_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_type_1111_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_u_1112_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_ringInst_1113_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_semiringInst_1114_);
lean_ctor_set(v_reuseFailAlloc_1132_, 5, v_charInst_x3f_1115_);
lean_ctor_set(v_reuseFailAlloc_1132_, 6, v_addFn_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1132_, 7, v_mulFn_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1132_, 8, v_subFn_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1132_, 9, v_negFn_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1132_, 10, v_powFn_x3f_1120_);
lean_ctor_set(v_reuseFailAlloc_1132_, 11, v_intCastFn_x3f_1121_);
lean_ctor_set(v_reuseFailAlloc_1132_, 12, v_natCastFn_x3f_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 13, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1132_, 14, v_vars_1123_);
lean_ctor_set(v_reuseFailAlloc_1132_, 15, v_varMap_1124_);
lean_ctor_set(v_reuseFailAlloc_1132_, 16, v_denote_1125_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1(lean_object* v_toPure_1135_, lean_object* v_one_1136_, lean_object* v_____r_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_apply_2(v_toPure_1135_, lean_box(0), v_one_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2(lean_object* v_one_1139_, lean_object* v_inst_1140_, lean_object* v_toBind_1141_, lean_object* v___f_1142_, lean_object* v_____r_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_internalize___boxed), 14, 3);
lean_closure_set(v___x_1146_, 0, v_one_1139_);
lean_closure_set(v___x_1146_, 1, v___x_1144_);
lean_closure_set(v___x_1146_, 2, v___x_1145_);
v___x_1147_ = lean_apply_2(v_inst_1140_, lean_box(0), v___x_1146_);
v___x_1148_ = lean_apply_4(v_toBind_1141_, lean_box(0), lean_box(0), v___x_1147_, v___f_1142_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3(lean_object* v_toPure_1149_, lean_object* v_inst_1150_, lean_object* v_toBind_1151_, lean_object* v_modifyRing_1152_, lean_object* v_one_1153_){
_start:
{
lean_object* v___f_1154_; lean_object* v___f_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_inc_ref_n(v_one_1153_, 2);
v___f_1154_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1154_, 0, v_one_1153_);
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1155_, 0, v_toPure_1149_);
lean_closure_set(v___f_1155_, 1, v_one_1153_);
lean_inc(v_toBind_1151_);
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1156_, 0, v_one_1153_);
lean_closure_set(v___f_1156_, 1, v_inst_1150_);
lean_closure_set(v___f_1156_, 2, v_toBind_1151_);
lean_closure_set(v___f_1156_, 3, v___f_1155_);
v___x_1157_ = lean_apply_1(v_modifyRing_1152_, v___f_1154_);
v___x_1158_ = lean_apply_4(v_toBind_1151_, lean_box(0), lean_box(0), v___x_1157_, v___f_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4(lean_object* v_toPure_1159_, lean_object* v_inst_1160_, lean_object* v_toBind_1161_, lean_object* v___f_1162_, lean_object* v_ring_1163_){
_start:
{
lean_object* v_one_x3f_1164_; 
v_one_x3f_1164_ = lean_ctor_get(v_ring_1163_, 13);
if (lean_obj_tag(v_one_x3f_1164_) == 1)
{
lean_object* v_val_1165_; lean_object* v___x_1166_; 
lean_inc_ref(v_one_x3f_1164_);
lean_dec_ref(v_ring_1163_);
lean_dec(v___f_1162_);
lean_dec(v_toBind_1161_);
lean_dec_ref(v_inst_1160_);
v_val_1165_ = lean_ctor_get(v_one_x3f_1164_, 0);
lean_inc(v_val_1165_);
lean_dec_ref(v_one_x3f_1164_);
v___x_1166_ = lean_apply_2(v_toPure_1159_, lean_box(0), v_val_1165_);
return v___x_1166_;
}
else
{
lean_object* v_type_1167_; lean_object* v_u_1168_; lean_object* v_semiringInst_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v_toPure_1159_);
v_type_1167_ = lean_ctor_get(v_ring_1163_, 1);
lean_inc_ref(v_type_1167_);
v_u_1168_ = lean_ctor_get(v_ring_1163_, 2);
lean_inc(v_u_1168_);
v_semiringInst_1169_ = lean_ctor_get(v_ring_1163_, 4);
lean_inc_ref(v_semiringInst_1169_);
lean_dec_ref(v_ring_1163_);
v___x_1170_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_1160_, v_u_1168_, v_type_1167_, v_semiringInst_1169_);
v___x_1171_ = lean_apply_4(v_toBind_1161_, lean_box(0), lean_box(0), v___x_1170_, v___f_1162_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_){
_start:
{
lean_object* v_toApplicative_1176_; lean_object* v_toBind_1177_; lean_object* v_getRing_1178_; lean_object* v_modifyRing_1179_; lean_object* v_toPure_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; 
v_toApplicative_1176_ = lean_ctor_get(v_inst_1172_, 0);
lean_inc_ref(v_toApplicative_1176_);
v_toBind_1177_ = lean_ctor_get(v_inst_1172_, 1);
lean_inc_n(v_toBind_1177_, 3);
lean_dec_ref(v_inst_1172_);
v_getRing_1178_ = lean_ctor_get(v_inst_1174_, 0);
lean_inc(v_getRing_1178_);
v_modifyRing_1179_ = lean_ctor_get(v_inst_1174_, 1);
lean_inc(v_modifyRing_1179_);
lean_dec_ref(v_inst_1174_);
v_toPure_1180_ = lean_ctor_get(v_toApplicative_1176_, 1);
lean_inc_n(v_toPure_1180_, 2);
lean_dec_ref(v_toApplicative_1176_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1181_, 0, v_toPure_1180_);
lean_closure_set(v___f_1181_, 1, v_inst_1175_);
lean_closure_set(v___f_1181_, 2, v_toBind_1177_);
lean_closure_set(v___f_1181_, 3, v_modifyRing_1179_);
v___f_1182_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1182_, 0, v_toPure_1180_);
lean_closure_set(v___f_1182_, 1, v_inst_1173_);
lean_closure_set(v___f_1182_, 2, v_toBind_1177_);
lean_closure_set(v___f_1182_, 3, v___f_1181_);
v___x_1183_ = lean_apply_4(v_toBind_1177_, lean_box(0), lean_box(0), v_getRing_1178_, v___f_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object* v_m_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(v_inst_1185_, v_inst_1186_, v_inst_1187_, v_inst_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0(lean_object* v_invFn_1190_, lean_object* v_s_1191_){
_start:
{
lean_object* v_toRing_1192_; lean_object* v_semiringId_x3f_1193_; lean_object* v_commSemiringInst_1194_; lean_object* v_commRingInst_1195_; lean_object* v_noZeroDivInst_x3f_1196_; lean_object* v_fieldInst_x3f_1197_; lean_object* v_powIdentityInst_x3f_1198_; lean_object* v_denoteEntries_1199_; lean_object* v_nextId_1200_; lean_object* v_steps_1201_; lean_object* v_queue_1202_; lean_object* v_basis_1203_; lean_object* v_diseqs_1204_; uint8_t v_recheck_1205_; lean_object* v_invSet_1206_; lean_object* v_powIdentityVarCount_1207_; lean_object* v_numEq0_x3f_1208_; uint8_t v_numEq0Updated_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v_toRing_1192_ = lean_ctor_get(v_s_1191_, 0);
v_semiringId_x3f_1193_ = lean_ctor_get(v_s_1191_, 2);
v_commSemiringInst_1194_ = lean_ctor_get(v_s_1191_, 3);
v_commRingInst_1195_ = lean_ctor_get(v_s_1191_, 4);
v_noZeroDivInst_x3f_1196_ = lean_ctor_get(v_s_1191_, 5);
v_fieldInst_x3f_1197_ = lean_ctor_get(v_s_1191_, 6);
v_powIdentityInst_x3f_1198_ = lean_ctor_get(v_s_1191_, 7);
v_denoteEntries_1199_ = lean_ctor_get(v_s_1191_, 8);
v_nextId_1200_ = lean_ctor_get(v_s_1191_, 9);
v_steps_1201_ = lean_ctor_get(v_s_1191_, 10);
v_queue_1202_ = lean_ctor_get(v_s_1191_, 11);
v_basis_1203_ = lean_ctor_get(v_s_1191_, 12);
v_diseqs_1204_ = lean_ctor_get(v_s_1191_, 13);
v_recheck_1205_ = lean_ctor_get_uint8(v_s_1191_, sizeof(void*)*17);
v_invSet_1206_ = lean_ctor_get(v_s_1191_, 14);
v_powIdentityVarCount_1207_ = lean_ctor_get(v_s_1191_, 15);
v_numEq0_x3f_1208_ = lean_ctor_get(v_s_1191_, 16);
v_numEq0Updated_1209_ = lean_ctor_get_uint8(v_s_1191_, sizeof(void*)*17 + 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_s_1191_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_s_1191_, 1);
lean_dec(v_unused_1218_);
v___x_1211_ = v_s_1191_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_numEq0_x3f_1208_);
lean_inc(v_powIdentityVarCount_1207_);
lean_inc(v_invSet_1206_);
lean_inc(v_diseqs_1204_);
lean_inc(v_basis_1203_);
lean_inc(v_queue_1202_);
lean_inc(v_steps_1201_);
lean_inc(v_nextId_1200_);
lean_inc(v_denoteEntries_1199_);
lean_inc(v_powIdentityInst_x3f_1198_);
lean_inc(v_fieldInst_x3f_1197_);
lean_inc(v_noZeroDivInst_x3f_1196_);
lean_inc(v_commRingInst_1195_);
lean_inc(v_commSemiringInst_1194_);
lean_inc(v_semiringId_x3f_1193_);
lean_inc(v_toRing_1192_);
lean_dec(v_s_1191_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_invFn_1190_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___x_1213_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_toRing_1192_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_semiringId_x3f_1193_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_commSemiringInst_1194_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_commRingInst_1195_);
lean_ctor_set(v_reuseFailAlloc_1216_, 5, v_noZeroDivInst_x3f_1196_);
lean_ctor_set(v_reuseFailAlloc_1216_, 6, v_fieldInst_x3f_1197_);
lean_ctor_set(v_reuseFailAlloc_1216_, 7, v_powIdentityInst_x3f_1198_);
lean_ctor_set(v_reuseFailAlloc_1216_, 8, v_denoteEntries_1199_);
lean_ctor_set(v_reuseFailAlloc_1216_, 9, v_nextId_1200_);
lean_ctor_set(v_reuseFailAlloc_1216_, 10, v_steps_1201_);
lean_ctor_set(v_reuseFailAlloc_1216_, 11, v_queue_1202_);
lean_ctor_set(v_reuseFailAlloc_1216_, 12, v_basis_1203_);
lean_ctor_set(v_reuseFailAlloc_1216_, 13, v_diseqs_1204_);
lean_ctor_set(v_reuseFailAlloc_1216_, 14, v_invSet_1206_);
lean_ctor_set(v_reuseFailAlloc_1216_, 15, v_powIdentityVarCount_1207_);
lean_ctor_set(v_reuseFailAlloc_1216_, 16, v_numEq0_x3f_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*17, v_recheck_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*17 + 1, v_numEq0Updated_1209_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1(lean_object* v_toPure_1219_, lean_object* v_invFn_1220_, lean_object* v_____r_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_apply_2(v_toPure_1219_, lean_box(0), v_invFn_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2(lean_object* v_toPure_1223_, lean_object* v_modifyCommRing_1224_, lean_object* v_toBind_1225_, lean_object* v_invFn_1226_){
_start:
{
lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_inc_ref(v_invFn_1226_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1227_, 0, v_invFn_1226_);
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1228_, 0, v_toPure_1223_);
lean_closure_set(v___f_1228_, 1, v_invFn_1226_);
v___x_1229_ = lean_apply_1(v_modifyCommRing_1224_, v___f_1227_);
v___x_1230_ = lean_apply_4(v_toBind_1225_, lean_box(0), lean_box(0), v___x_1229_, v___f_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7));
v___x_1247_ = l_Lean_stringToMessageData(v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3(lean_object* v_toPure_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_toBind_1253_, lean_object* v___f_1254_, lean_object* v_ring_1255_){
_start:
{
lean_object* v_fieldInst_x3f_1256_; 
v_fieldInst_x3f_1256_ = lean_ctor_get(v_ring_1255_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1256_) == 1)
{
lean_object* v_invFn_x3f_1257_; 
lean_inc_ref(v_fieldInst_x3f_1256_);
v_invFn_x3f_1257_ = lean_ctor_get(v_ring_1255_, 1);
if (lean_obj_tag(v_invFn_x3f_1257_) == 1)
{
lean_object* v_val_1258_; lean_object* v___x_1259_; 
lean_inc_ref(v_invFn_x3f_1257_);
lean_dec_ref(v_fieldInst_x3f_1256_);
lean_dec_ref(v_ring_1255_);
lean_dec(v___f_1254_);
lean_dec(v_toBind_1253_);
lean_dec_ref(v_inst_1252_);
lean_dec_ref(v_inst_1251_);
lean_dec_ref(v_inst_1250_);
lean_dec(v_inst_1249_);
v_val_1258_ = lean_ctor_get(v_invFn_x3f_1257_, 0);
lean_inc(v_val_1258_);
lean_dec_ref(v_invFn_x3f_1257_);
v___x_1259_ = lean_apply_2(v_toPure_1248_, lean_box(0), v_val_1258_);
return v___x_1259_;
}
else
{
lean_object* v_toRing_1260_; lean_object* v_val_1261_; lean_object* v_type_1262_; lean_object* v_u_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_expectedInst_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec(v_toPure_1248_);
v_toRing_1260_ = lean_ctor_get(v_ring_1255_, 0);
lean_inc_ref(v_toRing_1260_);
lean_dec_ref(v_ring_1255_);
v_val_1261_ = lean_ctor_get(v_fieldInst_x3f_1256_, 0);
lean_inc(v_val_1261_);
lean_dec_ref(v_fieldInst_x3f_1256_);
v_type_1262_ = lean_ctor_get(v_toRing_1260_, 1);
lean_inc_ref_n(v_type_1262_, 2);
v_u_1263_ = lean_ctor_get(v_toRing_1260_, 2);
lean_inc_n(v_u_1263_, 2);
lean_dec_ref(v_toRing_1260_);
v___x_1264_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2));
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_u_1263_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_mkConst(v___x_1264_, v___x_1266_);
v_expectedInst_1268_ = l_Lean_mkAppB(v___x_1267_, v_type_1262_, v_val_1261_);
v___x_1269_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4));
v___x_1270_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6));
v___x_1271_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(v_inst_1249_, v_inst_1250_, v_inst_1251_, v_inst_1252_, v_type_1262_, v_u_1263_, v___x_1269_, v___x_1270_, v_expectedInst_1268_);
v___x_1272_ = lean_apply_4(v_toBind_1253_, lean_box(0), lean_box(0), v___x_1271_, v___f_1254_);
return v___x_1272_;
}
}
else
{
lean_object* v_toRing_1273_; lean_object* v_type_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v___f_1254_);
lean_dec(v_toBind_1253_);
lean_dec_ref(v_inst_1252_);
lean_dec(v_inst_1249_);
lean_dec(v_toPure_1248_);
v_toRing_1273_ = lean_ctor_get(v_ring_1255_, 0);
lean_inc_ref(v_toRing_1273_);
lean_dec_ref(v_ring_1255_);
v_type_1274_ = lean_ctor_get(v_toRing_1273_, 1);
lean_inc_ref(v_type_1274_);
lean_dec_ref(v_toRing_1273_);
v___x_1275_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8);
v___x_1276_ = l_Lean_indentExpr(v_type_1274_);
v___x_1277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = l_Lean_throwError___redArg(v_inst_1251_, v_inst_1250_, v___x_1277_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_){
_start:
{
lean_object* v_toApplicative_1284_; lean_object* v_toBind_1285_; lean_object* v_getCommRing_1286_; lean_object* v_modifyCommRing_1287_; lean_object* v_toPure_1288_; lean_object* v___f_1289_; lean_object* v___f_1290_; lean_object* v___x_1291_; 
v_toApplicative_1284_ = lean_ctor_get(v_inst_1281_, 0);
v_toBind_1285_ = lean_ctor_get(v_inst_1281_, 1);
lean_inc_n(v_toBind_1285_, 3);
v_getCommRing_1286_ = lean_ctor_get(v_inst_1283_, 0);
lean_inc(v_getCommRing_1286_);
v_modifyCommRing_1287_ = lean_ctor_get(v_inst_1283_, 1);
lean_inc(v_modifyCommRing_1287_);
lean_dec_ref(v_inst_1283_);
v_toPure_1288_ = lean_ctor_get(v_toApplicative_1284_, 1);
lean_inc_n(v_toPure_1288_, 2);
v___f_1289_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1289_, 0, v_toPure_1288_);
lean_closure_set(v___f_1289_, 1, v_modifyCommRing_1287_);
lean_closure_set(v___f_1289_, 2, v_toBind_1285_);
v___f_1290_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1290_, 0, v_toPure_1288_);
lean_closure_set(v___f_1290_, 1, v_inst_1279_);
lean_closure_set(v___f_1290_, 2, v_inst_1280_);
lean_closure_set(v___f_1290_, 3, v_inst_1281_);
lean_closure_set(v___f_1290_, 4, v_inst_1282_);
lean_closure_set(v___f_1290_, 5, v_toBind_1285_);
lean_closure_set(v___f_1290_, 6, v___f_1289_);
v___x_1291_ = lean_apply_4(v_toBind_1285_, lean_box(0), lean_box(0), v_getCommRing_1286_, v___f_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn(lean_object* v_m_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(v_inst_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_, v_inst_1297_);
return v___x_1298_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
}
#ifdef __cplusplus
}
#endif
