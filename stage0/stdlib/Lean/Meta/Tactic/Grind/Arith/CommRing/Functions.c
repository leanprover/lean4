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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
lean_inc(v_ref_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_ref_30_);
lean_ctor_set(v___x_36_, 1, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0));
v___x_50_ = l_Lean_stringToMessageData(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2));
v___x_53_ = l_Lean_stringToMessageData(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4));
v___x_56_ = l_Lean_stringToMessageData(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6));
v___x_59_ = l_Lean_stringToMessageData(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object* v_declName_60_, lean_object* v_inst_61_, lean_object* v_inst_x27_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; 
lean_inc_ref(v_inst_x27_62_);
lean_inc_ref(v_inst_61_);
v___x_68_ = l_Lean_Meta_isDefEqI(v_inst_61_, v_inst_x27_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_92_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_92_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_92_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_92_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint8_t v___x_73_; 
v___x_73_ = lean_unbox(v_a_69_);
lean_dec(v_a_69_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
lean_del_object(v___x_71_);
v___x_74_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1);
v___x_75_ = l_Lean_MessageData_ofName(v_declName_60_);
v___x_76_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3);
v___x_78_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = l_Lean_indentExpr(v_inst_61_);
v___x_80_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5);
v___x_82_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = l_Lean_indentExpr(v_inst_x27_62_);
v___x_84_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7);
v___x_86_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v___x_86_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_90_; 
lean_dec_ref(v_inst_x27_62_);
lean_dec_ref(v_inst_61_);
lean_dec(v_declName_60_);
v___x_88_ = lean_box(0);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_88_);
v___x_90_ = v___x_71_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec_ref(v_inst_x27_62_);
lean_dec_ref(v_inst_61_);
lean_dec(v_declName_60_);
v_a_93_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_68_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_68_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed(lean_object* v_declName_101_, lean_object* v_inst_102_, lean_object* v_inst_x27_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_101_, v_inst_102_, v_inst_x27_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(lean_object* v_00_u03b1_110_, lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___boxed(lean_object* v_00_u03b1_118_, lean_object* v_msg_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(v_00_u03b1_118_, v_msg_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0(lean_object* v_inst_126_, lean_object* v_declName_127_, lean_object* v___x_128_, lean_object* v_type_129_, lean_object* v_inst_130_, lean_object* v_____r_131_){
_start:
{
lean_object* v_canonExpr_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_canonExpr_132_ = lean_ctor_get(v_inst_126_, 0);
lean_inc(v_canonExpr_132_);
lean_dec_ref(v_inst_126_);
v___x_133_ = l_Lean_mkConst(v_declName_127_, v___x_128_);
v___x_134_ = l_Lean_mkAppB(v___x_133_, v_type_129_, v_inst_130_);
v___x_135_ = lean_apply_1(v_canonExpr_132_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1(lean_object* v_inst_136_, lean_object* v_declName_137_, lean_object* v___x_138_, lean_object* v_type_139_, lean_object* v_expectedInst_140_, lean_object* v_inst_141_, lean_object* v_toBind_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
lean_inc_ref(v_inst_143_);
lean_inc(v_declName_137_);
v___f_144_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_144_, 0, v_inst_136_);
lean_closure_set(v___f_144_, 1, v_declName_137_);
lean_closure_set(v___f_144_, 2, v___x_138_);
lean_closure_set(v___f_144_, 3, v_type_139_);
lean_closure_set(v___f_144_, 4, v_inst_143_);
v___x_145_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_145_, 0, v_declName_137_);
lean_closure_set(v___x_145_, 1, v_inst_143_);
lean_closure_set(v___x_145_, 2, v_expectedInst_140_);
v___x_146_ = lean_apply_2(v_inst_141_, lean_box(0), v___x_145_);
v___x_147_ = lean_apply_4(v_toBind_142_, lean_box(0), lean_box(0), v___x_146_, v___f_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_type_152_, lean_object* v_u_153_, lean_object* v_instDeclName_154_, lean_object* v_declName_155_, lean_object* v_expectedInst_156_){
_start:
{
lean_object* v_toBind_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_toBind_157_ = lean_ctor_get(v_inst_150_, 1);
lean_inc_n(v_toBind_157_, 2);
v___x_158_ = lean_box(0);
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v_u_153_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
lean_inc_ref(v_type_152_);
lean_inc_ref(v___x_159_);
lean_inc_ref(v_inst_151_);
v___f_160_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_160_, 0, v_inst_151_);
lean_closure_set(v___f_160_, 1, v_declName_155_);
lean_closure_set(v___f_160_, 2, v___x_159_);
lean_closure_set(v___f_160_, 3, v_type_152_);
lean_closure_set(v___f_160_, 4, v_expectedInst_156_);
lean_closure_set(v___f_160_, 5, v_inst_148_);
lean_closure_set(v___f_160_, 6, v_toBind_157_);
v___x_161_ = l_Lean_mkConst(v_instDeclName_154_, v___x_159_);
v___x_162_ = l_Lean_Expr_app___override(v___x_161_, v_type_152_);
v___x_163_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_150_, v_inst_149_, v_inst_151_, v___x_162_);
v___x_164_ = lean_apply_4(v_toBind_157_, lean_box(0), lean_box(0), v___x_163_, v___f_160_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn(lean_object* v_m_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_type_170_, lean_object* v_u_171_, lean_object* v_instDeclName_172_, lean_object* v_declName_173_, lean_object* v_expectedInst_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(v_inst_166_, v_inst_167_, v_inst_168_, v_inst_169_, v_type_170_, v_u_171_, v_instDeclName_172_, v_declName_173_, v_expectedInst_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_176_, lean_object* v_declName_177_, lean_object* v___x_178_, lean_object* v_type_179_, lean_object* v_inst_180_, lean_object* v_____r_181_){
_start:
{
lean_object* v_canonExpr_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_canonExpr_182_ = lean_ctor_get(v_inst_176_, 0);
lean_inc(v_canonExpr_182_);
lean_dec_ref(v_inst_176_);
v___x_183_ = l_Lean_mkConst(v_declName_177_, v___x_178_);
lean_inc_ref_n(v_type_179_, 2);
v___x_184_ = l_Lean_mkApp4(v___x_183_, v_type_179_, v_type_179_, v_type_179_, v_inst_180_);
v___x_185_ = lean_apply_1(v_canonExpr_182_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_186_, lean_object* v_declName_187_, lean_object* v___x_188_, lean_object* v_type_189_, lean_object* v_expectedInst_190_, lean_object* v_inst_191_, lean_object* v_toBind_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v___f_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
lean_inc_ref(v_inst_193_);
lean_inc(v_declName_187_);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_194_, 0, v_inst_186_);
lean_closure_set(v___f_194_, 1, v_declName_187_);
lean_closure_set(v___f_194_, 2, v___x_188_);
lean_closure_set(v___f_194_, 3, v_type_189_);
lean_closure_set(v___f_194_, 4, v_inst_193_);
v___x_195_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_195_, 0, v_declName_187_);
lean_closure_set(v___x_195_, 1, v_inst_193_);
lean_closure_set(v___x_195_, 2, v_expectedInst_190_);
v___x_196_ = lean_apply_2(v_inst_191_, lean_box(0), v___x_195_);
v___x_197_ = lean_apply_4(v_toBind_192_, lean_box(0), lean_box(0), v___x_196_, v___f_194_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_type_202_, lean_object* v_u_203_, lean_object* v_instDeclName_204_, lean_object* v_declName_205_, lean_object* v_expectedInst_206_){
_start:
{
lean_object* v_toBind_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___f_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_toBind_207_ = lean_ctor_get(v_inst_200_, 1);
lean_inc_n(v_toBind_207_, 2);
v___x_208_ = lean_box(0);
lean_inc_n(v_u_203_, 2);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v_u_203_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v_u_203_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v_u_203_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_inc_ref_n(v_type_202_, 3);
lean_inc_ref(v___x_211_);
lean_inc_ref(v_inst_201_);
v___f_212_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_212_, 0, v_inst_201_);
lean_closure_set(v___f_212_, 1, v_declName_205_);
lean_closure_set(v___f_212_, 2, v___x_211_);
lean_closure_set(v___f_212_, 3, v_type_202_);
lean_closure_set(v___f_212_, 4, v_expectedInst_206_);
lean_closure_set(v___f_212_, 5, v_inst_198_);
lean_closure_set(v___f_212_, 6, v_toBind_207_);
v___x_213_ = l_Lean_mkConst(v_instDeclName_204_, v___x_211_);
v___x_214_ = l_Lean_mkApp3(v___x_213_, v_type_202_, v_type_202_, v_type_202_);
v___x_215_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_200_, v_inst_199_, v_inst_201_, v___x_214_);
v___x_216_ = lean_apply_4(v_toBind_207_, lean_box(0), lean_box(0), v___x_215_, v___f_212_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn(lean_object* v_m_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_type_222_, lean_object* v_u_223_, lean_object* v_instDeclName_224_, lean_object* v_declName_225_, lean_object* v_expectedInst_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_218_, v_inst_219_, v_inst_220_, v_inst_221_, v_type_222_, v_u_223_, v_instDeclName_224_, v_declName_225_, v_expectedInst_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0(lean_object* v_inst_228_, lean_object* v___x_229_, lean_object* v___x_230_, lean_object* v_type_231_, lean_object* v___x_232_, lean_object* v_inst_233_, lean_object* v_____r_234_){
_start:
{
lean_object* v_canonExpr_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_canonExpr_235_ = lean_ctor_get(v_inst_228_, 0);
lean_inc(v_canonExpr_235_);
lean_dec_ref(v_inst_228_);
v___x_236_ = l_Lean_mkConst(v___x_229_, v___x_230_);
lean_inc_ref(v_type_231_);
v___x_237_ = l_Lean_mkApp4(v___x_236_, v_type_231_, v___x_232_, v_type_231_, v_inst_233_);
v___x_238_ = lean_apply_1(v_canonExpr_235_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1(lean_object* v___x_249_, lean_object* v_type_250_, lean_object* v_semiringInst_251_, lean_object* v___x_252_, lean_object* v_inst_253_, lean_object* v___x_254_, lean_object* v___x_255_, lean_object* v_inst_256_, lean_object* v_toBind_257_, lean_object* v_inst_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_inst_x27_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_259_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4));
v___x_260_ = l_Lean_mkConst(v___x_259_, v___x_249_);
lean_inc_ref(v_type_250_);
v_inst_x27_261_ = l_Lean_mkAppB(v___x_260_, v_type_250_, v_semiringInst_251_);
v___x_262_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5));
v___x_263_ = l_Lean_Name_mkStr2(v___x_252_, v___x_262_);
lean_inc_ref(v_inst_258_);
lean_inc(v___x_263_);
v___f_264_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_264_, 0, v_inst_253_);
lean_closure_set(v___f_264_, 1, v___x_263_);
lean_closure_set(v___f_264_, 2, v___x_254_);
lean_closure_set(v___f_264_, 3, v_type_250_);
lean_closure_set(v___f_264_, 4, v___x_255_);
lean_closure_set(v___f_264_, 5, v_inst_258_);
v___x_265_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_265_, 0, v___x_263_);
lean_closure_set(v___x_265_, 1, v_inst_258_);
lean_closure_set(v___x_265_, 2, v_inst_x27_261_);
v___x_266_ = lean_apply_2(v_inst_256_, lean_box(0), v___x_265_);
v___x_267_ = lean_apply_4(v_toBind_257_, lean_box(0), lean_box(0), v___x_266_, v___f_264_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = l_Lean_Level_ofNat(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_u_277_, lean_object* v_type_278_, lean_object* v_semiringInst_279_){
_start:
{
lean_object* v_toBind_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_toBind_280_ = lean_ctor_get(v_inst_275_, 1);
lean_inc_n(v_toBind_280_, 2);
v___x_281_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0));
v___x_282_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1));
v___x_283_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2);
v___x_284_ = lean_box(0);
lean_inc(v_u_277_);
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v_u_277_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
lean_inc_ref(v___x_285_);
v___x_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_283_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v_u_277_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
lean_inc_ref(v___x_287_);
v___x_288_ = l_Lean_mkConst(v___x_282_, v___x_287_);
v___x_289_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_276_);
lean_inc_ref_n(v_type_278_, 2);
v___f_290_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_290_, 0, v___x_285_);
lean_closure_set(v___f_290_, 1, v_type_278_);
lean_closure_set(v___f_290_, 2, v_semiringInst_279_);
lean_closure_set(v___f_290_, 3, v___x_281_);
lean_closure_set(v___f_290_, 4, v_inst_276_);
lean_closure_set(v___f_290_, 5, v___x_287_);
lean_closure_set(v___f_290_, 6, v___x_289_);
lean_closure_set(v___f_290_, 7, v_inst_273_);
lean_closure_set(v___f_290_, 8, v_toBind_280_);
v___x_291_ = l_Lean_mkApp3(v___x_288_, v_type_278_, v___x_289_, v_type_278_);
v___x_292_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_275_, v_inst_274_, v_inst_276_, v___x_291_);
v___x_293_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_292_, v___f_290_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn(lean_object* v_m_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_u_299_, lean_object* v_type_300_, lean_object* v_semiringInst_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_295_, v_inst_296_, v_inst_297_, v_inst_298_, v_u_299_, v_type_300_, v_semiringInst_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0(lean_object* v___x_303_, lean_object* v___x_304_, lean_object* v___x_305_, lean_object* v_type_306_, lean_object* v_canonExpr_307_, lean_object* v_inst_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = l_Lean_Name_mkStr2(v___x_303_, v___x_304_);
v___x_310_ = l_Lean_mkConst(v___x_309_, v___x_305_);
v___x_311_ = l_Lean_mkAppB(v___x_310_, v_type_306_, v_inst_308_);
v___x_312_ = lean_apply_1(v_canonExpr_307_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1(lean_object* v___f_313_, lean_object* v_inst_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_apply_1(v___f_313_, v_inst_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_316_, lean_object* v_val_317_, lean_object* v_toBind_318_, lean_object* v___f_319_, lean_object* v_____r_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_apply_2(v_toPure_316_, lean_box(0), v_val_317_);
v___x_322_ = lean_apply_4(v_toBind_318_, lean_box(0), lean_box(0), v___x_321_, v___f_319_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_323_, lean_object* v_inst_x27_324_, lean_object* v_toBind_325_, lean_object* v___f_326_, lean_object* v___f_327_, lean_object* v___x_328_, lean_object* v___x_329_, lean_object* v_inst_330_, lean_object* v_____do__lift_331_){
_start:
{
if (lean_obj_tag(v_____do__lift_331_) == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_inst_330_);
lean_dec_ref(v___x_329_);
lean_dec_ref(v___x_328_);
lean_dec(v___f_327_);
v___x_332_ = lean_apply_2(v_toPure_323_, lean_box(0), v_inst_x27_324_);
v___x_333_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_332_, v___f_326_);
return v___x_333_;
}
else
{
lean_object* v_val_334_; lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v___f_326_);
v_val_334_ = lean_ctor_get(v_____do__lift_331_, 0);
lean_inc_n(v_val_334_, 2);
lean_dec_ref_known(v_____do__lift_331_, 1);
lean_inc(v_toBind_325_);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_335_, 0, v_toPure_323_);
lean_closure_set(v___f_335_, 1, v_val_334_);
lean_closure_set(v___f_335_, 2, v_toBind_325_);
lean_closure_set(v___f_335_, 3, v___f_327_);
v___x_336_ = l_Lean_Name_mkStr2(v___x_328_, v___x_329_);
v___x_337_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_337_, 0, v___x_336_);
lean_closure_set(v___x_337_, 1, v_val_334_);
lean_closure_set(v___x_337_, 2, v_inst_x27_324_);
v___x_338_ = lean_apply_2(v_inst_330_, lean_box(0), v___x_337_);
v___x_339_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_338_, v___f_335_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_u_352_, lean_object* v_type_353_, lean_object* v_semiringInst_354_){
_start:
{
lean_object* v_toApplicative_355_; lean_object* v_toBind_356_; lean_object* v_canonExpr_357_; lean_object* v_synthInstance_x3f_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_380_; 
v_toApplicative_355_ = lean_ctor_get(v_inst_350_, 0);
lean_inc_ref(v_toApplicative_355_);
v_toBind_356_ = lean_ctor_get(v_inst_350_, 1);
lean_inc(v_toBind_356_);
lean_dec_ref(v_inst_350_);
v_canonExpr_357_ = lean_ctor_get(v_inst_351_, 0);
v_synthInstance_x3f_358_ = lean_ctor_get(v_inst_351_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_inst_351_);
if (v_isSharedCheck_380_ == 0)
{
v___x_360_ = v_inst_351_;
v_isShared_361_ = v_isSharedCheck_380_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_synthInstance_x3f_358_);
lean_inc(v_canonExpr_357_);
lean_dec(v_inst_351_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_380_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_toPure_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v_toPure_362_ = lean_ctor_get(v_toApplicative_355_, 1);
lean_inc(v_toPure_362_);
lean_dec_ref(v_toApplicative_355_);
v___x_363_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0));
v___x_364_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1));
v___x_365_ = lean_box(0);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
lean_ctor_set(v___x_360_, 1, v___x_365_);
lean_ctor_set(v___x_360_, 0, v_u_352_);
v___x_367_ = v___x_360_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_u_352_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_365_);
v___x_367_ = v_reuseFailAlloc_379_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v_inst_x27_369_; lean_object* v___x_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_instType_375_; lean_object* v___x_376_; lean_object* v___f_377_; lean_object* v___x_378_; 
lean_inc_ref_n(v___x_367_, 2);
v___x_368_ = l_Lean_mkConst(v___x_364_, v___x_367_);
lean_inc_ref_n(v_type_353_, 2);
v_inst_x27_369_ = l_Lean_mkAppB(v___x_368_, v_type_353_, v_semiringInst_354_);
v___x_370_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2));
v___f_371_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_371_, 0, v___x_370_);
lean_closure_set(v___f_371_, 1, v___x_363_);
lean_closure_set(v___f_371_, 2, v___x_367_);
lean_closure_set(v___f_371_, 3, v_type_353_);
lean_closure_set(v___f_371_, 4, v_canonExpr_357_);
v___f_372_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_372_, 0, v___f_371_);
v___x_373_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3));
v___x_374_ = l_Lean_mkConst(v___x_373_, v___x_367_);
v_instType_375_ = l_Lean_Expr_app___override(v___x_374_, v_type_353_);
v___x_376_ = lean_apply_1(v_synthInstance_x3f_358_, v_instType_375_);
lean_inc_ref(v___f_372_);
lean_inc(v_toBind_356_);
v___f_377_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_377_, 0, v_toPure_362_);
lean_closure_set(v___f_377_, 1, v_inst_x27_369_);
lean_closure_set(v___f_377_, 2, v_toBind_356_);
lean_closure_set(v___f_377_, 3, v___f_372_);
lean_closure_set(v___f_377_, 4, v___f_372_);
lean_closure_set(v___f_377_, 5, v___x_370_);
lean_closure_set(v___f_377_, 6, v___x_363_);
lean_closure_set(v___f_377_, 7, v_inst_349_);
v___x_378_ = lean_apply_4(v_toBind_356_, lean_box(0), lean_box(0), v___x_376_, v___f_377_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn(lean_object* v_m_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_u_385_, lean_object* v_type_386_, lean_object* v_semiringInst_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_382_, v_inst_383_, v_inst_384_, v_u_385_, v_type_386_, v_semiringInst_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0(lean_object* v_addFn_389_, lean_object* v_s_390_){
_start:
{
lean_object* v_id_391_; lean_object* v_type_392_; lean_object* v_u_393_; lean_object* v_ringInst_394_; lean_object* v_semiringInst_395_; lean_object* v_charInst_x3f_396_; lean_object* v_mulFn_x3f_397_; lean_object* v_subFn_x3f_398_; lean_object* v_negFn_x3f_399_; lean_object* v_powFn_x3f_400_; lean_object* v_intCastFn_x3f_401_; lean_object* v_natCastFn_x3f_402_; lean_object* v_one_x3f_403_; lean_object* v_vars_404_; lean_object* v_varMap_405_; lean_object* v_denote_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_414_; 
v_id_391_ = lean_ctor_get(v_s_390_, 0);
v_type_392_ = lean_ctor_get(v_s_390_, 1);
v_u_393_ = lean_ctor_get(v_s_390_, 2);
v_ringInst_394_ = lean_ctor_get(v_s_390_, 3);
v_semiringInst_395_ = lean_ctor_get(v_s_390_, 4);
v_charInst_x3f_396_ = lean_ctor_get(v_s_390_, 5);
v_mulFn_x3f_397_ = lean_ctor_get(v_s_390_, 7);
v_subFn_x3f_398_ = lean_ctor_get(v_s_390_, 8);
v_negFn_x3f_399_ = lean_ctor_get(v_s_390_, 9);
v_powFn_x3f_400_ = lean_ctor_get(v_s_390_, 10);
v_intCastFn_x3f_401_ = lean_ctor_get(v_s_390_, 11);
v_natCastFn_x3f_402_ = lean_ctor_get(v_s_390_, 12);
v_one_x3f_403_ = lean_ctor_get(v_s_390_, 13);
v_vars_404_ = lean_ctor_get(v_s_390_, 14);
v_varMap_405_ = lean_ctor_get(v_s_390_, 15);
v_denote_406_ = lean_ctor_get(v_s_390_, 16);
v_isSharedCheck_414_ = !lean_is_exclusive(v_s_390_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v_s_390_, 6);
lean_dec(v_unused_415_);
v___x_408_ = v_s_390_;
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_denote_406_);
lean_inc(v_varMap_405_);
lean_inc(v_vars_404_);
lean_inc(v_one_x3f_403_);
lean_inc(v_natCastFn_x3f_402_);
lean_inc(v_intCastFn_x3f_401_);
lean_inc(v_powFn_x3f_400_);
lean_inc(v_negFn_x3f_399_);
lean_inc(v_subFn_x3f_398_);
lean_inc(v_mulFn_x3f_397_);
lean_inc(v_charInst_x3f_396_);
lean_inc(v_semiringInst_395_);
lean_inc(v_ringInst_394_);
lean_inc(v_u_393_);
lean_inc(v_type_392_);
lean_inc(v_id_391_);
lean_dec(v_s_390_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v_addFn_389_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 6, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_id_391_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_type_392_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_u_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_ringInst_394_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_semiringInst_395_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_charInst_x3f_396_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_mulFn_x3f_397_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_subFn_x3f_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 9, v_negFn_x3f_399_);
lean_ctor_set(v_reuseFailAlloc_413_, 10, v_powFn_x3f_400_);
lean_ctor_set(v_reuseFailAlloc_413_, 11, v_intCastFn_x3f_401_);
lean_ctor_set(v_reuseFailAlloc_413_, 12, v_natCastFn_x3f_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 13, v_one_x3f_403_);
lean_ctor_set(v_reuseFailAlloc_413_, 14, v_vars_404_);
lean_ctor_set(v_reuseFailAlloc_413_, 15, v_varMap_405_);
lean_ctor_set(v_reuseFailAlloc_413_, 16, v_denote_406_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1(lean_object* v_toPure_416_, lean_object* v_addFn_417_, lean_object* v_____r_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = lean_apply_2(v_toPure_416_, lean_box(0), v_addFn_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2(lean_object* v_toPure_420_, lean_object* v_modifyRing_421_, lean_object* v_toBind_422_, lean_object* v_addFn_423_){
_start:
{
lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_inc_ref(v_addFn_423_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_424_, 0, v_addFn_423_);
v___f_425_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_425_, 0, v_toPure_420_);
lean_closure_set(v___f_425_, 1, v_addFn_423_);
v___x_426_ = lean_apply_1(v_modifyRing_421_, v___f_424_);
v___x_427_ = lean_apply_4(v_toBind_422_, lean_box(0), lean_box(0), v___x_426_, v___f_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3(lean_object* v_toPure_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_toBind_449_, lean_object* v___f_450_, lean_object* v_ring_451_){
_start:
{
lean_object* v_addFn_x3f_452_; 
v_addFn_x3f_452_ = lean_ctor_get(v_ring_451_, 6);
if (lean_obj_tag(v_addFn_x3f_452_) == 1)
{
lean_object* v_val_453_; lean_object* v___x_454_; 
lean_inc_ref(v_addFn_x3f_452_);
lean_dec_ref(v_ring_451_);
lean_dec(v___f_450_);
lean_dec(v_toBind_449_);
lean_dec_ref(v_inst_448_);
lean_dec_ref(v_inst_447_);
lean_dec_ref(v_inst_446_);
lean_dec(v_inst_445_);
v_val_453_ = lean_ctor_get(v_addFn_x3f_452_, 0);
lean_inc(v_val_453_);
lean_dec_ref_known(v_addFn_x3f_452_, 1);
v___x_454_ = lean_apply_2(v_toPure_444_, lean_box(0), v_val_453_);
return v___x_454_;
}
else
{
lean_object* v_type_455_; lean_object* v_u_456_; lean_object* v_semiringInst_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_expectedInst_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_toPure_444_);
v_type_455_ = lean_ctor_get(v_ring_451_, 1);
lean_inc_ref_n(v_type_455_, 3);
v_u_456_ = lean_ctor_get(v_ring_451_, 2);
lean_inc_n(v_u_456_, 2);
v_semiringInst_457_ = lean_ctor_get(v_ring_451_, 4);
lean_inc_ref(v_semiringInst_457_);
lean_dec_ref(v_ring_451_);
v___x_458_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1));
v___x_459_ = lean_box(0);
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v_u_456_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
lean_inc_ref(v___x_460_);
v___x_461_ = l_Lean_mkConst(v___x_458_, v___x_460_);
v___x_462_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3));
v___x_463_ = l_Lean_mkConst(v___x_462_, v___x_460_);
v___x_464_ = l_Lean_mkAppB(v___x_463_, v_type_455_, v_semiringInst_457_);
v_expectedInst_465_ = l_Lean_mkAppB(v___x_461_, v_type_455_, v___x_464_);
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5));
v___x_467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7));
v___x_468_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_445_, v_inst_446_, v_inst_447_, v_inst_448_, v_type_455_, v_u_456_, v___x_466_, v___x_467_, v_expectedInst_465_);
v___x_469_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v___x_468_, v___f_450_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_){
_start:
{
lean_object* v_toApplicative_475_; lean_object* v_toBind_476_; lean_object* v_getRing_477_; lean_object* v_modifyRing_478_; lean_object* v_toPure_479_; lean_object* v___f_480_; lean_object* v___f_481_; lean_object* v___x_482_; 
v_toApplicative_475_ = lean_ctor_get(v_inst_472_, 0);
v_toBind_476_ = lean_ctor_get(v_inst_472_, 1);
lean_inc_n(v_toBind_476_, 3);
v_getRing_477_ = lean_ctor_get(v_inst_474_, 0);
lean_inc(v_getRing_477_);
v_modifyRing_478_ = lean_ctor_get(v_inst_474_, 1);
lean_inc(v_modifyRing_478_);
lean_dec_ref(v_inst_474_);
v_toPure_479_ = lean_ctor_get(v_toApplicative_475_, 1);
lean_inc_n(v_toPure_479_, 2);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_480_, 0, v_toPure_479_);
lean_closure_set(v___f_480_, 1, v_modifyRing_478_);
lean_closure_set(v___f_480_, 2, v_toBind_476_);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_481_, 0, v_toPure_479_);
lean_closure_set(v___f_481_, 1, v_inst_470_);
lean_closure_set(v___f_481_, 2, v_inst_471_);
lean_closure_set(v___f_481_, 3, v_inst_472_);
lean_closure_set(v___f_481_, 4, v_inst_473_);
lean_closure_set(v___f_481_, 5, v_toBind_476_);
lean_closure_set(v___f_481_, 6, v___f_480_);
v___x_482_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v_getRing_477_, v___f_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn(lean_object* v_m_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(v_inst_484_, v_inst_485_, v_inst_486_, v_inst_487_, v_inst_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0(lean_object* v_subFn_490_, lean_object* v_s_491_){
_start:
{
lean_object* v_id_492_; lean_object* v_type_493_; lean_object* v_u_494_; lean_object* v_ringInst_495_; lean_object* v_semiringInst_496_; lean_object* v_charInst_x3f_497_; lean_object* v_addFn_x3f_498_; lean_object* v_mulFn_x3f_499_; lean_object* v_negFn_x3f_500_; lean_object* v_powFn_x3f_501_; lean_object* v_intCastFn_x3f_502_; lean_object* v_natCastFn_x3f_503_; lean_object* v_one_x3f_504_; lean_object* v_vars_505_; lean_object* v_varMap_506_; lean_object* v_denote_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_id_492_ = lean_ctor_get(v_s_491_, 0);
v_type_493_ = lean_ctor_get(v_s_491_, 1);
v_u_494_ = lean_ctor_get(v_s_491_, 2);
v_ringInst_495_ = lean_ctor_get(v_s_491_, 3);
v_semiringInst_496_ = lean_ctor_get(v_s_491_, 4);
v_charInst_x3f_497_ = lean_ctor_get(v_s_491_, 5);
v_addFn_x3f_498_ = lean_ctor_get(v_s_491_, 6);
v_mulFn_x3f_499_ = lean_ctor_get(v_s_491_, 7);
v_negFn_x3f_500_ = lean_ctor_get(v_s_491_, 9);
v_powFn_x3f_501_ = lean_ctor_get(v_s_491_, 10);
v_intCastFn_x3f_502_ = lean_ctor_get(v_s_491_, 11);
v_natCastFn_x3f_503_ = lean_ctor_get(v_s_491_, 12);
v_one_x3f_504_ = lean_ctor_get(v_s_491_, 13);
v_vars_505_ = lean_ctor_get(v_s_491_, 14);
v_varMap_506_ = lean_ctor_get(v_s_491_, 15);
v_denote_507_ = lean_ctor_get(v_s_491_, 16);
v_isSharedCheck_515_ = !lean_is_exclusive(v_s_491_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_s_491_, 8);
lean_dec(v_unused_516_);
v___x_509_ = v_s_491_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_denote_507_);
lean_inc(v_varMap_506_);
lean_inc(v_vars_505_);
lean_inc(v_one_x3f_504_);
lean_inc(v_natCastFn_x3f_503_);
lean_inc(v_intCastFn_x3f_502_);
lean_inc(v_powFn_x3f_501_);
lean_inc(v_negFn_x3f_500_);
lean_inc(v_mulFn_x3f_499_);
lean_inc(v_addFn_x3f_498_);
lean_inc(v_charInst_x3f_497_);
lean_inc(v_semiringInst_496_);
lean_inc(v_ringInst_495_);
lean_inc(v_u_494_);
lean_inc(v_type_493_);
lean_inc(v_id_492_);
lean_dec(v_s_491_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_subFn_490_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 8, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_id_492_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_type_493_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_u_494_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_ringInst_495_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_semiringInst_496_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v_charInst_x3f_497_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v_addFn_x3f_498_);
lean_ctor_set(v_reuseFailAlloc_514_, 7, v_mulFn_x3f_499_);
lean_ctor_set(v_reuseFailAlloc_514_, 8, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 9, v_negFn_x3f_500_);
lean_ctor_set(v_reuseFailAlloc_514_, 10, v_powFn_x3f_501_);
lean_ctor_set(v_reuseFailAlloc_514_, 11, v_intCastFn_x3f_502_);
lean_ctor_set(v_reuseFailAlloc_514_, 12, v_natCastFn_x3f_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 13, v_one_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 14, v_vars_505_);
lean_ctor_set(v_reuseFailAlloc_514_, 15, v_varMap_506_);
lean_ctor_set(v_reuseFailAlloc_514_, 16, v_denote_507_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1(lean_object* v_toPure_517_, lean_object* v_subFn_518_, lean_object* v_____r_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_apply_2(v_toPure_517_, lean_box(0), v_subFn_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2(lean_object* v_toPure_521_, lean_object* v_modifyRing_522_, lean_object* v_toBind_523_, lean_object* v_subFn_524_){
_start:
{
lean_object* v___f_525_; lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_inc_ref(v_subFn_524_);
v___f_525_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_525_, 0, v_subFn_524_);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_526_, 0, v_toPure_521_);
lean_closure_set(v___f_526_, 1, v_subFn_524_);
v___x_527_ = lean_apply_1(v_modifyRing_522_, v___f_525_);
v___x_528_ = lean_apply_4(v_toBind_523_, lean_box(0), lean_box(0), v___x_527_, v___f_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3(lean_object* v_toPure_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_toBind_551_, lean_object* v___f_552_, lean_object* v_ring_553_){
_start:
{
lean_object* v_subFn_x3f_554_; 
v_subFn_x3f_554_ = lean_ctor_get(v_ring_553_, 8);
if (lean_obj_tag(v_subFn_x3f_554_) == 1)
{
lean_object* v_val_555_; lean_object* v___x_556_; 
lean_inc_ref(v_subFn_x3f_554_);
lean_dec_ref(v_ring_553_);
lean_dec(v___f_552_);
lean_dec(v_toBind_551_);
lean_dec_ref(v_inst_550_);
lean_dec_ref(v_inst_549_);
lean_dec_ref(v_inst_548_);
lean_dec(v_inst_547_);
v_val_555_ = lean_ctor_get(v_subFn_x3f_554_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v_subFn_x3f_554_, 1);
v___x_556_ = lean_apply_2(v_toPure_546_, lean_box(0), v_val_555_);
return v___x_556_;
}
else
{
lean_object* v_type_557_; lean_object* v_u_558_; lean_object* v_ringInst_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_expectedInst_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_toPure_546_);
v_type_557_ = lean_ctor_get(v_ring_553_, 1);
lean_inc_ref_n(v_type_557_, 3);
v_u_558_ = lean_ctor_get(v_ring_553_, 2);
lean_inc_n(v_u_558_, 2);
v_ringInst_559_ = lean_ctor_get(v_ring_553_, 3);
lean_inc_ref(v_ringInst_559_);
lean_dec_ref(v_ring_553_);
v___x_560_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1));
v___x_561_ = lean_box(0);
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v_u_558_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
lean_inc_ref(v___x_562_);
v___x_563_ = l_Lean_mkConst(v___x_560_, v___x_562_);
v___x_564_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4));
v___x_565_ = l_Lean_mkConst(v___x_564_, v___x_562_);
v___x_566_ = l_Lean_mkAppB(v___x_565_, v_type_557_, v_ringInst_559_);
v_expectedInst_567_ = l_Lean_mkAppB(v___x_563_, v_type_557_, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6));
v___x_569_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8));
v___x_570_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_547_, v_inst_548_, v_inst_549_, v_inst_550_, v_type_557_, v_u_558_, v___x_568_, v___x_569_, v_expectedInst_567_);
v___x_571_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_570_, v___f_552_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_){
_start:
{
lean_object* v_toApplicative_577_; lean_object* v_toBind_578_; lean_object* v_getRing_579_; lean_object* v_modifyRing_580_; lean_object* v_toPure_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___x_584_; 
v_toApplicative_577_ = lean_ctor_get(v_inst_574_, 0);
v_toBind_578_ = lean_ctor_get(v_inst_574_, 1);
lean_inc_n(v_toBind_578_, 3);
v_getRing_579_ = lean_ctor_get(v_inst_576_, 0);
lean_inc(v_getRing_579_);
v_modifyRing_580_ = lean_ctor_get(v_inst_576_, 1);
lean_inc(v_modifyRing_580_);
lean_dec_ref(v_inst_576_);
v_toPure_581_ = lean_ctor_get(v_toApplicative_577_, 1);
lean_inc_n(v_toPure_581_, 2);
v___f_582_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_582_, 0, v_toPure_581_);
lean_closure_set(v___f_582_, 1, v_modifyRing_580_);
lean_closure_set(v___f_582_, 2, v_toBind_578_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_583_, 0, v_toPure_581_);
lean_closure_set(v___f_583_, 1, v_inst_572_);
lean_closure_set(v___f_583_, 2, v_inst_573_);
lean_closure_set(v___f_583_, 3, v_inst_574_);
lean_closure_set(v___f_583_, 4, v_inst_575_);
lean_closure_set(v___f_583_, 5, v_toBind_578_);
lean_closure_set(v___f_583_, 6, v___f_582_);
v___x_584_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v_getRing_579_, v___f_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn(lean_object* v_m_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(v_inst_586_, v_inst_587_, v_inst_588_, v_inst_589_, v_inst_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0(lean_object* v_mulFn_592_, lean_object* v_s_593_){
_start:
{
lean_object* v_id_594_; lean_object* v_type_595_; lean_object* v_u_596_; lean_object* v_ringInst_597_; lean_object* v_semiringInst_598_; lean_object* v_charInst_x3f_599_; lean_object* v_addFn_x3f_600_; lean_object* v_subFn_x3f_601_; lean_object* v_negFn_x3f_602_; lean_object* v_powFn_x3f_603_; lean_object* v_intCastFn_x3f_604_; lean_object* v_natCastFn_x3f_605_; lean_object* v_one_x3f_606_; lean_object* v_vars_607_; lean_object* v_varMap_608_; lean_object* v_denote_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_617_; 
v_id_594_ = lean_ctor_get(v_s_593_, 0);
v_type_595_ = lean_ctor_get(v_s_593_, 1);
v_u_596_ = lean_ctor_get(v_s_593_, 2);
v_ringInst_597_ = lean_ctor_get(v_s_593_, 3);
v_semiringInst_598_ = lean_ctor_get(v_s_593_, 4);
v_charInst_x3f_599_ = lean_ctor_get(v_s_593_, 5);
v_addFn_x3f_600_ = lean_ctor_get(v_s_593_, 6);
v_subFn_x3f_601_ = lean_ctor_get(v_s_593_, 8);
v_negFn_x3f_602_ = lean_ctor_get(v_s_593_, 9);
v_powFn_x3f_603_ = lean_ctor_get(v_s_593_, 10);
v_intCastFn_x3f_604_ = lean_ctor_get(v_s_593_, 11);
v_natCastFn_x3f_605_ = lean_ctor_get(v_s_593_, 12);
v_one_x3f_606_ = lean_ctor_get(v_s_593_, 13);
v_vars_607_ = lean_ctor_get(v_s_593_, 14);
v_varMap_608_ = lean_ctor_get(v_s_593_, 15);
v_denote_609_ = lean_ctor_get(v_s_593_, 16);
v_isSharedCheck_617_ = !lean_is_exclusive(v_s_593_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v_s_593_, 7);
lean_dec(v_unused_618_);
v___x_611_ = v_s_593_;
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_denote_609_);
lean_inc(v_varMap_608_);
lean_inc(v_vars_607_);
lean_inc(v_one_x3f_606_);
lean_inc(v_natCastFn_x3f_605_);
lean_inc(v_intCastFn_x3f_604_);
lean_inc(v_powFn_x3f_603_);
lean_inc(v_negFn_x3f_602_);
lean_inc(v_subFn_x3f_601_);
lean_inc(v_addFn_x3f_600_);
lean_inc(v_charInst_x3f_599_);
lean_inc(v_semiringInst_598_);
lean_inc(v_ringInst_597_);
lean_inc(v_u_596_);
lean_inc(v_type_595_);
lean_inc(v_id_594_);
lean_dec(v_s_593_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_mulFn_592_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 7, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_id_594_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_type_595_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_u_596_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_ringInst_597_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_semiringInst_598_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_charInst_x3f_599_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_addFn_x3f_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_subFn_x3f_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 9, v_negFn_x3f_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 10, v_powFn_x3f_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 11, v_intCastFn_x3f_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 12, v_natCastFn_x3f_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 13, v_one_x3f_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 14, v_vars_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 15, v_varMap_608_);
lean_ctor_set(v_reuseFailAlloc_616_, 16, v_denote_609_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1(lean_object* v_toPure_619_, lean_object* v_mulFn_620_, lean_object* v_____r_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_apply_2(v_toPure_619_, lean_box(0), v_mulFn_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2(lean_object* v_toPure_623_, lean_object* v_modifyRing_624_, lean_object* v_toBind_625_, lean_object* v_mulFn_626_){
_start:
{
lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc_ref(v_mulFn_626_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_627_, 0, v_mulFn_626_);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_628_, 0, v_toPure_623_);
lean_closure_set(v___f_628_, 1, v_mulFn_626_);
v___x_629_ = lean_apply_1(v_modifyRing_624_, v___f_627_);
v___x_630_ = lean_apply_4(v_toBind_625_, lean_box(0), lean_box(0), v___x_629_, v___f_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3(lean_object* v_toPure_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_toBind_652_, lean_object* v___f_653_, lean_object* v_ring_654_){
_start:
{
lean_object* v_mulFn_x3f_655_; 
v_mulFn_x3f_655_ = lean_ctor_get(v_ring_654_, 7);
if (lean_obj_tag(v_mulFn_x3f_655_) == 1)
{
lean_object* v_val_656_; lean_object* v___x_657_; 
lean_inc_ref(v_mulFn_x3f_655_);
lean_dec_ref(v_ring_654_);
lean_dec(v___f_653_);
lean_dec(v_toBind_652_);
lean_dec_ref(v_inst_651_);
lean_dec_ref(v_inst_650_);
lean_dec_ref(v_inst_649_);
lean_dec(v_inst_648_);
v_val_656_ = lean_ctor_get(v_mulFn_x3f_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v_mulFn_x3f_655_, 1);
v___x_657_ = lean_apply_2(v_toPure_647_, lean_box(0), v_val_656_);
return v___x_657_;
}
else
{
lean_object* v_type_658_; lean_object* v_u_659_; lean_object* v_semiringInst_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_expectedInst_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_toPure_647_);
v_type_658_ = lean_ctor_get(v_ring_654_, 1);
lean_inc_ref_n(v_type_658_, 3);
v_u_659_ = lean_ctor_get(v_ring_654_, 2);
lean_inc_n(v_u_659_, 2);
v_semiringInst_660_ = lean_ctor_get(v_ring_654_, 4);
lean_inc_ref(v_semiringInst_660_);
lean_dec_ref(v_ring_654_);
v___x_661_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1));
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v_u_659_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
lean_inc_ref(v___x_663_);
v___x_664_ = l_Lean_mkConst(v___x_661_, v___x_663_);
v___x_665_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3));
v___x_666_ = l_Lean_mkConst(v___x_665_, v___x_663_);
v___x_667_ = l_Lean_mkAppB(v___x_666_, v_type_658_, v_semiringInst_660_);
v_expectedInst_668_ = l_Lean_mkAppB(v___x_664_, v_type_658_, v___x_667_);
v___x_669_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5));
v___x_670_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7));
v___x_671_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_648_, v_inst_649_, v_inst_650_, v_inst_651_, v_type_658_, v_u_659_, v___x_669_, v___x_670_, v_expectedInst_668_);
v___x_672_ = lean_apply_4(v_toBind_652_, lean_box(0), lean_box(0), v___x_671_, v___f_653_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_){
_start:
{
lean_object* v_toApplicative_678_; lean_object* v_toBind_679_; lean_object* v_getRing_680_; lean_object* v_modifyRing_681_; lean_object* v_toPure_682_; lean_object* v___f_683_; lean_object* v___f_684_; lean_object* v___x_685_; 
v_toApplicative_678_ = lean_ctor_get(v_inst_675_, 0);
v_toBind_679_ = lean_ctor_get(v_inst_675_, 1);
lean_inc_n(v_toBind_679_, 3);
v_getRing_680_ = lean_ctor_get(v_inst_677_, 0);
lean_inc(v_getRing_680_);
v_modifyRing_681_ = lean_ctor_get(v_inst_677_, 1);
lean_inc(v_modifyRing_681_);
lean_dec_ref(v_inst_677_);
v_toPure_682_ = lean_ctor_get(v_toApplicative_678_, 1);
lean_inc_n(v_toPure_682_, 2);
v___f_683_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_683_, 0, v_toPure_682_);
lean_closure_set(v___f_683_, 1, v_modifyRing_681_);
lean_closure_set(v___f_683_, 2, v_toBind_679_);
v___f_684_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_684_, 0, v_toPure_682_);
lean_closure_set(v___f_684_, 1, v_inst_673_);
lean_closure_set(v___f_684_, 2, v_inst_674_);
lean_closure_set(v___f_684_, 3, v_inst_675_);
lean_closure_set(v___f_684_, 4, v_inst_676_);
lean_closure_set(v___f_684_, 5, v_toBind_679_);
lean_closure_set(v___f_684_, 6, v___f_683_);
v___x_685_ = lean_apply_4(v_toBind_679_, lean_box(0), lean_box(0), v_getRing_680_, v___f_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn(lean_object* v_m_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_, v_inst_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0(lean_object* v_negFn_693_, lean_object* v_s_694_){
_start:
{
lean_object* v_id_695_; lean_object* v_type_696_; lean_object* v_u_697_; lean_object* v_ringInst_698_; lean_object* v_semiringInst_699_; lean_object* v_charInst_x3f_700_; lean_object* v_addFn_x3f_701_; lean_object* v_mulFn_x3f_702_; lean_object* v_subFn_x3f_703_; lean_object* v_powFn_x3f_704_; lean_object* v_intCastFn_x3f_705_; lean_object* v_natCastFn_x3f_706_; lean_object* v_one_x3f_707_; lean_object* v_vars_708_; lean_object* v_varMap_709_; lean_object* v_denote_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
v_id_695_ = lean_ctor_get(v_s_694_, 0);
v_type_696_ = lean_ctor_get(v_s_694_, 1);
v_u_697_ = lean_ctor_get(v_s_694_, 2);
v_ringInst_698_ = lean_ctor_get(v_s_694_, 3);
v_semiringInst_699_ = lean_ctor_get(v_s_694_, 4);
v_charInst_x3f_700_ = lean_ctor_get(v_s_694_, 5);
v_addFn_x3f_701_ = lean_ctor_get(v_s_694_, 6);
v_mulFn_x3f_702_ = lean_ctor_get(v_s_694_, 7);
v_subFn_x3f_703_ = lean_ctor_get(v_s_694_, 8);
v_powFn_x3f_704_ = lean_ctor_get(v_s_694_, 10);
v_intCastFn_x3f_705_ = lean_ctor_get(v_s_694_, 11);
v_natCastFn_x3f_706_ = lean_ctor_get(v_s_694_, 12);
v_one_x3f_707_ = lean_ctor_get(v_s_694_, 13);
v_vars_708_ = lean_ctor_get(v_s_694_, 14);
v_varMap_709_ = lean_ctor_get(v_s_694_, 15);
v_denote_710_ = lean_ctor_get(v_s_694_, 16);
v_isSharedCheck_718_ = !lean_is_exclusive(v_s_694_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_s_694_, 9);
lean_dec(v_unused_719_);
v___x_712_ = v_s_694_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_denote_710_);
lean_inc(v_varMap_709_);
lean_inc(v_vars_708_);
lean_inc(v_one_x3f_707_);
lean_inc(v_natCastFn_x3f_706_);
lean_inc(v_intCastFn_x3f_705_);
lean_inc(v_powFn_x3f_704_);
lean_inc(v_subFn_x3f_703_);
lean_inc(v_mulFn_x3f_702_);
lean_inc(v_addFn_x3f_701_);
lean_inc(v_charInst_x3f_700_);
lean_inc(v_semiringInst_699_);
lean_inc(v_ringInst_698_);
lean_inc(v_u_697_);
lean_inc(v_type_696_);
lean_inc(v_id_695_);
lean_dec(v_s_694_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_negFn_693_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 9, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_id_695_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_type_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_u_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_ringInst_698_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_semiringInst_699_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v_charInst_x3f_700_);
lean_ctor_set(v_reuseFailAlloc_717_, 6, v_addFn_x3f_701_);
lean_ctor_set(v_reuseFailAlloc_717_, 7, v_mulFn_x3f_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 8, v_subFn_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 9, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 10, v_powFn_x3f_704_);
lean_ctor_set(v_reuseFailAlloc_717_, 11, v_intCastFn_x3f_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 12, v_natCastFn_x3f_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 13, v_one_x3f_707_);
lean_ctor_set(v_reuseFailAlloc_717_, 14, v_vars_708_);
lean_ctor_set(v_reuseFailAlloc_717_, 15, v_varMap_709_);
lean_ctor_set(v_reuseFailAlloc_717_, 16, v_denote_710_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1(lean_object* v_toPure_720_, lean_object* v_negFn_721_, lean_object* v_____r_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_apply_2(v_toPure_720_, lean_box(0), v_negFn_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2(lean_object* v_toPure_724_, lean_object* v_modifyRing_725_, lean_object* v_toBind_726_, lean_object* v_negFn_727_){
_start:
{
lean_object* v___f_728_; lean_object* v___f_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_inc_ref(v_negFn_727_);
v___f_728_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_728_, 0, v_negFn_727_);
v___f_729_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_729_, 0, v_toPure_724_);
lean_closure_set(v___f_729_, 1, v_negFn_727_);
v___x_730_ = lean_apply_1(v_modifyRing_725_, v___f_728_);
v___x_731_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v___x_730_, v___f_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3(lean_object* v_toPure_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_toBind_750_, lean_object* v___f_751_, lean_object* v_ring_752_){
_start:
{
lean_object* v_negFn_x3f_753_; 
v_negFn_x3f_753_ = lean_ctor_get(v_ring_752_, 9);
if (lean_obj_tag(v_negFn_x3f_753_) == 1)
{
lean_object* v_val_754_; lean_object* v___x_755_; 
lean_inc_ref(v_negFn_x3f_753_);
lean_dec_ref(v_ring_752_);
lean_dec(v___f_751_);
lean_dec(v_toBind_750_);
lean_dec_ref(v_inst_749_);
lean_dec_ref(v_inst_748_);
lean_dec_ref(v_inst_747_);
lean_dec(v_inst_746_);
v_val_754_ = lean_ctor_get(v_negFn_x3f_753_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v_negFn_x3f_753_, 1);
v___x_755_ = lean_apply_2(v_toPure_745_, lean_box(0), v_val_754_);
return v___x_755_;
}
else
{
lean_object* v_type_756_; lean_object* v_u_757_; lean_object* v_ringInst_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_expectedInst_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v_toPure_745_);
v_type_756_ = lean_ctor_get(v_ring_752_, 1);
lean_inc_ref_n(v_type_756_, 2);
v_u_757_ = lean_ctor_get(v_ring_752_, 2);
lean_inc_n(v_u_757_, 2);
v_ringInst_758_ = lean_ctor_get(v_ring_752_, 3);
lean_inc_ref(v_ringInst_758_);
lean_dec_ref(v_ring_752_);
v___x_759_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1));
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_761_, 0, v_u_757_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_mkConst(v___x_759_, v___x_761_);
v_expectedInst_763_ = l_Lean_mkAppB(v___x_762_, v_type_756_, v_ringInst_758_);
v___x_764_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3));
v___x_765_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5));
v___x_766_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(v_inst_746_, v_inst_747_, v_inst_748_, v_inst_749_, v_type_756_, v_u_757_, v___x_764_, v___x_765_, v_expectedInst_763_);
v___x_767_ = lean_apply_4(v_toBind_750_, lean_box(0), lean_box(0), v___x_766_, v___f_751_);
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_inst_772_){
_start:
{
lean_object* v_toApplicative_773_; lean_object* v_toBind_774_; lean_object* v_getRing_775_; lean_object* v_modifyRing_776_; lean_object* v_toPure_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_780_; 
v_toApplicative_773_ = lean_ctor_get(v_inst_770_, 0);
v_toBind_774_ = lean_ctor_get(v_inst_770_, 1);
lean_inc_n(v_toBind_774_, 3);
v_getRing_775_ = lean_ctor_get(v_inst_772_, 0);
lean_inc(v_getRing_775_);
v_modifyRing_776_ = lean_ctor_get(v_inst_772_, 1);
lean_inc(v_modifyRing_776_);
lean_dec_ref(v_inst_772_);
v_toPure_777_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_inc_n(v_toPure_777_, 2);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_778_, 0, v_toPure_777_);
lean_closure_set(v___f_778_, 1, v_modifyRing_776_);
lean_closure_set(v___f_778_, 2, v_toBind_774_);
v___f_779_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_779_, 0, v_toPure_777_);
lean_closure_set(v___f_779_, 1, v_inst_768_);
lean_closure_set(v___f_779_, 2, v_inst_769_);
lean_closure_set(v___f_779_, 3, v_inst_770_);
lean_closure_set(v___f_779_, 4, v_inst_771_);
lean_closure_set(v___f_779_, 5, v_toBind_774_);
lean_closure_set(v___f_779_, 6, v___f_778_);
v___x_780_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v_getRing_775_, v___f_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn(lean_object* v_m_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(v_inst_782_, v_inst_783_, v_inst_784_, v_inst_785_, v_inst_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0(lean_object* v_powFn_788_, lean_object* v_s_789_){
_start:
{
lean_object* v_id_790_; lean_object* v_type_791_; lean_object* v_u_792_; lean_object* v_ringInst_793_; lean_object* v_semiringInst_794_; lean_object* v_charInst_x3f_795_; lean_object* v_addFn_x3f_796_; lean_object* v_mulFn_x3f_797_; lean_object* v_subFn_x3f_798_; lean_object* v_negFn_x3f_799_; lean_object* v_intCastFn_x3f_800_; lean_object* v_natCastFn_x3f_801_; lean_object* v_one_x3f_802_; lean_object* v_vars_803_; lean_object* v_varMap_804_; lean_object* v_denote_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_id_790_ = lean_ctor_get(v_s_789_, 0);
v_type_791_ = lean_ctor_get(v_s_789_, 1);
v_u_792_ = lean_ctor_get(v_s_789_, 2);
v_ringInst_793_ = lean_ctor_get(v_s_789_, 3);
v_semiringInst_794_ = lean_ctor_get(v_s_789_, 4);
v_charInst_x3f_795_ = lean_ctor_get(v_s_789_, 5);
v_addFn_x3f_796_ = lean_ctor_get(v_s_789_, 6);
v_mulFn_x3f_797_ = lean_ctor_get(v_s_789_, 7);
v_subFn_x3f_798_ = lean_ctor_get(v_s_789_, 8);
v_negFn_x3f_799_ = lean_ctor_get(v_s_789_, 9);
v_intCastFn_x3f_800_ = lean_ctor_get(v_s_789_, 11);
v_natCastFn_x3f_801_ = lean_ctor_get(v_s_789_, 12);
v_one_x3f_802_ = lean_ctor_get(v_s_789_, 13);
v_vars_803_ = lean_ctor_get(v_s_789_, 14);
v_varMap_804_ = lean_ctor_get(v_s_789_, 15);
v_denote_805_ = lean_ctor_get(v_s_789_, 16);
v_isSharedCheck_813_ = !lean_is_exclusive(v_s_789_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_s_789_, 10);
lean_dec(v_unused_814_);
v___x_807_ = v_s_789_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_denote_805_);
lean_inc(v_varMap_804_);
lean_inc(v_vars_803_);
lean_inc(v_one_x3f_802_);
lean_inc(v_natCastFn_x3f_801_);
lean_inc(v_intCastFn_x3f_800_);
lean_inc(v_negFn_x3f_799_);
lean_inc(v_subFn_x3f_798_);
lean_inc(v_mulFn_x3f_797_);
lean_inc(v_addFn_x3f_796_);
lean_inc(v_charInst_x3f_795_);
lean_inc(v_semiringInst_794_);
lean_inc(v_ringInst_793_);
lean_inc(v_u_792_);
lean_inc(v_type_791_);
lean_inc(v_id_790_);
lean_dec(v_s_789_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_powFn_788_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 10, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_id_790_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_type_791_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_u_792_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_ringInst_793_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_semiringInst_794_);
lean_ctor_set(v_reuseFailAlloc_812_, 5, v_charInst_x3f_795_);
lean_ctor_set(v_reuseFailAlloc_812_, 6, v_addFn_x3f_796_);
lean_ctor_set(v_reuseFailAlloc_812_, 7, v_mulFn_x3f_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 8, v_subFn_x3f_798_);
lean_ctor_set(v_reuseFailAlloc_812_, 9, v_negFn_x3f_799_);
lean_ctor_set(v_reuseFailAlloc_812_, 10, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 11, v_intCastFn_x3f_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 12, v_natCastFn_x3f_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 13, v_one_x3f_802_);
lean_ctor_set(v_reuseFailAlloc_812_, 14, v_vars_803_);
lean_ctor_set(v_reuseFailAlloc_812_, 15, v_varMap_804_);
lean_ctor_set(v_reuseFailAlloc_812_, 16, v_denote_805_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1(lean_object* v_toPure_815_, lean_object* v_powFn_816_, lean_object* v_____r_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = lean_apply_2(v_toPure_815_, lean_box(0), v_powFn_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2(lean_object* v_toPure_819_, lean_object* v_modifyRing_820_, lean_object* v_toBind_821_, lean_object* v_powFn_822_){
_start:
{
lean_object* v___f_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_inc_ref(v_powFn_822_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_823_, 0, v_powFn_822_);
v___f_824_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_824_, 0, v_toPure_819_);
lean_closure_set(v___f_824_, 1, v_powFn_822_);
v___x_825_ = lean_apply_1(v_modifyRing_820_, v___f_823_);
v___x_826_ = lean_apply_4(v_toBind_821_, lean_box(0), lean_box(0), v___x_825_, v___f_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3(lean_object* v_toPure_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_toBind_832_, lean_object* v___f_833_, lean_object* v_ring_834_){
_start:
{
lean_object* v_powFn_x3f_835_; 
v_powFn_x3f_835_ = lean_ctor_get(v_ring_834_, 10);
if (lean_obj_tag(v_powFn_x3f_835_) == 1)
{
lean_object* v_val_836_; lean_object* v___x_837_; 
lean_inc_ref(v_powFn_x3f_835_);
lean_dec_ref(v_ring_834_);
lean_dec(v___f_833_);
lean_dec(v_toBind_832_);
lean_dec_ref(v_inst_831_);
lean_dec_ref(v_inst_830_);
lean_dec_ref(v_inst_829_);
lean_dec(v_inst_828_);
v_val_836_ = lean_ctor_get(v_powFn_x3f_835_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v_powFn_x3f_835_, 1);
v___x_837_ = lean_apply_2(v_toPure_827_, lean_box(0), v_val_836_);
return v___x_837_;
}
else
{
lean_object* v_type_838_; lean_object* v_u_839_; lean_object* v_semiringInst_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v_toPure_827_);
v_type_838_ = lean_ctor_get(v_ring_834_, 1);
lean_inc_ref(v_type_838_);
v_u_839_ = lean_ctor_get(v_ring_834_, 2);
lean_inc(v_u_839_);
v_semiringInst_840_ = lean_ctor_get(v_ring_834_, 4);
lean_inc_ref(v_semiringInst_840_);
lean_dec_ref(v_ring_834_);
v___x_841_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_828_, v_inst_829_, v_inst_830_, v_inst_831_, v_u_839_, v_type_838_, v_semiringInst_840_);
v___x_842_ = lean_apply_4(v_toBind_832_, lean_box(0), lean_box(0), v___x_841_, v___f_833_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_){
_start:
{
lean_object* v_toApplicative_848_; lean_object* v_toBind_849_; lean_object* v_getRing_850_; lean_object* v_modifyRing_851_; lean_object* v_toPure_852_; lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___x_855_; 
v_toApplicative_848_ = lean_ctor_get(v_inst_845_, 0);
v_toBind_849_ = lean_ctor_get(v_inst_845_, 1);
lean_inc_n(v_toBind_849_, 3);
v_getRing_850_ = lean_ctor_get(v_inst_847_, 0);
lean_inc(v_getRing_850_);
v_modifyRing_851_ = lean_ctor_get(v_inst_847_, 1);
lean_inc(v_modifyRing_851_);
lean_dec_ref(v_inst_847_);
v_toPure_852_ = lean_ctor_get(v_toApplicative_848_, 1);
lean_inc_n(v_toPure_852_, 2);
v___f_853_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_853_, 0, v_toPure_852_);
lean_closure_set(v___f_853_, 1, v_modifyRing_851_);
lean_closure_set(v___f_853_, 2, v_toBind_849_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_854_, 0, v_toPure_852_);
lean_closure_set(v___f_854_, 1, v_inst_843_);
lean_closure_set(v___f_854_, 2, v_inst_844_);
lean_closure_set(v___f_854_, 3, v_inst_845_);
lean_closure_set(v___f_854_, 4, v_inst_846_);
lean_closure_set(v___f_854_, 5, v_toBind_849_);
lean_closure_set(v___f_854_, 6, v___f_853_);
v___x_855_ = lean_apply_4(v_toBind_849_, lean_box(0), lean_box(0), v_getRing_850_, v___f_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn(lean_object* v_m_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_inst_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(v_inst_857_, v_inst_858_, v_inst_859_, v_inst_860_, v_inst_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_863_, lean_object* v_s_864_){
_start:
{
lean_object* v_id_865_; lean_object* v_type_866_; lean_object* v_u_867_; lean_object* v_ringInst_868_; lean_object* v_semiringInst_869_; lean_object* v_charInst_x3f_870_; lean_object* v_addFn_x3f_871_; lean_object* v_mulFn_x3f_872_; lean_object* v_subFn_x3f_873_; lean_object* v_negFn_x3f_874_; lean_object* v_powFn_x3f_875_; lean_object* v_natCastFn_x3f_876_; lean_object* v_one_x3f_877_; lean_object* v_vars_878_; lean_object* v_varMap_879_; lean_object* v_denote_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_id_865_ = lean_ctor_get(v_s_864_, 0);
v_type_866_ = lean_ctor_get(v_s_864_, 1);
v_u_867_ = lean_ctor_get(v_s_864_, 2);
v_ringInst_868_ = lean_ctor_get(v_s_864_, 3);
v_semiringInst_869_ = lean_ctor_get(v_s_864_, 4);
v_charInst_x3f_870_ = lean_ctor_get(v_s_864_, 5);
v_addFn_x3f_871_ = lean_ctor_get(v_s_864_, 6);
v_mulFn_x3f_872_ = lean_ctor_get(v_s_864_, 7);
v_subFn_x3f_873_ = lean_ctor_get(v_s_864_, 8);
v_negFn_x3f_874_ = lean_ctor_get(v_s_864_, 9);
v_powFn_x3f_875_ = lean_ctor_get(v_s_864_, 10);
v_natCastFn_x3f_876_ = lean_ctor_get(v_s_864_, 12);
v_one_x3f_877_ = lean_ctor_get(v_s_864_, 13);
v_vars_878_ = lean_ctor_get(v_s_864_, 14);
v_varMap_879_ = lean_ctor_get(v_s_864_, 15);
v_denote_880_ = lean_ctor_get(v_s_864_, 16);
v_isSharedCheck_888_ = !lean_is_exclusive(v_s_864_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_s_864_, 11);
lean_dec(v_unused_889_);
v___x_882_ = v_s_864_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_denote_880_);
lean_inc(v_varMap_879_);
lean_inc(v_vars_878_);
lean_inc(v_one_x3f_877_);
lean_inc(v_natCastFn_x3f_876_);
lean_inc(v_powFn_x3f_875_);
lean_inc(v_negFn_x3f_874_);
lean_inc(v_subFn_x3f_873_);
lean_inc(v_mulFn_x3f_872_);
lean_inc(v_addFn_x3f_871_);
lean_inc(v_charInst_x3f_870_);
lean_inc(v_semiringInst_869_);
lean_inc(v_ringInst_868_);
lean_inc(v_u_867_);
lean_inc(v_type_866_);
lean_inc(v_id_865_);
lean_dec(v_s_864_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v_intCastFn_863_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 11, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_id_865_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_type_866_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_u_867_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v_ringInst_868_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_semiringInst_869_);
lean_ctor_set(v_reuseFailAlloc_887_, 5, v_charInst_x3f_870_);
lean_ctor_set(v_reuseFailAlloc_887_, 6, v_addFn_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_887_, 7, v_mulFn_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_887_, 8, v_subFn_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_887_, 9, v_negFn_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_887_, 10, v_powFn_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_887_, 11, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 12, v_natCastFn_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 13, v_one_x3f_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 14, v_vars_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 15, v_varMap_879_);
lean_ctor_set(v_reuseFailAlloc_887_, 16, v_denote_880_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1(lean_object* v_toPure_890_, lean_object* v_intCastFn_891_, lean_object* v_____r_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_apply_2(v_toPure_890_, lean_box(0), v_intCastFn_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2(lean_object* v_toPure_894_, lean_object* v_modifyRing_895_, lean_object* v_toBind_896_, lean_object* v_intCastFn_897_){
_start:
{
lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_inc_ref(v_intCastFn_897_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_898_, 0, v_intCastFn_897_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_899_, 0, v_toPure_894_);
lean_closure_set(v___f_899_, 1, v_intCastFn_897_);
v___x_900_ = lean_apply_1(v_modifyRing_895_, v___f_898_);
v___x_901_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_900_, v___f_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3(lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v_type_905_, lean_object* v_canonExpr_906_, lean_object* v_toBind_907_, lean_object* v___f_908_, lean_object* v_inst_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_910_ = l_Lean_Name_mkStr2(v___x_902_, v___x_903_);
v___x_911_ = l_Lean_mkConst(v___x_910_, v___x_904_);
v___x_912_ = l_Lean_mkAppB(v___x_911_, v_type_905_, v_inst_909_);
v___x_913_ = lean_apply_1(v_canonExpr_906_, v___x_912_);
v___x_914_ = lean_apply_4(v_toBind_907_, lean_box(0), lean_box(0), v___x_913_, v___f_908_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7(lean_object* v_toPure_920_, lean_object* v_inst_x27_921_, lean_object* v_toBind_922_, lean_object* v___f_923_, lean_object* v___f_924_, lean_object* v_inst_925_, lean_object* v_____do__lift_926_){
_start:
{
if (lean_obj_tag(v_____do__lift_926_) == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v_inst_925_);
lean_dec(v___f_924_);
v___x_927_ = lean_apply_2(v_toPure_920_, lean_box(0), v_inst_x27_921_);
v___x_928_ = lean_apply_4(v_toBind_922_, lean_box(0), lean_box(0), v___x_927_, v___f_923_);
return v___x_928_;
}
else
{
lean_object* v_val_929_; lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v___f_923_);
v_val_929_ = lean_ctor_get(v_____do__lift_926_, 0);
lean_inc_n(v_val_929_, 2);
lean_dec_ref_known(v_____do__lift_926_, 1);
lean_inc(v_toBind_922_);
v___f_930_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_930_, 0, v_toPure_920_);
lean_closure_set(v___f_930_, 1, v_val_929_);
lean_closure_set(v___f_930_, 2, v_toBind_922_);
lean_closure_set(v___f_930_, 3, v___f_924_);
v___x_931_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2));
v___x_932_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(v___x_932_, 0, v___x_931_);
lean_closure_set(v___x_932_, 1, v_val_929_);
lean_closure_set(v___x_932_, 2, v_inst_x27_921_);
v___x_933_ = lean_apply_2(v_inst_925_, lean_box(0), v___x_932_);
v___x_934_ = lean_apply_4(v_toBind_922_, lean_box(0), lean_box(0), v___x_933_, v___f_930_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4(lean_object* v_toPure_944_, lean_object* v_inst_945_, lean_object* v_toBind_946_, lean_object* v___f_947_, lean_object* v_inst_948_, lean_object* v_ring_949_){
_start:
{
lean_object* v_intCastFn_x3f_950_; 
v_intCastFn_x3f_950_ = lean_ctor_get(v_ring_949_, 11);
if (lean_obj_tag(v_intCastFn_x3f_950_) == 1)
{
lean_object* v_val_951_; lean_object* v___x_952_; 
lean_inc_ref(v_intCastFn_x3f_950_);
lean_dec_ref(v_ring_949_);
lean_dec(v_inst_948_);
lean_dec(v___f_947_);
lean_dec(v_toBind_946_);
lean_dec_ref(v_inst_945_);
v_val_951_ = lean_ctor_get(v_intCastFn_x3f_950_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v_intCastFn_x3f_950_, 1);
v___x_952_ = lean_apply_2(v_toPure_944_, lean_box(0), v_val_951_);
return v___x_952_;
}
else
{
lean_object* v_type_953_; lean_object* v_u_954_; lean_object* v_ringInst_955_; lean_object* v_canonExpr_956_; lean_object* v_synthInstance_x3f_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_978_; 
v_type_953_ = lean_ctor_get(v_ring_949_, 1);
lean_inc_ref(v_type_953_);
v_u_954_ = lean_ctor_get(v_ring_949_, 2);
lean_inc(v_u_954_);
v_ringInst_955_ = lean_ctor_get(v_ring_949_, 3);
lean_inc_ref(v_ringInst_955_);
lean_dec_ref(v_ring_949_);
v_canonExpr_956_ = lean_ctor_get(v_inst_945_, 0);
v_synthInstance_x3f_957_ = lean_ctor_get(v_inst_945_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_inst_945_);
if (v_isSharedCheck_978_ == 0)
{
v___x_959_ = v_inst_945_;
v_isShared_960_ = v_isSharedCheck_978_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_synthInstance_x3f_957_);
lean_inc(v_canonExpr_956_);
lean_dec(v_inst_945_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_978_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_961_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0));
v___x_962_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1));
v___x_963_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
lean_ctor_set(v___x_959_, 1, v___x_963_);
lean_ctor_set(v___x_959_, 0, v_u_954_);
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_u_954_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_977_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v_inst_x27_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___f_970_; lean_object* v___f_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_instType_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_inc_ref_n(v___x_965_, 2);
v___x_966_ = l_Lean_mkConst(v___x_962_, v___x_965_);
lean_inc_ref_n(v_type_953_, 2);
v_inst_x27_967_ = l_Lean_mkAppB(v___x_966_, v_type_953_, v_ringInst_955_);
v___x_968_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_946_, 2);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_969_, 0, v___x_968_);
lean_closure_set(v___f_969_, 1, v___x_961_);
lean_closure_set(v___f_969_, 2, v___x_965_);
lean_closure_set(v___f_969_, 3, v_type_953_);
lean_closure_set(v___f_969_, 4, v_canonExpr_956_);
lean_closure_set(v___f_969_, 5, v_toBind_946_);
lean_closure_set(v___f_969_, 6, v___f_947_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_970_, 0, v___f_969_);
lean_inc_ref(v___f_970_);
v___f_971_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_971_, 0, v_toPure_944_);
lean_closure_set(v___f_971_, 1, v_inst_x27_967_);
lean_closure_set(v___f_971_, 2, v_toBind_946_);
lean_closure_set(v___f_971_, 3, v___f_970_);
lean_closure_set(v___f_971_, 4, v___f_970_);
lean_closure_set(v___f_971_, 5, v_inst_948_);
v___x_972_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3));
v___x_973_ = l_Lean_mkConst(v___x_972_, v___x_965_);
v_instType_974_ = l_Lean_Expr_app___override(v___x_973_, v_type_953_);
v___x_975_ = lean_apply_1(v_synthInstance_x3f_957_, v_instType_974_);
v___x_976_ = lean_apply_4(v_toBind_946_, lean_box(0), lean_box(0), v___x_975_, v___f_971_);
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_inst_982_){
_start:
{
lean_object* v_toApplicative_983_; lean_object* v_toBind_984_; lean_object* v_getRing_985_; lean_object* v_modifyRing_986_; lean_object* v_toPure_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___x_990_; 
v_toApplicative_983_ = lean_ctor_get(v_inst_980_, 0);
lean_inc_ref(v_toApplicative_983_);
v_toBind_984_ = lean_ctor_get(v_inst_980_, 1);
lean_inc_n(v_toBind_984_, 3);
lean_dec_ref(v_inst_980_);
v_getRing_985_ = lean_ctor_get(v_inst_982_, 0);
lean_inc(v_getRing_985_);
v_modifyRing_986_ = lean_ctor_get(v_inst_982_, 1);
lean_inc(v_modifyRing_986_);
lean_dec_ref(v_inst_982_);
v_toPure_987_ = lean_ctor_get(v_toApplicative_983_, 1);
lean_inc_n(v_toPure_987_, 2);
lean_dec_ref(v_toApplicative_983_);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_988_, 0, v_toPure_987_);
lean_closure_set(v___f_988_, 1, v_modifyRing_986_);
lean_closure_set(v___f_988_, 2, v_toBind_984_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_989_, 0, v_toPure_987_);
lean_closure_set(v___f_989_, 1, v_inst_981_);
lean_closure_set(v___f_989_, 2, v_toBind_984_);
lean_closure_set(v___f_989_, 3, v___f_988_);
lean_closure_set(v___f_989_, 4, v_inst_979_);
v___x_990_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v_getRing_985_, v___f_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn(lean_object* v_m_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(v_inst_992_, v_inst_993_, v_inst_994_, v_inst_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_997_, lean_object* v_s_998_){
_start:
{
lean_object* v_id_999_; lean_object* v_type_1000_; lean_object* v_u_1001_; lean_object* v_ringInst_1002_; lean_object* v_semiringInst_1003_; lean_object* v_charInst_x3f_1004_; lean_object* v_addFn_x3f_1005_; lean_object* v_mulFn_x3f_1006_; lean_object* v_subFn_x3f_1007_; lean_object* v_negFn_x3f_1008_; lean_object* v_powFn_x3f_1009_; lean_object* v_intCastFn_x3f_1010_; lean_object* v_one_x3f_1011_; lean_object* v_vars_1012_; lean_object* v_varMap_1013_; lean_object* v_denote_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_id_999_ = lean_ctor_get(v_s_998_, 0);
v_type_1000_ = lean_ctor_get(v_s_998_, 1);
v_u_1001_ = lean_ctor_get(v_s_998_, 2);
v_ringInst_1002_ = lean_ctor_get(v_s_998_, 3);
v_semiringInst_1003_ = lean_ctor_get(v_s_998_, 4);
v_charInst_x3f_1004_ = lean_ctor_get(v_s_998_, 5);
v_addFn_x3f_1005_ = lean_ctor_get(v_s_998_, 6);
v_mulFn_x3f_1006_ = lean_ctor_get(v_s_998_, 7);
v_subFn_x3f_1007_ = lean_ctor_get(v_s_998_, 8);
v_negFn_x3f_1008_ = lean_ctor_get(v_s_998_, 9);
v_powFn_x3f_1009_ = lean_ctor_get(v_s_998_, 10);
v_intCastFn_x3f_1010_ = lean_ctor_get(v_s_998_, 11);
v_one_x3f_1011_ = lean_ctor_get(v_s_998_, 13);
v_vars_1012_ = lean_ctor_get(v_s_998_, 14);
v_varMap_1013_ = lean_ctor_get(v_s_998_, 15);
v_denote_1014_ = lean_ctor_get(v_s_998_, 16);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_s_998_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_s_998_, 12);
lean_dec(v_unused_1023_);
v___x_1016_ = v_s_998_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_denote_1014_);
lean_inc(v_varMap_1013_);
lean_inc(v_vars_1012_);
lean_inc(v_one_x3f_1011_);
lean_inc(v_intCastFn_x3f_1010_);
lean_inc(v_powFn_x3f_1009_);
lean_inc(v_negFn_x3f_1008_);
lean_inc(v_subFn_x3f_1007_);
lean_inc(v_mulFn_x3f_1006_);
lean_inc(v_addFn_x3f_1005_);
lean_inc(v_charInst_x3f_1004_);
lean_inc(v_semiringInst_1003_);
lean_inc(v_ringInst_1002_);
lean_inc(v_u_1001_);
lean_inc(v_type_1000_);
lean_inc(v_id_999_);
lean_dec(v_s_998_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_natCastFn_997_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 12, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_id_999_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_type_1000_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_u_1001_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_ringInst_1002_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_semiringInst_1003_);
lean_ctor_set(v_reuseFailAlloc_1021_, 5, v_charInst_x3f_1004_);
lean_ctor_set(v_reuseFailAlloc_1021_, 6, v_addFn_x3f_1005_);
lean_ctor_set(v_reuseFailAlloc_1021_, 7, v_mulFn_x3f_1006_);
lean_ctor_set(v_reuseFailAlloc_1021_, 8, v_subFn_x3f_1007_);
lean_ctor_set(v_reuseFailAlloc_1021_, 9, v_negFn_x3f_1008_);
lean_ctor_set(v_reuseFailAlloc_1021_, 10, v_powFn_x3f_1009_);
lean_ctor_set(v_reuseFailAlloc_1021_, 11, v_intCastFn_x3f_1010_);
lean_ctor_set(v_reuseFailAlloc_1021_, 12, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 13, v_one_x3f_1011_);
lean_ctor_set(v_reuseFailAlloc_1021_, 14, v_vars_1012_);
lean_ctor_set(v_reuseFailAlloc_1021_, 15, v_varMap_1013_);
lean_ctor_set(v_reuseFailAlloc_1021_, 16, v_denote_1014_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1024_, lean_object* v_natCastFn_1025_, lean_object* v_____r_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_apply_2(v_toPure_1024_, lean_box(0), v_natCastFn_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1028_, lean_object* v_modifyRing_1029_, lean_object* v_toBind_1030_, lean_object* v_natCastFn_1031_){
_start:
{
lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_inc_ref(v_natCastFn_1031_);
v___f_1032_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1032_, 0, v_natCastFn_1031_);
v___f_1033_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1033_, 0, v_toPure_1028_);
lean_closure_set(v___f_1033_, 1, v_natCastFn_1031_);
v___x_1034_ = lean_apply_1(v_modifyRing_1029_, v___f_1032_);
v___x_1035_ = lean_apply_4(v_toBind_1030_, lean_box(0), lean_box(0), v___x_1034_, v___f_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_toBind_1040_, lean_object* v___f_1041_, lean_object* v_ring_1042_){
_start:
{
lean_object* v_natCastFn_x3f_1043_; 
v_natCastFn_x3f_1043_ = lean_ctor_get(v_ring_1042_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1043_) == 1)
{
lean_object* v_val_1044_; lean_object* v___x_1045_; 
lean_inc_ref(v_natCastFn_x3f_1043_);
lean_dec_ref(v_ring_1042_);
lean_dec(v___f_1041_);
lean_dec(v_toBind_1040_);
lean_dec_ref(v_inst_1039_);
lean_dec_ref(v_inst_1038_);
lean_dec(v_inst_1037_);
v_val_1044_ = lean_ctor_get(v_natCastFn_x3f_1043_, 0);
lean_inc(v_val_1044_);
lean_dec_ref_known(v_natCastFn_x3f_1043_, 1);
v___x_1045_ = lean_apply_2(v_toPure_1036_, lean_box(0), v_val_1044_);
return v___x_1045_;
}
else
{
lean_object* v_type_1046_; lean_object* v_u_1047_; lean_object* v_semiringInst_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec(v_toPure_1036_);
v_type_1046_ = lean_ctor_get(v_ring_1042_, 1);
lean_inc_ref(v_type_1046_);
v_u_1047_ = lean_ctor_get(v_ring_1042_, 2);
lean_inc(v_u_1047_);
v_semiringInst_1048_ = lean_ctor_get(v_ring_1042_, 4);
lean_inc_ref(v_semiringInst_1048_);
lean_dec_ref(v_ring_1042_);
v___x_1049_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_1037_, v_inst_1038_, v_inst_1039_, v_u_1047_, v_type_1046_, v_semiringInst_1048_);
v___x_1050_ = lean_apply_4(v_toBind_1040_, lean_box(0), lean_box(0), v___x_1049_, v___f_1041_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_){
_start:
{
lean_object* v_toApplicative_1055_; lean_object* v_toBind_1056_; lean_object* v_getRing_1057_; lean_object* v_modifyRing_1058_; lean_object* v_toPure_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; 
v_toApplicative_1055_ = lean_ctor_get(v_inst_1052_, 0);
v_toBind_1056_ = lean_ctor_get(v_inst_1052_, 1);
lean_inc_n(v_toBind_1056_, 3);
v_getRing_1057_ = lean_ctor_get(v_inst_1054_, 0);
lean_inc(v_getRing_1057_);
v_modifyRing_1058_ = lean_ctor_get(v_inst_1054_, 1);
lean_inc(v_modifyRing_1058_);
lean_dec_ref(v_inst_1054_);
v_toPure_1059_ = lean_ctor_get(v_toApplicative_1055_, 1);
lean_inc_n(v_toPure_1059_, 2);
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1060_, 0, v_toPure_1059_);
lean_closure_set(v___f_1060_, 1, v_modifyRing_1058_);
lean_closure_set(v___f_1060_, 2, v_toBind_1056_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1061_, 0, v_toPure_1059_);
lean_closure_set(v___f_1061_, 1, v_inst_1051_);
lean_closure_set(v___f_1061_, 2, v_inst_1052_);
lean_closure_set(v___f_1061_, 3, v_inst_1053_);
lean_closure_set(v___f_1061_, 4, v_toBind_1056_);
lean_closure_set(v___f_1061_, 5, v___f_1060_);
v___x_1062_ = lean_apply_4(v_toBind_1056_, lean_box(0), lean_box(0), v_getRing_1057_, v___f_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn(lean_object* v_m_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(v_inst_1064_, v_inst_1065_, v_inst_1066_, v_inst_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_1069_; lean_object* v_n_1070_; 
v___x_1069_ = lean_unsigned_to_nat(1u);
v_n_1070_ = l_Lean_mkRawNatLit(v___x_1069_);
return v_n_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object* v_inst_1081_, lean_object* v_u_1082_, lean_object* v_type_1083_, lean_object* v_semiringInst_1084_){
_start:
{
lean_object* v_canonExpr_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1101_; 
v_canonExpr_1085_ = lean_ctor_get(v_inst_1081_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_inst_1081_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v_inst_1081_, 1);
lean_dec(v_unused_1102_);
v___x_1087_ = v_inst_1081_;
v_isShared_1088_ = v_isSharedCheck_1101_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_canonExpr_1085_);
lean_dec(v_inst_1081_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1101_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_n_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v_n_1089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
v___x_1090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2));
v___x_1091_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 1);
lean_ctor_set(v___x_1087_, 1, v___x_1091_);
lean_ctor_set(v___x_1087_, 0, v_u_1082_);
v___x_1093_ = v___x_1087_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_u_1082_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v_ofNatInst_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_inc_ref(v___x_1093_);
v___x_1094_ = l_Lean_mkConst(v___x_1090_, v___x_1093_);
lean_inc_ref(v_type_1083_);
v_ofNatInst_1095_ = l_Lean_mkApp3(v___x_1094_, v_type_1083_, v_semiringInst_1084_, v_n_1089_);
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4));
v___x_1097_ = l_Lean_mkConst(v___x_1096_, v___x_1093_);
v___x_1098_ = l_Lean_mkApp3(v___x_1097_, v_type_1083_, v_n_1089_, v_ofNatInst_1095_);
v___x_1099_ = lean_apply_1(v_canonExpr_1085_, v___x_1098_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object* v_m_1103_, lean_object* v_inst_1104_, lean_object* v_u_1105_, lean_object* v_type_1106_, lean_object* v_semiringInst_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_1104_, v_u_1105_, v_type_1106_, v_semiringInst_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0(lean_object* v_one_1109_, lean_object* v_s_1110_){
_start:
{
lean_object* v_id_1111_; lean_object* v_type_1112_; lean_object* v_u_1113_; lean_object* v_ringInst_1114_; lean_object* v_semiringInst_1115_; lean_object* v_charInst_x3f_1116_; lean_object* v_addFn_x3f_1117_; lean_object* v_mulFn_x3f_1118_; lean_object* v_subFn_x3f_1119_; lean_object* v_negFn_x3f_1120_; lean_object* v_powFn_x3f_1121_; lean_object* v_intCastFn_x3f_1122_; lean_object* v_natCastFn_x3f_1123_; lean_object* v_vars_1124_; lean_object* v_varMap_1125_; lean_object* v_denote_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v_id_1111_ = lean_ctor_get(v_s_1110_, 0);
v_type_1112_ = lean_ctor_get(v_s_1110_, 1);
v_u_1113_ = lean_ctor_get(v_s_1110_, 2);
v_ringInst_1114_ = lean_ctor_get(v_s_1110_, 3);
v_semiringInst_1115_ = lean_ctor_get(v_s_1110_, 4);
v_charInst_x3f_1116_ = lean_ctor_get(v_s_1110_, 5);
v_addFn_x3f_1117_ = lean_ctor_get(v_s_1110_, 6);
v_mulFn_x3f_1118_ = lean_ctor_get(v_s_1110_, 7);
v_subFn_x3f_1119_ = lean_ctor_get(v_s_1110_, 8);
v_negFn_x3f_1120_ = lean_ctor_get(v_s_1110_, 9);
v_powFn_x3f_1121_ = lean_ctor_get(v_s_1110_, 10);
v_intCastFn_x3f_1122_ = lean_ctor_get(v_s_1110_, 11);
v_natCastFn_x3f_1123_ = lean_ctor_get(v_s_1110_, 12);
v_vars_1124_ = lean_ctor_get(v_s_1110_, 14);
v_varMap_1125_ = lean_ctor_get(v_s_1110_, 15);
v_denote_1126_ = lean_ctor_get(v_s_1110_, 16);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_s_1110_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v_s_1110_, 13);
lean_dec(v_unused_1135_);
v___x_1128_ = v_s_1110_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_denote_1126_);
lean_inc(v_varMap_1125_);
lean_inc(v_vars_1124_);
lean_inc(v_natCastFn_x3f_1123_);
lean_inc(v_intCastFn_x3f_1122_);
lean_inc(v_powFn_x3f_1121_);
lean_inc(v_negFn_x3f_1120_);
lean_inc(v_subFn_x3f_1119_);
lean_inc(v_mulFn_x3f_1118_);
lean_inc(v_addFn_x3f_1117_);
lean_inc(v_charInst_x3f_1116_);
lean_inc(v_semiringInst_1115_);
lean_inc(v_ringInst_1114_);
lean_inc(v_u_1113_);
lean_inc(v_type_1112_);
lean_inc(v_id_1111_);
lean_dec(v_s_1110_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_one_1109_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 13, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_id_1111_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_type_1112_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_u_1113_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_ringInst_1114_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_semiringInst_1115_);
lean_ctor_set(v_reuseFailAlloc_1133_, 5, v_charInst_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1133_, 6, v_addFn_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1133_, 7, v_mulFn_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1133_, 8, v_subFn_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1133_, 9, v_negFn_x3f_1120_);
lean_ctor_set(v_reuseFailAlloc_1133_, 10, v_powFn_x3f_1121_);
lean_ctor_set(v_reuseFailAlloc_1133_, 11, v_intCastFn_x3f_1122_);
lean_ctor_set(v_reuseFailAlloc_1133_, 12, v_natCastFn_x3f_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 13, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1133_, 14, v_vars_1124_);
lean_ctor_set(v_reuseFailAlloc_1133_, 15, v_varMap_1125_);
lean_ctor_set(v_reuseFailAlloc_1133_, 16, v_denote_1126_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1(lean_object* v_toPure_1136_, lean_object* v_one_1137_, lean_object* v_____r_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_apply_2(v_toPure_1136_, lean_box(0), v_one_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2(lean_object* v_one_1140_, lean_object* v_inst_1141_, lean_object* v_toBind_1142_, lean_object* v___f_1143_, lean_object* v_____r_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_internalize___boxed), 14, 3);
lean_closure_set(v___x_1147_, 0, v_one_1140_);
lean_closure_set(v___x_1147_, 1, v___x_1145_);
lean_closure_set(v___x_1147_, 2, v___x_1146_);
v___x_1148_ = lean_apply_2(v_inst_1141_, lean_box(0), v___x_1147_);
v___x_1149_ = lean_apply_4(v_toBind_1142_, lean_box(0), lean_box(0), v___x_1148_, v___f_1143_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3(lean_object* v_toPure_1150_, lean_object* v_inst_1151_, lean_object* v_toBind_1152_, lean_object* v_modifyRing_1153_, lean_object* v_one_1154_){
_start:
{
lean_object* v___f_1155_; lean_object* v___f_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_inc_ref_n(v_one_1154_, 2);
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1155_, 0, v_one_1154_);
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1156_, 0, v_toPure_1150_);
lean_closure_set(v___f_1156_, 1, v_one_1154_);
lean_inc(v_toBind_1152_);
v___f_1157_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1157_, 0, v_one_1154_);
lean_closure_set(v___f_1157_, 1, v_inst_1151_);
lean_closure_set(v___f_1157_, 2, v_toBind_1152_);
lean_closure_set(v___f_1157_, 3, v___f_1156_);
v___x_1158_ = lean_apply_1(v_modifyRing_1153_, v___f_1155_);
v___x_1159_ = lean_apply_4(v_toBind_1152_, lean_box(0), lean_box(0), v___x_1158_, v___f_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4(lean_object* v_toPure_1160_, lean_object* v_inst_1161_, lean_object* v_toBind_1162_, lean_object* v___f_1163_, lean_object* v_ring_1164_){
_start:
{
lean_object* v_one_x3f_1165_; 
v_one_x3f_1165_ = lean_ctor_get(v_ring_1164_, 13);
if (lean_obj_tag(v_one_x3f_1165_) == 1)
{
lean_object* v_val_1166_; lean_object* v___x_1167_; 
lean_inc_ref(v_one_x3f_1165_);
lean_dec_ref(v_ring_1164_);
lean_dec(v___f_1163_);
lean_dec(v_toBind_1162_);
lean_dec_ref(v_inst_1161_);
v_val_1166_ = lean_ctor_get(v_one_x3f_1165_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v_one_x3f_1165_, 1);
v___x_1167_ = lean_apply_2(v_toPure_1160_, lean_box(0), v_val_1166_);
return v___x_1167_;
}
else
{
lean_object* v_type_1168_; lean_object* v_u_1169_; lean_object* v_semiringInst_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v_toPure_1160_);
v_type_1168_ = lean_ctor_get(v_ring_1164_, 1);
lean_inc_ref(v_type_1168_);
v_u_1169_ = lean_ctor_get(v_ring_1164_, 2);
lean_inc(v_u_1169_);
v_semiringInst_1170_ = lean_ctor_get(v_ring_1164_, 4);
lean_inc_ref(v_semiringInst_1170_);
lean_dec_ref(v_ring_1164_);
v___x_1171_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_1161_, v_u_1169_, v_type_1168_, v_semiringInst_1170_);
v___x_1172_ = lean_apply_4(v_toBind_1162_, lean_box(0), lean_box(0), v___x_1171_, v___f_1163_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_){
_start:
{
lean_object* v_toApplicative_1177_; lean_object* v_toBind_1178_; lean_object* v_getRing_1179_; lean_object* v_modifyRing_1180_; lean_object* v_toPure_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; 
v_toApplicative_1177_ = lean_ctor_get(v_inst_1173_, 0);
lean_inc_ref(v_toApplicative_1177_);
v_toBind_1178_ = lean_ctor_get(v_inst_1173_, 1);
lean_inc_n(v_toBind_1178_, 3);
lean_dec_ref(v_inst_1173_);
v_getRing_1179_ = lean_ctor_get(v_inst_1175_, 0);
lean_inc(v_getRing_1179_);
v_modifyRing_1180_ = lean_ctor_get(v_inst_1175_, 1);
lean_inc(v_modifyRing_1180_);
lean_dec_ref(v_inst_1175_);
v_toPure_1181_ = lean_ctor_get(v_toApplicative_1177_, 1);
lean_inc_n(v_toPure_1181_, 2);
lean_dec_ref(v_toApplicative_1177_);
v___f_1182_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1182_, 0, v_toPure_1181_);
lean_closure_set(v___f_1182_, 1, v_inst_1176_);
lean_closure_set(v___f_1182_, 2, v_toBind_1178_);
lean_closure_set(v___f_1182_, 3, v_modifyRing_1180_);
v___f_1183_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1183_, 0, v_toPure_1181_);
lean_closure_set(v___f_1183_, 1, v_inst_1174_);
lean_closure_set(v___f_1183_, 2, v_toBind_1178_);
lean_closure_set(v___f_1183_, 3, v___f_1182_);
v___x_1184_ = lean_apply_4(v_toBind_1178_, lean_box(0), lean_box(0), v_getRing_1179_, v___f_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object* v_m_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(v_inst_1186_, v_inst_1187_, v_inst_1188_, v_inst_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0(lean_object* v_invFn_1191_, lean_object* v_s_1192_){
_start:
{
lean_object* v_toRing_1193_; lean_object* v_semiringId_x3f_1194_; lean_object* v_commSemiringInst_1195_; lean_object* v_commRingInst_1196_; lean_object* v_noZeroDivInst_x3f_1197_; lean_object* v_fieldInst_x3f_1198_; lean_object* v_powIdentityInst_x3f_1199_; lean_object* v_denoteEntries_1200_; lean_object* v_nextId_1201_; lean_object* v_steps_1202_; lean_object* v_queue_1203_; lean_object* v_basis_1204_; lean_object* v_diseqs_1205_; uint8_t v_recheck_1206_; lean_object* v_invSet_1207_; lean_object* v_powIdentityVarCount_1208_; lean_object* v_numEq0_x3f_1209_; uint8_t v_numEq0Updated_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
v_toRing_1193_ = lean_ctor_get(v_s_1192_, 0);
v_semiringId_x3f_1194_ = lean_ctor_get(v_s_1192_, 2);
v_commSemiringInst_1195_ = lean_ctor_get(v_s_1192_, 3);
v_commRingInst_1196_ = lean_ctor_get(v_s_1192_, 4);
v_noZeroDivInst_x3f_1197_ = lean_ctor_get(v_s_1192_, 5);
v_fieldInst_x3f_1198_ = lean_ctor_get(v_s_1192_, 6);
v_powIdentityInst_x3f_1199_ = lean_ctor_get(v_s_1192_, 7);
v_denoteEntries_1200_ = lean_ctor_get(v_s_1192_, 8);
v_nextId_1201_ = lean_ctor_get(v_s_1192_, 9);
v_steps_1202_ = lean_ctor_get(v_s_1192_, 10);
v_queue_1203_ = lean_ctor_get(v_s_1192_, 11);
v_basis_1204_ = lean_ctor_get(v_s_1192_, 12);
v_diseqs_1205_ = lean_ctor_get(v_s_1192_, 13);
v_recheck_1206_ = lean_ctor_get_uint8(v_s_1192_, sizeof(void*)*17);
v_invSet_1207_ = lean_ctor_get(v_s_1192_, 14);
v_powIdentityVarCount_1208_ = lean_ctor_get(v_s_1192_, 15);
v_numEq0_x3f_1209_ = lean_ctor_get(v_s_1192_, 16);
v_numEq0Updated_1210_ = lean_ctor_get_uint8(v_s_1192_, sizeof(void*)*17 + 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_s_1192_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_s_1192_, 1);
lean_dec(v_unused_1219_);
v___x_1212_ = v_s_1192_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_numEq0_x3f_1209_);
lean_inc(v_powIdentityVarCount_1208_);
lean_inc(v_invSet_1207_);
lean_inc(v_diseqs_1205_);
lean_inc(v_basis_1204_);
lean_inc(v_queue_1203_);
lean_inc(v_steps_1202_);
lean_inc(v_nextId_1201_);
lean_inc(v_denoteEntries_1200_);
lean_inc(v_powIdentityInst_x3f_1199_);
lean_inc(v_fieldInst_x3f_1198_);
lean_inc(v_noZeroDivInst_x3f_1197_);
lean_inc(v_commRingInst_1196_);
lean_inc(v_commSemiringInst_1195_);
lean_inc(v_semiringId_x3f_1194_);
lean_inc(v_toRing_1193_);
lean_dec(v_s_1192_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_invFn_1191_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_toRing_1193_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_semiringId_x3f_1194_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_commSemiringInst_1195_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_commRingInst_1196_);
lean_ctor_set(v_reuseFailAlloc_1217_, 5, v_noZeroDivInst_x3f_1197_);
lean_ctor_set(v_reuseFailAlloc_1217_, 6, v_fieldInst_x3f_1198_);
lean_ctor_set(v_reuseFailAlloc_1217_, 7, v_powIdentityInst_x3f_1199_);
lean_ctor_set(v_reuseFailAlloc_1217_, 8, v_denoteEntries_1200_);
lean_ctor_set(v_reuseFailAlloc_1217_, 9, v_nextId_1201_);
lean_ctor_set(v_reuseFailAlloc_1217_, 10, v_steps_1202_);
lean_ctor_set(v_reuseFailAlloc_1217_, 11, v_queue_1203_);
lean_ctor_set(v_reuseFailAlloc_1217_, 12, v_basis_1204_);
lean_ctor_set(v_reuseFailAlloc_1217_, 13, v_diseqs_1205_);
lean_ctor_set(v_reuseFailAlloc_1217_, 14, v_invSet_1207_);
lean_ctor_set(v_reuseFailAlloc_1217_, 15, v_powIdentityVarCount_1208_);
lean_ctor_set(v_reuseFailAlloc_1217_, 16, v_numEq0_x3f_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*17, v_recheck_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*17 + 1, v_numEq0Updated_1210_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1(lean_object* v_toPure_1220_, lean_object* v_invFn_1221_, lean_object* v_____r_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_apply_2(v_toPure_1220_, lean_box(0), v_invFn_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2(lean_object* v_toPure_1224_, lean_object* v_modifyCommRing_1225_, lean_object* v_toBind_1226_, lean_object* v_invFn_1227_){
_start:
{
lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_inc_ref(v_invFn_1227_);
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1228_, 0, v_invFn_1227_);
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1229_, 0, v_toPure_1224_);
lean_closure_set(v___f_1229_, 1, v_invFn_1227_);
v___x_1230_ = lean_apply_1(v_modifyCommRing_1225_, v___f_1228_);
v___x_1231_ = lean_apply_4(v_toBind_1226_, lean_box(0), lean_box(0), v___x_1230_, v___f_1229_);
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7));
v___x_1248_ = l_Lean_stringToMessageData(v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3(lean_object* v_toPure_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_toBind_1254_, lean_object* v___f_1255_, lean_object* v_ring_1256_){
_start:
{
lean_object* v_fieldInst_x3f_1257_; 
v_fieldInst_x3f_1257_ = lean_ctor_get(v_ring_1256_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1257_) == 1)
{
lean_object* v_invFn_x3f_1258_; 
lean_inc_ref(v_fieldInst_x3f_1257_);
v_invFn_x3f_1258_ = lean_ctor_get(v_ring_1256_, 1);
if (lean_obj_tag(v_invFn_x3f_1258_) == 1)
{
lean_object* v_val_1259_; lean_object* v___x_1260_; 
lean_inc_ref(v_invFn_x3f_1258_);
lean_dec_ref_known(v_fieldInst_x3f_1257_, 1);
lean_dec_ref(v_ring_1256_);
lean_dec(v___f_1255_);
lean_dec(v_toBind_1254_);
lean_dec_ref(v_inst_1253_);
lean_dec_ref(v_inst_1252_);
lean_dec_ref(v_inst_1251_);
lean_dec(v_inst_1250_);
v_val_1259_ = lean_ctor_get(v_invFn_x3f_1258_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v_invFn_x3f_1258_, 1);
v___x_1260_ = lean_apply_2(v_toPure_1249_, lean_box(0), v_val_1259_);
return v___x_1260_;
}
else
{
lean_object* v_toRing_1261_; lean_object* v_val_1262_; lean_object* v_type_1263_; lean_object* v_u_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_expectedInst_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec(v_toPure_1249_);
v_toRing_1261_ = lean_ctor_get(v_ring_1256_, 0);
lean_inc_ref(v_toRing_1261_);
lean_dec_ref(v_ring_1256_);
v_val_1262_ = lean_ctor_get(v_fieldInst_x3f_1257_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v_fieldInst_x3f_1257_, 1);
v_type_1263_ = lean_ctor_get(v_toRing_1261_, 1);
lean_inc_ref_n(v_type_1263_, 2);
v_u_1264_ = lean_ctor_get(v_toRing_1261_, 2);
lean_inc_n(v_u_1264_, 2);
lean_dec_ref(v_toRing_1261_);
v___x_1265_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2));
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_u_1264_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_mkConst(v___x_1265_, v___x_1267_);
v_expectedInst_1269_ = l_Lean_mkAppB(v___x_1268_, v_type_1263_, v_val_1262_);
v___x_1270_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4));
v___x_1271_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6));
v___x_1272_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(v_inst_1250_, v_inst_1251_, v_inst_1252_, v_inst_1253_, v_type_1263_, v_u_1264_, v___x_1270_, v___x_1271_, v_expectedInst_1269_);
v___x_1273_ = lean_apply_4(v_toBind_1254_, lean_box(0), lean_box(0), v___x_1272_, v___f_1255_);
return v___x_1273_;
}
}
else
{
lean_object* v_toRing_1274_; lean_object* v_type_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec(v___f_1255_);
lean_dec(v_toBind_1254_);
lean_dec_ref(v_inst_1253_);
lean_dec(v_inst_1250_);
lean_dec(v_toPure_1249_);
v_toRing_1274_ = lean_ctor_get(v_ring_1256_, 0);
lean_inc_ref(v_toRing_1274_);
lean_dec_ref(v_ring_1256_);
v_type_1275_ = lean_ctor_get(v_toRing_1274_, 1);
lean_inc_ref(v_type_1275_);
lean_dec_ref(v_toRing_1274_);
v___x_1276_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8);
v___x_1277_ = l_Lean_indentExpr(v_type_1275_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_throwError___redArg(v_inst_1252_, v_inst_1251_, v___x_1278_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_){
_start:
{
lean_object* v_toApplicative_1285_; lean_object* v_toBind_1286_; lean_object* v_getCommRing_1287_; lean_object* v_modifyCommRing_1288_; lean_object* v_toPure_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; 
v_toApplicative_1285_ = lean_ctor_get(v_inst_1282_, 0);
v_toBind_1286_ = lean_ctor_get(v_inst_1282_, 1);
lean_inc_n(v_toBind_1286_, 3);
v_getCommRing_1287_ = lean_ctor_get(v_inst_1284_, 0);
lean_inc(v_getCommRing_1287_);
v_modifyCommRing_1288_ = lean_ctor_get(v_inst_1284_, 1);
lean_inc(v_modifyCommRing_1288_);
lean_dec_ref(v_inst_1284_);
v_toPure_1289_ = lean_ctor_get(v_toApplicative_1285_, 1);
lean_inc_n(v_toPure_1289_, 2);
v___f_1290_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1290_, 0, v_toPure_1289_);
lean_closure_set(v___f_1290_, 1, v_modifyCommRing_1288_);
lean_closure_set(v___f_1290_, 2, v_toBind_1286_);
v___f_1291_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1291_, 0, v_toPure_1289_);
lean_closure_set(v___f_1291_, 1, v_inst_1280_);
lean_closure_set(v___f_1291_, 2, v_inst_1281_);
lean_closure_set(v___f_1291_, 3, v_inst_1282_);
lean_closure_set(v___f_1291_, 4, v_inst_1283_);
lean_closure_set(v___f_1291_, 5, v_toBind_1286_);
lean_closure_set(v___f_1291_, 6, v___f_1290_);
v___x_1292_ = lean_apply_4(v_toBind_1286_, lean_box(0), lean_box(0), v_getCommRing_1287_, v___f_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn(lean_object* v_m_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(v_inst_1294_, v_inst_1295_, v_inst_1296_, v_inst_1297_, v_inst_1298_);
return v___x_1299_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
