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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "error while initializing `grind ring` operators:\ninstance for `"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "\nis not definitionally equal to the expected one "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "\nwhen only reducible definitions and instances are reduced"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7;
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2;
extern lean_object* l_Lean_Nat_mkType;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
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
lean_object* l_Lean_Meta_Grind_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`grind` internal error, type is not a field"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__0_value;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__1;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_9 = l_Lean_Meta_isDefEqI(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_9);
x_13 = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1;
x_14 = l_Lean_MessageData_ofName(x_1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_indentExpr(x_2);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_3);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(x_25, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_9, 0, x_27);
return x_9;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1;
x_31 = l_Lean_MessageData_ofName(x_1);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_indentExpr(x_2);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_indentExpr(x_3);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(x_42, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
return x_9;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_9, 0);
lean_inc(x_47);
lean_dec(x_9);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_mkConst(x_2, x_3);
x_9 = l_Lean_mkAppB(x_8, x_4, x_5);
x_10 = lean_apply_1(x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_8);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_5);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_10);
lean_inc_ref(x_5);
lean_inc_ref(x_12);
lean_inc_ref(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_9);
lean_closure_set(x_13, 5, x_1);
lean_closure_set(x_13, 6, x_10);
x_14 = l_Lean_mkConst(x_7, x_12);
x_15 = l_Lean_Expr_app___override(x_14, x_5);
x_16 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___redArg(x_3, x_2, x_4, x_15);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_mkConst(x_2, x_3);
lean_inc_ref_n(x_4, 2);
x_9 = l_Lean_mkApp4(x_8, x_4, x_4, x_4, x_5);
x_10 = lean_apply_1(x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_8);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_5);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_box(0);
lean_inc(x_6);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_10);
lean_inc_ref(x_5);
lean_inc_ref(x_14);
lean_inc_ref(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_9);
lean_closure_set(x_15, 5, x_1);
lean_closure_set(x_15, 6, x_10);
x_16 = l_Lean_mkConst(x_7, x_14);
lean_inc_ref_n(x_5, 2);
x_17 = l_Lean_mkApp3(x_16, x_5, x_5, x_5);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___redArg(x_3, x_2, x_4, x_17);
x_19 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_18, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_mkConst(x_2, x_3);
lean_inc_ref(x_4);
x_10 = l_Lean_mkApp4(x_9, x_4, x_5, x_4, x_6);
x_11 = lean_apply_1(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4));
x_12 = l_Lean_mkConst(x_11, x_1);
lean_inc_ref(x_2);
x_13 = l_Lean_mkAppB(x_12, x_2, x_3);
x_14 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5));
x_15 = l_Lean_Name_mkStr2(x_4, x_14);
lean_inc_ref(x_10);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(x_16, 0, x_5);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_6);
lean_closure_set(x_16, 3, x_2);
lean_closure_set(x_16, 4, x_7);
lean_closure_set(x_16, 5, x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_10);
lean_closure_set(x_17, 2, x_13);
x_18 = lean_apply_2(x_8, lean_box(0), x_17);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_18, x_16);
return x_19;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0));
x_10 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1));
x_11 = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2;
x_12 = lean_box(0);
lean_inc(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
lean_inc_ref(x_13);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
lean_inc_ref(x_15);
x_16 = l_Lean_mkConst(x_10, x_15);
x_17 = l_Lean_Nat_mkType;
lean_inc(x_8);
lean_inc_ref(x_4);
lean_inc_ref(x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_6);
lean_closure_set(x_18, 2, x_7);
lean_closure_set(x_18, 3, x_9);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_15);
lean_closure_set(x_18, 6, x_17);
lean_closure_set(x_18, 7, x_1);
lean_closure_set(x_18, 8, x_8);
lean_inc_ref(x_6);
x_19 = l_Lean_mkApp3(x_16, x_6, x_17, x_6);
x_20 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___redArg(x_3, x_2, x_4, x_19);
x_21 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Name_mkStr2(x_1, x_2);
x_8 = l_Lean_mkConst(x_7, x_3);
x_9 = l_Lean_mkAppB(x_8, x_4, x_6);
x_10 = lean_apply_1(x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_1, lean_box(0), x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_10 = lean_apply_2(x_1, lean_box(0), x_2);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec_ref(x_9);
lean_inc(x_3);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_5);
x_14 = l_Lean_Name_mkStr2(x_6, x_7);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_2);
x_16 = lean_apply_2(x_8, lean_box(0), x_15);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec_ref(x_7);
x_13 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0));
x_14 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1));
x_15 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_4);
lean_inc_ref(x_3);
x_16 = l_Lean_mkConst(x_14, x_3);
lean_inc_ref(x_5);
x_17 = l_Lean_mkAppB(x_16, x_5, x_6);
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2));
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_5);
lean_closure_set(x_19, 4, x_10);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3));
x_22 = l_Lean_mkConst(x_21, x_3);
x_23 = l_Lean_Expr_app___override(x_22, x_5);
x_24 = lean_apply_1(x_11, x_23);
lean_inc_ref(x_20);
lean_inc(x_8);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(x_25, 0, x_12);
lean_closure_set(x_25, 1, x_17);
lean_closure_set(x_25, 2, x_8);
lean_closure_set(x_25, 3, x_20);
lean_closure_set(x_25, 4, x_20);
lean_closure_set(x_25, 5, x_18);
lean_closure_set(x_25, 6, x_13);
lean_closure_set(x_25, 7, x_1);
x_26 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_dec_ref(x_7);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0));
x_31 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1));
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
lean_inc_ref(x_33);
x_34 = l_Lean_mkConst(x_31, x_33);
lean_inc_ref(x_5);
x_35 = l_Lean_mkAppB(x_34, x_5, x_6);
x_36 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2));
lean_inc_ref(x_5);
lean_inc_ref(x_33);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_30);
lean_closure_set(x_37, 2, x_33);
lean_closure_set(x_37, 3, x_5);
lean_closure_set(x_37, 4, x_27);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3));
x_40 = l_Lean_mkConst(x_39, x_33);
x_41 = l_Lean_Expr_app___override(x_40, x_5);
x_42 = lean_apply_1(x_28, x_41);
lean_inc_ref(x_38);
lean_inc(x_8);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(x_43, 0, x_29);
lean_closure_set(x_43, 1, x_35);
lean_closure_set(x_43, 2, x_8);
lean_closure_set(x_43, 3, x_38);
lean_closure_set(x_43, 4, x_38);
lean_closure_set(x_43, 5, x_36);
lean_closure_set(x_43, 6, x_30);
lean_closure_set(x_43, 7, x_1);
x_44 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_42, x_43);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 6);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 6, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 7);
x_13 = lean_ctor_get(x_2, 8);
x_14 = lean_ctor_get(x_2, 9);
x_15 = lean_ctor_get(x_2, 10);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get(x_2, 13);
x_19 = lean_ctor_get(x_2, 14);
x_20 = lean_ctor_get(x_2, 15);
x_21 = lean_ctor_get(x_2, 16);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_22);
lean_ctor_set(x_23, 7, x_12);
lean_ctor_set(x_23, 8, x_13);
lean_ctor_set(x_23, 9, x_14);
lean_ctor_set(x_23, 10, x_15);
lean_ctor_set(x_23, 11, x_16);
lean_ctor_set(x_23, 12, x_17);
lean_ctor_set(x_23, 13, x_18);
lean_ctor_set(x_23, 14, x_19);
lean_ctor_set(x_23, 15, x_20);
lean_ctor_set(x_23, 16, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1));
x_12 = lean_box(0);
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
lean_inc_ref(x_13);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3));
x_16 = l_Lean_mkConst(x_15, x_13);
lean_inc_ref(x_2);
x_17 = l_Lean_mkAppB(x_16, x_2, x_3);
lean_inc_ref(x_2);
x_18 = l_Lean_mkAppB(x_14, x_2, x_17);
x_19 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5));
x_20 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7));
x_21 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(x_4, x_5, x_6, x_7, x_2, x_1, x_19, x_20, x_18);
x_22 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_9);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 6);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_14);
lean_dec_ref(x_8);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3), 10, 9);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
lean_closure_set(x_15, 6, x_5);
lean_closure_set(x_15, 7, x_6);
lean_closure_set(x_15, 8, x_7);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_1, lean_box(0), x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_7);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__4), 8, 7);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 8);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 8, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 9);
x_15 = lean_ctor_get(x_2, 10);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get(x_2, 13);
x_19 = lean_ctor_get(x_2, 14);
x_20 = lean_ctor_get(x_2, 15);
x_21 = lean_ctor_get(x_2, 16);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_12);
lean_ctor_set(x_23, 7, x_13);
lean_ctor_set(x_23, 8, x_22);
lean_ctor_set(x_23, 9, x_14);
lean_ctor_set(x_23, 10, x_15);
lean_ctor_set(x_23, 11, x_16);
lean_ctor_set(x_23, 12, x_17);
lean_ctor_set(x_23, 13, x_18);
lean_ctor_set(x_23, 14, x_19);
lean_ctor_set(x_23, 15, x_20);
lean_ctor_set(x_23, 16, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1));
x_12 = lean_box(0);
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
lean_inc_ref(x_13);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4));
x_16 = l_Lean_mkConst(x_15, x_13);
lean_inc_ref(x_2);
x_17 = l_Lean_mkAppB(x_16, x_2, x_3);
lean_inc_ref(x_2);
x_18 = l_Lean_mkAppB(x_14, x_2, x_17);
x_19 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6));
x_20 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8));
x_21 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(x_4, x_5, x_6, x_7, x_2, x_1, x_19, x_20, x_18);
x_22 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_9);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_14);
lean_dec_ref(x_8);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3), 10, 9);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
lean_closure_set(x_15, 6, x_5);
lean_closure_set(x_15, 7, x_6);
lean_closure_set(x_15, 8, x_7);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_1, lean_box(0), x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_7);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__4), 8, 7);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 7);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 7, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 8);
x_14 = lean_ctor_get(x_2, 9);
x_15 = lean_ctor_get(x_2, 10);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get(x_2, 13);
x_19 = lean_ctor_get(x_2, 14);
x_20 = lean_ctor_get(x_2, 15);
x_21 = lean_ctor_get(x_2, 16);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_12);
lean_ctor_set(x_23, 7, x_22);
lean_ctor_set(x_23, 8, x_13);
lean_ctor_set(x_23, 9, x_14);
lean_ctor_set(x_23, 10, x_15);
lean_ctor_set(x_23, 11, x_16);
lean_ctor_set(x_23, 12, x_17);
lean_ctor_set(x_23, 13, x_18);
lean_ctor_set(x_23, 14, x_19);
lean_ctor_set(x_23, 15, x_20);
lean_ctor_set(x_23, 16, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1));
x_12 = lean_box(0);
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
lean_inc_ref(x_13);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3));
x_16 = l_Lean_mkConst(x_15, x_13);
lean_inc_ref(x_2);
x_17 = l_Lean_mkAppB(x_16, x_2, x_3);
lean_inc_ref(x_2);
x_18 = l_Lean_mkAppB(x_14, x_2, x_17);
x_19 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5));
x_20 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7));
x_21 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(x_4, x_5, x_6, x_7, x_2, x_1, x_19, x_20, x_18);
x_22 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_9);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 7);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_14);
lean_dec_ref(x_8);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3), 10, 9);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
lean_closure_set(x_15, 6, x_5);
lean_closure_set(x_15, 7, x_6);
lean_closure_set(x_15, 8, x_7);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_1, lean_box(0), x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_7);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__4), 8, 7);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 9);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 9, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 10);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get(x_2, 13);
x_19 = lean_ctor_get(x_2, 14);
x_20 = lean_ctor_get(x_2, 15);
x_21 = lean_ctor_get(x_2, 16);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_12);
lean_ctor_set(x_23, 7, x_13);
lean_ctor_set(x_23, 8, x_14);
lean_ctor_set(x_23, 9, x_22);
lean_ctor_set(x_23, 10, x_15);
lean_ctor_set(x_23, 11, x_16);
lean_ctor_set(x_23, 12, x_17);
lean_ctor_set(x_23, 13, x_18);
lean_ctor_set(x_23, 14, x_19);
lean_ctor_set(x_23, 15, x_20);
lean_ctor_set(x_23, 16, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1));
x_12 = lean_box(0);
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_mkConst(x_11, x_13);
lean_inc_ref(x_2);
x_15 = l_Lean_mkAppB(x_14, x_2, x_3);
x_16 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3));
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5));
x_18 = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(x_4, x_5, x_6, x_7, x_2, x_1, x_16, x_17, x_15);
x_19 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_18, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 9);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_14);
lean_dec_ref(x_8);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3), 10, 9);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
lean_closure_set(x_15, 6, x_5);
lean_closure_set(x_15, 7, x_6);
lean_closure_set(x_15, 8, x_7);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_1, lean_box(0), x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_7);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__4), 8, 7);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 10);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 10, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get(x_2, 13);
x_19 = lean_ctor_get(x_2, 14);
x_20 = lean_ctor_get(x_2, 15);
x_21 = lean_ctor_get(x_2, 16);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_12);
lean_ctor_set(x_23, 7, x_13);
lean_ctor_set(x_23, 8, x_14);
lean_ctor_set(x_23, 9, x_15);
lean_ctor_set(x_23, 10, x_22);
lean_ctor_set(x_23, 11, x_16);
lean_ctor_set(x_23, 12, x_17);
lean_ctor_set(x_23, 13, x_18);
lean_ctor_set(x_23, 14, x_19);
lean_ctor_set(x_23, 15, x_20);
lean_ctor_set(x_23, 16, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 10);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_14);
lean_dec_ref(x_8);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3), 10, 9);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_12);
lean_closure_set(x_15, 6, x_14);
lean_closure_set(x_15, 7, x_6);
lean_closure_set(x_15, 8, x_7);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_1, lean_box(0), x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_7);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__4), 8, 7);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 11);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 11, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get(x_2, 13);
x_19 = lean_ctor_get(x_2, 14);
x_20 = lean_ctor_get(x_2, 15);
x_21 = lean_ctor_get(x_2, 16);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_12);
lean_ctor_set(x_23, 7, x_13);
lean_ctor_set(x_23, 8, x_14);
lean_ctor_set(x_23, 9, x_15);
lean_ctor_set(x_23, 10, x_16);
lean_ctor_set(x_23, 11, x_22);
lean_ctor_set(x_23, 12, x_17);
lean_ctor_set(x_23, 13, x_18);
lean_ctor_set(x_23, 14, x_19);
lean_ctor_set(x_23, 15, x_20);
lean_ctor_set(x_23, 16, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Name_mkStr2(x_1, x_2);
x_10 = l_Lean_mkConst(x_9, x_3);
x_11 = l_Lean_mkAppB(x_10, x_4, x_8);
x_12 = lean_apply_1(x_5, x_11);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_2);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
lean_inc(x_3);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_5);
x_12 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2));
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed), 8, 3);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_2);
x_14 = lean_apply_2(x_6, lean_box(0), x_13);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0));
x_14 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1));
x_15 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_2);
lean_inc_ref(x_1);
x_16 = l_Lean_mkConst(x_14, x_1);
lean_inc_ref(x_3);
x_17 = l_Lean_mkAppB(x_16, x_3, x_4);
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2));
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_11);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_6);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc_ref(x_20);
lean_inc(x_5);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(x_21, 0, x_7);
lean_closure_set(x_21, 1, x_17);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_20);
lean_closure_set(x_21, 5, x_8);
x_22 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3));
x_23 = l_Lean_mkConst(x_22, x_1);
x_24 = l_Lean_Expr_app___override(x_23, x_3);
x_25 = lean_apply_1(x_12, x_24);
x_26 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_25, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0));
x_30 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1));
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
lean_inc_ref(x_32);
x_33 = l_Lean_mkConst(x_30, x_32);
lean_inc_ref(x_3);
x_34 = l_Lean_mkAppB(x_33, x_3, x_4);
x_35 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2));
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc_ref(x_32);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_29);
lean_closure_set(x_36, 2, x_32);
lean_closure_set(x_36, 3, x_3);
lean_closure_set(x_36, 4, x_27);
lean_closure_set(x_36, 5, x_5);
lean_closure_set(x_36, 6, x_6);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(x_37, 0, x_36);
lean_inc_ref(x_37);
lean_inc(x_5);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(x_38, 0, x_7);
lean_closure_set(x_38, 1, x_34);
lean_closure_set(x_38, 2, x_5);
lean_closure_set(x_38, 3, x_37);
lean_closure_set(x_38, 4, x_37);
lean_closure_set(x_38, 5, x_8);
x_39 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3));
x_40 = l_Lean_mkConst(x_39, x_32);
x_41 = l_Lean_Expr_app___override(x_40, x_3);
x_42 = lean_apply_1(x_28, x_41);
x_43 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_42, x_38);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 11);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_6);
lean_inc(x_1);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4), 9, 8);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_1);
lean_closure_set(x_13, 7, x_5);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_1, lean_box(0), x_14);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
lean_inc(x_6);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_6);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__5), 6, 5);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_10);
lean_closure_set(x_11, 4, x_1);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 12);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 12, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 13);
x_19 = lean_ctor_get(x_2, 14);
x_20 = lean_ctor_get(x_2, 15);
x_21 = lean_ctor_get(x_2, 16);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_12);
lean_ctor_set(x_23, 7, x_13);
lean_ctor_set(x_23, 8, x_14);
lean_ctor_set(x_23, 9, x_15);
lean_ctor_set(x_23, 10, x_16);
lean_ctor_set(x_23, 11, x_17);
lean_ctor_set(x_23, 12, x_22);
lean_ctor_set(x_23, 13, x_18);
lean_ctor_set(x_23, 14, x_19);
lean_ctor_set(x_23, 15, x_20);
lean_ctor_set(x_23, 16, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 12);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_13);
lean_dec_ref(x_7);
lean_inc(x_5);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3), 9, 8);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_5);
lean_closure_set(x_14, 7, x_6);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_1, lean_box(0), x_15);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_6);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__4), 7, 6);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_6);
lean_closure_set(x_11, 5, x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_mkRawNatLit(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0;
x_9 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2));
x_10 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_2);
lean_inc_ref(x_1);
x_11 = l_Lean_mkConst(x_9, x_1);
lean_inc_ref(x_3);
x_12 = l_Lean_mkApp3(x_11, x_3, x_4, x_8);
x_13 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4));
x_14 = l_Lean_mkConst(x_13, x_1);
x_15 = l_Lean_mkApp3(x_14, x_3, x_8, x_12);
x_16 = lean_apply_1(x_6, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0;
x_19 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2));
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
lean_inc_ref(x_21);
x_22 = l_Lean_mkConst(x_19, x_21);
lean_inc_ref(x_3);
x_23 = l_Lean_mkApp3(x_22, x_3, x_4, x_18);
x_24 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4));
x_25 = l_Lean_mkConst(x_24, x_21);
x_26 = l_Lean_mkApp3(x_25, x_3, x_18, x_23);
x_27 = lean_apply_1(x_17, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 13);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 13, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get(x_2, 14);
x_20 = lean_ctor_get(x_2, 15);
x_21 = lean_ctor_get(x_2, 16);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_12);
lean_ctor_set(x_23, 7, x_13);
lean_ctor_set(x_23, 8, x_14);
lean_ctor_set(x_23, 9, x_15);
lean_ctor_set(x_23, 10, x_16);
lean_ctor_set(x_23, 11, x_17);
lean_ctor_set(x_23, 12, x_18);
lean_ctor_set(x_23, 13, x_22);
lean_ctor_set(x_23, 14, x_19);
lean_ctor_set(x_23, 15, x_20);
lean_ctor_set(x_23, 16, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_internalize___boxed), 14, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_5);
lean_inc_ref(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_1(x_4, x_6);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(x_1, x_2, x_3, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 13);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_11);
lean_dec_ref(x_5);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4), 7, 6);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_3);
lean_closure_set(x_12, 5, x_4);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_1, lean_box(0), x_13);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
lean_inc(x_6);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3), 5, 4);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_6);
lean_closure_set(x_10, 3, x_8);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__5), 5, 4);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_ctor_get(x_2, 6);
x_12 = lean_ctor_get(x_2, 7);
x_13 = lean_ctor_get(x_2, 8);
x_14 = lean_ctor_get(x_2, 9);
x_15 = lean_ctor_get(x_2, 10);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_19 = lean_ctor_get(x_2, 13);
x_20 = lean_ctor_get(x_2, 14);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_8);
lean_ctor_set(x_23, 4, x_9);
lean_ctor_set(x_23, 5, x_10);
lean_ctor_set(x_23, 6, x_11);
lean_ctor_set(x_23, 7, x_12);
lean_ctor_set(x_23, 8, x_13);
lean_ctor_set(x_23, 9, x_14);
lean_ctor_set(x_23, 10, x_15);
lean_ctor_set(x_23, 11, x_16);
lean_ctor_set(x_23, 12, x_17);
lean_ctor_set(x_23, 13, x_19);
lean_ctor_set(x_23, 14, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*15, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*15 + 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2));
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_mkConst(x_12, x_14);
lean_inc_ref(x_10);
x_16 = l_Lean_mkAppB(x_15, x_10, x_2);
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4));
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6));
x_19 = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(x_3, x_4, x_5, x_6, x_10, x_11, x_17, x_18, x_16);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_8);
return x_20;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 6);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 1);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec_ref(x_9);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3), 9, 8);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_5);
lean_closure_set(x_15, 6, x_6);
lean_closure_set(x_15, 7, x_7);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_1, lean_box(0), x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_8);
x_20 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__1;
x_22 = l_Lean_indentExpr(x_20);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___redArg(x_4, x_3, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_7);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4), 8, 7);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
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
l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3 = _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3);
l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5 = _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5);
l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7 = _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7);
l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2 = _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__4___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
