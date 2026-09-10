// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Functions
// Imports: public import Lean.Meta.Sym.Arith.MonadRing public import Lean.Meta.Sym.Arith.MonadSemiring
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "error while initializing arithmetic operators:\ninstance for `"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "\nis not definitionally equal to the expected one "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "\nwhen only reducible definitions and instances are reduced"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 4, 252, 84, 28, 16, 24, 6)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 152, 64, 108, 234, 163, 46, 107)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "internal error: type is not a field"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0));
v___x_50_ = l_Lean_stringToMessageData(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2));
v___x_53_ = l_Lean_stringToMessageData(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4));
v___x_56_ = l_Lean_stringToMessageData(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6));
v___x_59_ = l_Lean_stringToMessageData(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object* v_declName_60_, lean_object* v_inst_61_, lean_object* v_inst_x27_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___y_69_; lean_object* v___x_102_; uint8_t v_transparency_103_; uint8_t v___x_104_; uint8_t v___x_105_; 
v___x_102_ = l_Lean_Meta_Context_config(v_a_63_);
v_transparency_103_ = lean_ctor_get_uint8(v___x_102_, 9);
lean_dec_ref(v___x_102_);
v___x_104_ = 3;
v___x_105_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v_keyedConfig_106_; uint8_t v_trackZetaDelta_107_; lean_object* v_zetaDeltaSet_108_; lean_object* v_lctx_109_; lean_object* v_localInstances_110_; lean_object* v_defEqCtx_x3f_111_; lean_object* v_synthPendingDepth_112_; lean_object* v_customCanUnfoldPredicate_x3f_113_; uint8_t v_univApprox_114_; uint8_t v_inTypeClassResolution_115_; uint8_t v_cacheInferType_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_keyedConfig_106_ = lean_ctor_get(v_a_63_, 0);
v_trackZetaDelta_107_ = lean_ctor_get_uint8(v_a_63_, sizeof(void*)*7);
v_zetaDeltaSet_108_ = lean_ctor_get(v_a_63_, 1);
v_lctx_109_ = lean_ctor_get(v_a_63_, 2);
v_localInstances_110_ = lean_ctor_get(v_a_63_, 3);
v_defEqCtx_x3f_111_ = lean_ctor_get(v_a_63_, 4);
v_synthPendingDepth_112_ = lean_ctor_get(v_a_63_, 5);
v_customCanUnfoldPredicate_x3f_113_ = lean_ctor_get(v_a_63_, 6);
v_univApprox_114_ = lean_ctor_get_uint8(v_a_63_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_115_ = lean_ctor_get_uint8(v_a_63_, sizeof(void*)*7 + 2);
v_cacheInferType_116_ = lean_ctor_get_uint8(v_a_63_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_106_);
v___x_117_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_104_, v_keyedConfig_106_);
lean_inc(v_customCanUnfoldPredicate_x3f_113_);
lean_inc(v_synthPendingDepth_112_);
lean_inc(v_defEqCtx_x3f_111_);
lean_inc_ref(v_localInstances_110_);
lean_inc_ref(v_lctx_109_);
lean_inc(v_zetaDeltaSet_108_);
v___x_118_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_zetaDeltaSet_108_);
lean_ctor_set(v___x_118_, 2, v_lctx_109_);
lean_ctor_set(v___x_118_, 3, v_localInstances_110_);
lean_ctor_set(v___x_118_, 4, v_defEqCtx_x3f_111_);
lean_ctor_set(v___x_118_, 5, v_synthPendingDepth_112_);
lean_ctor_set(v___x_118_, 6, v_customCanUnfoldPredicate_x3f_113_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*7, v_trackZetaDelta_107_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*7 + 1, v_univApprox_114_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*7 + 2, v_inTypeClassResolution_115_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*7 + 3, v_cacheInferType_116_);
lean_inc_ref(v_inst_x27_62_);
lean_inc_ref(v_inst_61_);
v___x_119_ = l_Lean_Meta_isExprDefEq(v_inst_61_, v_inst_x27_62_, v___x_118_, v_a_64_, v_a_65_, v_a_66_);
lean_dec_ref_known(v___x_118_, 7);
v___y_69_ = v___x_119_;
goto v___jp_68_;
}
else
{
lean_object* v___x_120_; 
lean_inc_ref(v_inst_x27_62_);
lean_inc_ref(v_inst_61_);
v___x_120_ = l_Lean_Meta_isExprDefEq(v_inst_61_, v_inst_x27_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
v___y_69_ = v___x_120_;
goto v___jp_68_;
}
v___jp_68_:
{
if (lean_obj_tag(v___y_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_93_; 
v_a_70_ = lean_ctor_get(v___y_69_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___y_69_);
if (v_isSharedCheck_93_ == 0)
{
v___x_72_ = v___y_69_;
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___y_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
uint8_t v___x_74_; 
v___x_74_ = lean_unbox(v_a_70_);
lean_dec(v_a_70_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
lean_del_object(v___x_72_);
v___x_75_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1);
v___x_76_ = l_Lean_MessageData_ofName(v_declName_60_);
v___x_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3);
v___x_79_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = l_Lean_indentExpr(v_inst_61_);
v___x_81_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5);
v___x_83_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = l_Lean_indentExpr(v_inst_x27_62_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7);
v___x_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_87_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_91_; 
lean_dec_ref(v_inst_x27_62_);
lean_dec_ref(v_inst_61_);
lean_dec(v_declName_60_);
v___x_89_ = lean_box(0);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_89_);
v___x_91_ = v___x_72_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec_ref(v_inst_x27_62_);
lean_dec_ref(v_inst_61_);
lean_dec(v_declName_60_);
v_a_94_ = lean_ctor_get(v___y_69_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___y_69_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___y_69_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___y_69_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object* v_declName_121_, lean_object* v_inst_122_, lean_object* v_inst_x27_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_121_, v_inst_122_, v_inst_x27_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object* v_00_u03b1_130_, lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(lean_object* v_00_u03b1_138_, lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(v_00_u03b1_138_, v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object* v_inst_146_, lean_object* v_declName_147_, lean_object* v___x_148_, lean_object* v_type_149_, lean_object* v_inst_150_, lean_object* v_____r_151_){
_start:
{
lean_object* v_canonExpr_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_canonExpr_152_ = lean_ctor_get(v_inst_146_, 0);
lean_inc(v_canonExpr_152_);
lean_dec_ref(v_inst_146_);
v___x_153_ = l_Lean_mkConst(v_declName_147_, v___x_148_);
v___x_154_ = l_Lean_mkAppB(v___x_153_, v_type_149_, v_inst_150_);
v___x_155_ = lean_apply_1(v_canonExpr_152_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object* v_inst_156_, lean_object* v_declName_157_, lean_object* v___x_158_, lean_object* v_type_159_, lean_object* v_expectedInst_160_, lean_object* v_inst_161_, lean_object* v_toBind_162_, lean_object* v_inst_163_){
_start:
{
lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
lean_inc_ref(v_inst_163_);
lean_inc(v_declName_157_);
v___f_164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_164_, 0, v_inst_156_);
lean_closure_set(v___f_164_, 1, v_declName_157_);
lean_closure_set(v___f_164_, 2, v___x_158_);
lean_closure_set(v___f_164_, 3, v_type_159_);
lean_closure_set(v___f_164_, 4, v_inst_163_);
v___x_165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_165_, 0, v_declName_157_);
lean_closure_set(v___x_165_, 1, v_inst_163_);
lean_closure_set(v___x_165_, 2, v_expectedInst_160_);
v___x_166_ = lean_apply_2(v_inst_161_, lean_box(0), v___x_165_);
v___x_167_ = lean_apply_4(v_toBind_162_, lean_box(0), lean_box(0), v___x_166_, v___f_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_type_172_, lean_object* v_u_173_, lean_object* v_instDeclName_174_, lean_object* v_declName_175_, lean_object* v_expectedInst_176_){
_start:
{
lean_object* v_toBind_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_toBind_177_ = lean_ctor_get(v_inst_170_, 1);
lean_inc_n(v_toBind_177_, 2);
v___x_178_ = lean_box(0);
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v_u_173_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
lean_inc_ref(v_type_172_);
lean_inc_ref(v___x_179_);
lean_inc_ref(v_inst_171_);
v___f_180_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_180_, 0, v_inst_171_);
lean_closure_set(v___f_180_, 1, v_declName_175_);
lean_closure_set(v___f_180_, 2, v___x_179_);
lean_closure_set(v___f_180_, 3, v_type_172_);
lean_closure_set(v___f_180_, 4, v_expectedInst_176_);
lean_closure_set(v___f_180_, 5, v_inst_168_);
lean_closure_set(v___f_180_, 6, v_toBind_177_);
v___x_181_ = l_Lean_mkConst(v_instDeclName_174_, v___x_179_);
v___x_182_ = l_Lean_Expr_app___override(v___x_181_, v_type_172_);
v___x_183_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_170_, v_inst_169_, v_inst_171_, v___x_182_);
v___x_184_ = lean_apply_4(v_toBind_177_, lean_box(0), lean_box(0), v___x_183_, v___f_180_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object* v_m_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_type_190_, lean_object* v_u_191_, lean_object* v_instDeclName_192_, lean_object* v_declName_193_, lean_object* v_expectedInst_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_186_, v_inst_187_, v_inst_188_, v_inst_189_, v_type_190_, v_u_191_, v_instDeclName_192_, v_declName_193_, v_expectedInst_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_196_, lean_object* v_declName_197_, lean_object* v___x_198_, lean_object* v_type_199_, lean_object* v_inst_200_, lean_object* v_____r_201_){
_start:
{
lean_object* v_canonExpr_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_canonExpr_202_ = lean_ctor_get(v_inst_196_, 0);
lean_inc(v_canonExpr_202_);
lean_dec_ref(v_inst_196_);
v___x_203_ = l_Lean_mkConst(v_declName_197_, v___x_198_);
lean_inc_ref_n(v_type_199_, 2);
v___x_204_ = l_Lean_mkApp4(v___x_203_, v_type_199_, v_type_199_, v_type_199_, v_inst_200_);
v___x_205_ = lean_apply_1(v_canonExpr_202_, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_206_, lean_object* v_declName_207_, lean_object* v___x_208_, lean_object* v_type_209_, lean_object* v_expectedInst_210_, lean_object* v_inst_211_, lean_object* v_toBind_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
lean_inc_ref(v_inst_213_);
lean_inc(v_declName_207_);
v___f_214_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_214_, 0, v_inst_206_);
lean_closure_set(v___f_214_, 1, v_declName_207_);
lean_closure_set(v___f_214_, 2, v___x_208_);
lean_closure_set(v___f_214_, 3, v_type_209_);
lean_closure_set(v___f_214_, 4, v_inst_213_);
v___x_215_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_215_, 0, v_declName_207_);
lean_closure_set(v___x_215_, 1, v_inst_213_);
lean_closure_set(v___x_215_, 2, v_expectedInst_210_);
v___x_216_ = lean_apply_2(v_inst_211_, lean_box(0), v___x_215_);
v___x_217_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_216_, v___f_214_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_type_222_, lean_object* v_u_223_, lean_object* v_instDeclName_224_, lean_object* v_declName_225_, lean_object* v_expectedInst_226_){
_start:
{
lean_object* v_toBind_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_toBind_227_ = lean_ctor_get(v_inst_220_, 1);
lean_inc_n(v_toBind_227_, 2);
v___x_228_ = lean_box(0);
lean_inc_n(v_u_223_, 2);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v_u_223_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v_u_223_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v_u_223_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
lean_inc_ref_n(v_type_222_, 3);
lean_inc_ref(v___x_231_);
lean_inc_ref(v_inst_221_);
v___f_232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_232_, 0, v_inst_221_);
lean_closure_set(v___f_232_, 1, v_declName_225_);
lean_closure_set(v___f_232_, 2, v___x_231_);
lean_closure_set(v___f_232_, 3, v_type_222_);
lean_closure_set(v___f_232_, 4, v_expectedInst_226_);
lean_closure_set(v___f_232_, 5, v_inst_218_);
lean_closure_set(v___f_232_, 6, v_toBind_227_);
v___x_233_ = l_Lean_mkConst(v_instDeclName_224_, v___x_231_);
v___x_234_ = l_Lean_mkApp3(v___x_233_, v_type_222_, v_type_222_, v_type_222_);
v___x_235_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_220_, v_inst_219_, v_inst_221_, v___x_234_);
v___x_236_ = lean_apply_4(v_toBind_227_, lean_box(0), lean_box(0), v___x_235_, v___f_232_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object* v_m_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_type_242_, lean_object* v_u_243_, lean_object* v_instDeclName_244_, lean_object* v_declName_245_, lean_object* v_expectedInst_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_238_, v_inst_239_, v_inst_240_, v_inst_241_, v_type_242_, v_u_243_, v_instDeclName_244_, v_declName_245_, v_expectedInst_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object* v_inst_248_, lean_object* v___x_249_, lean_object* v___x_250_, lean_object* v_type_251_, lean_object* v___x_252_, lean_object* v_inst_253_, lean_object* v_____r_254_){
_start:
{
lean_object* v_canonExpr_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_canonExpr_255_ = lean_ctor_get(v_inst_248_, 0);
lean_inc(v_canonExpr_255_);
lean_dec_ref(v_inst_248_);
v___x_256_ = l_Lean_mkConst(v___x_249_, v___x_250_);
lean_inc_ref(v_type_251_);
v___x_257_ = l_Lean_mkApp4(v___x_256_, v_type_251_, v___x_252_, v_type_251_, v_inst_253_);
v___x_258_ = lean_apply_1(v_canonExpr_255_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object* v___x_269_, lean_object* v_type_270_, lean_object* v_semiringInst_271_, lean_object* v___x_272_, lean_object* v_inst_273_, lean_object* v___x_274_, lean_object* v___x_275_, lean_object* v_inst_276_, lean_object* v_toBind_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_inst_x27_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___f_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4));
v___x_280_ = l_Lean_mkConst(v___x_279_, v___x_269_);
lean_inc_ref(v_type_270_);
v_inst_x27_281_ = l_Lean_mkAppB(v___x_280_, v_type_270_, v_semiringInst_271_);
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5));
v___x_283_ = l_Lean_Name_mkStr2(v___x_272_, v___x_282_);
lean_inc_ref(v_inst_278_);
lean_inc(v___x_283_);
v___f_284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_284_, 0, v_inst_273_);
lean_closure_set(v___f_284_, 1, v___x_283_);
lean_closure_set(v___f_284_, 2, v___x_274_);
lean_closure_set(v___f_284_, 3, v_type_270_);
lean_closure_set(v___f_284_, 4, v___x_275_);
lean_closure_set(v___f_284_, 5, v_inst_278_);
v___x_285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_285_, 0, v___x_283_);
lean_closure_set(v___x_285_, 1, v_inst_278_);
lean_closure_set(v___x_285_, 2, v_inst_x27_281_);
v___x_286_ = lean_apply_2(v_inst_276_, lean_box(0), v___x_285_);
v___x_287_ = lean_apply_4(v_toBind_277_, lean_box(0), lean_box(0), v___x_286_, v___f_284_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Lean_Level_ofNat(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_u_297_, lean_object* v_type_298_, lean_object* v_semiringInst_299_){
_start:
{
lean_object* v_toBind_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_toBind_300_ = lean_ctor_get(v_inst_295_, 1);
lean_inc_n(v_toBind_300_, 2);
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0));
v___x_302_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1));
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_304_ = lean_box(0);
lean_inc(v_u_297_);
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v_u_297_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
lean_inc_ref(v___x_305_);
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v_u_297_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
lean_inc_ref(v___x_307_);
v___x_308_ = l_Lean_mkConst(v___x_302_, v___x_307_);
v___x_309_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_296_);
lean_inc_ref_n(v_type_298_, 2);
v___f_310_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_310_, 0, v___x_305_);
lean_closure_set(v___f_310_, 1, v_type_298_);
lean_closure_set(v___f_310_, 2, v_semiringInst_299_);
lean_closure_set(v___f_310_, 3, v___x_301_);
lean_closure_set(v___f_310_, 4, v_inst_296_);
lean_closure_set(v___f_310_, 5, v___x_307_);
lean_closure_set(v___f_310_, 6, v___x_309_);
lean_closure_set(v___f_310_, 7, v_inst_293_);
lean_closure_set(v___f_310_, 8, v_toBind_300_);
v___x_311_ = l_Lean_mkApp3(v___x_308_, v_type_298_, v___x_309_, v_type_298_);
v___x_312_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_295_, v_inst_294_, v_inst_296_, v___x_311_);
v___x_313_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_312_, v___f_310_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object* v_m_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_u_319_, lean_object* v_type_320_, lean_object* v_semiringInst_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_315_, v_inst_316_, v_inst_317_, v_inst_318_, v_u_319_, v_type_320_, v_semiringInst_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object* v___x_323_, lean_object* v___x_324_, lean_object* v___x_325_, lean_object* v_type_326_, lean_object* v_canonExpr_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = l_Lean_Name_mkStr2(v___x_323_, v___x_324_);
v___x_330_ = l_Lean_mkConst(v___x_329_, v___x_325_);
v___x_331_ = l_Lean_mkAppB(v___x_330_, v_type_326_, v_inst_328_);
v___x_332_ = lean_apply_1(v_canonExpr_327_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object* v___f_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_apply_1(v___f_333_, v_inst_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_336_, lean_object* v_val_337_, lean_object* v_toBind_338_, lean_object* v___f_339_, lean_object* v_____r_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_apply_2(v_toPure_336_, lean_box(0), v_val_337_);
v___x_342_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_341_, v___f_339_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_343_, lean_object* v_inst_x27_344_, lean_object* v_toBind_345_, lean_object* v___f_346_, lean_object* v___f_347_, lean_object* v___x_348_, lean_object* v___x_349_, lean_object* v_inst_350_, lean_object* v_____do__lift_351_){
_start:
{
if (lean_obj_tag(v_____do__lift_351_) == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_inst_350_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_348_);
lean_dec(v___f_347_);
v___x_352_ = lean_apply_2(v_toPure_343_, lean_box(0), v_inst_x27_344_);
v___x_353_ = lean_apply_4(v_toBind_345_, lean_box(0), lean_box(0), v___x_352_, v___f_346_);
return v___x_353_;
}
else
{
lean_object* v_val_354_; lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v___f_346_);
v_val_354_ = lean_ctor_get(v_____do__lift_351_, 0);
lean_inc_n(v_val_354_, 2);
lean_dec_ref_known(v_____do__lift_351_, 1);
lean_inc(v_toBind_345_);
v___f_355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_355_, 0, v_toPure_343_);
lean_closure_set(v___f_355_, 1, v_val_354_);
lean_closure_set(v___f_355_, 2, v_toBind_345_);
lean_closure_set(v___f_355_, 3, v___f_347_);
v___x_356_ = l_Lean_Name_mkStr2(v___x_348_, v___x_349_);
v___x_357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_357_, 0, v___x_356_);
lean_closure_set(v___x_357_, 1, v_val_354_);
lean_closure_set(v___x_357_, 2, v_inst_x27_344_);
v___x_358_ = lean_apply_2(v_inst_350_, lean_box(0), v___x_357_);
v___x_359_ = lean_apply_4(v_toBind_345_, lean_box(0), lean_box(0), v___x_358_, v___f_355_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_u_372_, lean_object* v_type_373_, lean_object* v_semiringInst_374_){
_start:
{
lean_object* v_toApplicative_375_; lean_object* v_toBind_376_; lean_object* v_canonExpr_377_; lean_object* v_synthInstance_x3f_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_400_; 
v_toApplicative_375_ = lean_ctor_get(v_inst_370_, 0);
lean_inc_ref(v_toApplicative_375_);
v_toBind_376_ = lean_ctor_get(v_inst_370_, 1);
lean_inc(v_toBind_376_);
lean_dec_ref(v_inst_370_);
v_canonExpr_377_ = lean_ctor_get(v_inst_371_, 0);
v_synthInstance_x3f_378_ = lean_ctor_get(v_inst_371_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_inst_371_);
if (v_isSharedCheck_400_ == 0)
{
v___x_380_ = v_inst_371_;
v_isShared_381_ = v_isSharedCheck_400_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_synthInstance_x3f_378_);
lean_inc(v_canonExpr_377_);
lean_dec(v_inst_371_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_400_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_toPure_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v_toPure_382_ = lean_ctor_get(v_toApplicative_375_, 1);
lean_inc(v_toPure_382_);
lean_dec_ref(v_toApplicative_375_);
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0));
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1));
v___x_385_ = lean_box(0);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
lean_ctor_set(v___x_380_, 1, v___x_385_);
lean_ctor_set(v___x_380_, 0, v_u_372_);
v___x_387_ = v___x_380_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_u_372_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_399_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v_inst_x27_389_; lean_object* v___x_390_; lean_object* v___f_391_; lean_object* v___f_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_instType_395_; lean_object* v___x_396_; lean_object* v___f_397_; lean_object* v___x_398_; 
lean_inc_ref_n(v___x_387_, 2);
v___x_388_ = l_Lean_mkConst(v___x_384_, v___x_387_);
lean_inc_ref_n(v_type_373_, 2);
v_inst_x27_389_ = l_Lean_mkAppB(v___x_388_, v_type_373_, v_semiringInst_374_);
v___x_390_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2));
v___f_391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_391_, 0, v___x_390_);
lean_closure_set(v___f_391_, 1, v___x_383_);
lean_closure_set(v___f_391_, 2, v___x_387_);
lean_closure_set(v___f_391_, 3, v_type_373_);
lean_closure_set(v___f_391_, 4, v_canonExpr_377_);
v___f_392_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_392_, 0, v___f_391_);
v___x_393_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3));
v___x_394_ = l_Lean_mkConst(v___x_393_, v___x_387_);
v_instType_395_ = l_Lean_Expr_app___override(v___x_394_, v_type_373_);
v___x_396_ = lean_apply_1(v_synthInstance_x3f_378_, v_instType_395_);
lean_inc_ref(v___f_392_);
lean_inc(v_toBind_376_);
v___f_397_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_397_, 0, v_toPure_382_);
lean_closure_set(v___f_397_, 1, v_inst_x27_389_);
lean_closure_set(v___f_397_, 2, v_toBind_376_);
lean_closure_set(v___f_397_, 3, v___f_392_);
lean_closure_set(v___f_397_, 4, v___f_392_);
lean_closure_set(v___f_397_, 5, v___x_390_);
lean_closure_set(v___f_397_, 6, v___x_383_);
lean_closure_set(v___f_397_, 7, v_inst_369_);
v___x_398_ = lean_apply_4(v_toBind_376_, lean_box(0), lean_box(0), v___x_396_, v___f_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object* v_m_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_u_405_, lean_object* v_type_406_, lean_object* v_semiringInst_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_402_, v_inst_403_, v_inst_404_, v_u_405_, v_type_406_, v_semiringInst_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_409_, lean_object* v_s_410_){
_start:
{
lean_object* v_id_411_; lean_object* v_type_412_; lean_object* v_u_413_; lean_object* v_ringInst_414_; lean_object* v_semiringInst_415_; lean_object* v_charInst_x3f_416_; lean_object* v_mulFn_x3f_417_; lean_object* v_subFn_x3f_418_; lean_object* v_negFn_x3f_419_; lean_object* v_powFn_x3f_420_; lean_object* v_intCastFn_x3f_421_; lean_object* v_natCastFn_x3f_422_; lean_object* v_one_x3f_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_431_; 
v_id_411_ = lean_ctor_get(v_s_410_, 0);
v_type_412_ = lean_ctor_get(v_s_410_, 1);
v_u_413_ = lean_ctor_get(v_s_410_, 2);
v_ringInst_414_ = lean_ctor_get(v_s_410_, 3);
v_semiringInst_415_ = lean_ctor_get(v_s_410_, 4);
v_charInst_x3f_416_ = lean_ctor_get(v_s_410_, 5);
v_mulFn_x3f_417_ = lean_ctor_get(v_s_410_, 7);
v_subFn_x3f_418_ = lean_ctor_get(v_s_410_, 8);
v_negFn_x3f_419_ = lean_ctor_get(v_s_410_, 9);
v_powFn_x3f_420_ = lean_ctor_get(v_s_410_, 10);
v_intCastFn_x3f_421_ = lean_ctor_get(v_s_410_, 11);
v_natCastFn_x3f_422_ = lean_ctor_get(v_s_410_, 12);
v_one_x3f_423_ = lean_ctor_get(v_s_410_, 13);
v_isSharedCheck_431_ = !lean_is_exclusive(v_s_410_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_s_410_, 6);
lean_dec(v_unused_432_);
v___x_425_ = v_s_410_;
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_one_x3f_423_);
lean_inc(v_natCastFn_x3f_422_);
lean_inc(v_intCastFn_x3f_421_);
lean_inc(v_powFn_x3f_420_);
lean_inc(v_negFn_x3f_419_);
lean_inc(v_subFn_x3f_418_);
lean_inc(v_mulFn_x3f_417_);
lean_inc(v_charInst_x3f_416_);
lean_inc(v_semiringInst_415_);
lean_inc(v_ringInst_414_);
lean_inc(v_u_413_);
lean_inc(v_type_412_);
lean_inc(v_id_411_);
lean_dec(v_s_410_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_addFn_409_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 6, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_id_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_type_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_u_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_ringInst_414_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_semiringInst_415_);
lean_ctor_set(v_reuseFailAlloc_430_, 5, v_charInst_x3f_416_);
lean_ctor_set(v_reuseFailAlloc_430_, 6, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_430_, 7, v_mulFn_x3f_417_);
lean_ctor_set(v_reuseFailAlloc_430_, 8, v_subFn_x3f_418_);
lean_ctor_set(v_reuseFailAlloc_430_, 9, v_negFn_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_430_, 10, v_powFn_x3f_420_);
lean_ctor_set(v_reuseFailAlloc_430_, 11, v_intCastFn_x3f_421_);
lean_ctor_set(v_reuseFailAlloc_430_, 12, v_natCastFn_x3f_422_);
lean_ctor_set(v_reuseFailAlloc_430_, 13, v_one_x3f_423_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_433_, lean_object* v_addFn_434_, lean_object* v_____r_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_apply_2(v_toPure_433_, lean_box(0), v_addFn_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_437_, lean_object* v_modifyRing_438_, lean_object* v_toBind_439_, lean_object* v_addFn_440_){
_start:
{
lean_object* v___f_441_; lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_inc_ref(v_addFn_440_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_441_, 0, v_addFn_440_);
v___f_442_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_442_, 0, v_toPure_437_);
lean_closure_set(v___f_442_, 1, v_addFn_440_);
v___x_443_ = lean_apply_1(v_modifyRing_438_, v___f_441_);
v___x_444_ = lean_apply_4(v_toBind_439_, lean_box(0), lean_box(0), v___x_443_, v___f_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_toBind_466_, lean_object* v___f_467_, lean_object* v_ring_468_){
_start:
{
lean_object* v_addFn_x3f_469_; 
v_addFn_x3f_469_ = lean_ctor_get(v_ring_468_, 6);
if (lean_obj_tag(v_addFn_x3f_469_) == 1)
{
lean_object* v_val_470_; lean_object* v___x_471_; 
lean_inc_ref(v_addFn_x3f_469_);
lean_dec_ref(v_ring_468_);
lean_dec(v___f_467_);
lean_dec(v_toBind_466_);
lean_dec_ref(v_inst_465_);
lean_dec_ref(v_inst_464_);
lean_dec_ref(v_inst_463_);
lean_dec(v_inst_462_);
v_val_470_ = lean_ctor_get(v_addFn_x3f_469_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v_addFn_x3f_469_, 1);
v___x_471_ = lean_apply_2(v_toPure_461_, lean_box(0), v_val_470_);
return v___x_471_;
}
else
{
lean_object* v_type_472_; lean_object* v_u_473_; lean_object* v_semiringInst_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_expectedInst_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_toPure_461_);
v_type_472_ = lean_ctor_get(v_ring_468_, 1);
lean_inc_ref_n(v_type_472_, 3);
v_u_473_ = lean_ctor_get(v_ring_468_, 2);
lean_inc_n(v_u_473_, 2);
v_semiringInst_474_ = lean_ctor_get(v_ring_468_, 4);
lean_inc_ref(v_semiringInst_474_);
lean_dec_ref(v_ring_468_);
v___x_475_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_476_ = lean_box(0);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_u_473_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_inc_ref(v___x_477_);
v___x_478_ = l_Lean_mkConst(v___x_475_, v___x_477_);
v___x_479_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_480_ = l_Lean_mkConst(v___x_479_, v___x_477_);
v___x_481_ = l_Lean_mkAppB(v___x_480_, v_type_472_, v_semiringInst_474_);
v_expectedInst_482_ = l_Lean_mkAppB(v___x_478_, v_type_472_, v___x_481_);
v___x_483_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_484_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_485_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_462_, v_inst_463_, v_inst_464_, v_inst_465_, v_type_472_, v_u_473_, v___x_483_, v___x_484_, v_expectedInst_482_);
v___x_486_ = lean_apply_4(v_toBind_466_, lean_box(0), lean_box(0), v___x_485_, v___f_467_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_){
_start:
{
lean_object* v_toApplicative_492_; lean_object* v_toBind_493_; lean_object* v_getRing_494_; lean_object* v_modifyRing_495_; lean_object* v_toPure_496_; lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v___x_499_; 
v_toApplicative_492_ = lean_ctor_get(v_inst_489_, 0);
v_toBind_493_ = lean_ctor_get(v_inst_489_, 1);
lean_inc_n(v_toBind_493_, 3);
v_getRing_494_ = lean_ctor_get(v_inst_491_, 0);
lean_inc(v_getRing_494_);
v_modifyRing_495_ = lean_ctor_get(v_inst_491_, 1);
lean_inc(v_modifyRing_495_);
lean_dec_ref(v_inst_491_);
v_toPure_496_ = lean_ctor_get(v_toApplicative_492_, 1);
lean_inc_n(v_toPure_496_, 2);
v___f_497_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_497_, 0, v_toPure_496_);
lean_closure_set(v___f_497_, 1, v_modifyRing_495_);
lean_closure_set(v___f_497_, 2, v_toBind_493_);
v___f_498_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_498_, 0, v_toPure_496_);
lean_closure_set(v___f_498_, 1, v_inst_487_);
lean_closure_set(v___f_498_, 2, v_inst_488_);
lean_closure_set(v___f_498_, 3, v_inst_489_);
lean_closure_set(v___f_498_, 4, v_inst_490_);
lean_closure_set(v___f_498_, 5, v_toBind_493_);
lean_closure_set(v___f_498_, 6, v___f_497_);
v___x_499_ = lean_apply_4(v_toBind_493_, lean_box(0), lean_box(0), v_getRing_494_, v___f_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_501_, v_inst_502_, v_inst_503_, v_inst_504_, v_inst_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_507_, lean_object* v_s_508_){
_start:
{
lean_object* v_id_509_; lean_object* v_type_510_; lean_object* v_u_511_; lean_object* v_ringInst_512_; lean_object* v_semiringInst_513_; lean_object* v_charInst_x3f_514_; lean_object* v_addFn_x3f_515_; lean_object* v_subFn_x3f_516_; lean_object* v_negFn_x3f_517_; lean_object* v_powFn_x3f_518_; lean_object* v_intCastFn_x3f_519_; lean_object* v_natCastFn_x3f_520_; lean_object* v_one_x3f_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_529_; 
v_id_509_ = lean_ctor_get(v_s_508_, 0);
v_type_510_ = lean_ctor_get(v_s_508_, 1);
v_u_511_ = lean_ctor_get(v_s_508_, 2);
v_ringInst_512_ = lean_ctor_get(v_s_508_, 3);
v_semiringInst_513_ = lean_ctor_get(v_s_508_, 4);
v_charInst_x3f_514_ = lean_ctor_get(v_s_508_, 5);
v_addFn_x3f_515_ = lean_ctor_get(v_s_508_, 6);
v_subFn_x3f_516_ = lean_ctor_get(v_s_508_, 8);
v_negFn_x3f_517_ = lean_ctor_get(v_s_508_, 9);
v_powFn_x3f_518_ = lean_ctor_get(v_s_508_, 10);
v_intCastFn_x3f_519_ = lean_ctor_get(v_s_508_, 11);
v_natCastFn_x3f_520_ = lean_ctor_get(v_s_508_, 12);
v_one_x3f_521_ = lean_ctor_get(v_s_508_, 13);
v_isSharedCheck_529_ = !lean_is_exclusive(v_s_508_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_s_508_, 7);
lean_dec(v_unused_530_);
v___x_523_ = v_s_508_;
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_one_x3f_521_);
lean_inc(v_natCastFn_x3f_520_);
lean_inc(v_intCastFn_x3f_519_);
lean_inc(v_powFn_x3f_518_);
lean_inc(v_negFn_x3f_517_);
lean_inc(v_subFn_x3f_516_);
lean_inc(v_addFn_x3f_515_);
lean_inc(v_charInst_x3f_514_);
lean_inc(v_semiringInst_513_);
lean_inc(v_ringInst_512_);
lean_inc(v_u_511_);
lean_inc(v_type_510_);
lean_inc(v_id_509_);
lean_dec(v_s_508_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_mulFn_507_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 7, v___x_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_id_509_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_type_510_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_u_511_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v_ringInst_512_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v_semiringInst_513_);
lean_ctor_set(v_reuseFailAlloc_528_, 5, v_charInst_x3f_514_);
lean_ctor_set(v_reuseFailAlloc_528_, 6, v_addFn_x3f_515_);
lean_ctor_set(v_reuseFailAlloc_528_, 7, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_528_, 8, v_subFn_x3f_516_);
lean_ctor_set(v_reuseFailAlloc_528_, 9, v_negFn_x3f_517_);
lean_ctor_set(v_reuseFailAlloc_528_, 10, v_powFn_x3f_518_);
lean_ctor_set(v_reuseFailAlloc_528_, 11, v_intCastFn_x3f_519_);
lean_ctor_set(v_reuseFailAlloc_528_, 12, v_natCastFn_x3f_520_);
lean_ctor_set(v_reuseFailAlloc_528_, 13, v_one_x3f_521_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object* v_toPure_531_, lean_object* v_mulFn_532_, lean_object* v_____r_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_apply_2(v_toPure_531_, lean_box(0), v_mulFn_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object* v_toPure_535_, lean_object* v_modifyRing_536_, lean_object* v_toBind_537_, lean_object* v_mulFn_538_){
_start:
{
lean_object* v___f_539_; lean_object* v___f_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
lean_inc_ref(v_mulFn_538_);
v___f_539_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_539_, 0, v_mulFn_538_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_540_, 0, v_toPure_535_);
lean_closure_set(v___f_540_, 1, v_mulFn_538_);
v___x_541_ = lean_apply_1(v_modifyRing_536_, v___f_539_);
v___x_542_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_541_, v___f_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object* v_toPure_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_toBind_564_, lean_object* v___f_565_, lean_object* v_ring_566_){
_start:
{
lean_object* v_mulFn_x3f_567_; 
v_mulFn_x3f_567_ = lean_ctor_get(v_ring_566_, 7);
if (lean_obj_tag(v_mulFn_x3f_567_) == 1)
{
lean_object* v_val_568_; lean_object* v___x_569_; 
lean_inc_ref(v_mulFn_x3f_567_);
lean_dec_ref(v_ring_566_);
lean_dec(v___f_565_);
lean_dec(v_toBind_564_);
lean_dec_ref(v_inst_563_);
lean_dec_ref(v_inst_562_);
lean_dec_ref(v_inst_561_);
lean_dec(v_inst_560_);
v_val_568_ = lean_ctor_get(v_mulFn_x3f_567_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v_mulFn_x3f_567_, 1);
v___x_569_ = lean_apply_2(v_toPure_559_, lean_box(0), v_val_568_);
return v___x_569_;
}
else
{
lean_object* v_type_570_; lean_object* v_u_571_; lean_object* v_semiringInst_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_expectedInst_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v_toPure_559_);
v_type_570_ = lean_ctor_get(v_ring_566_, 1);
lean_inc_ref_n(v_type_570_, 3);
v_u_571_ = lean_ctor_get(v_ring_566_, 2);
lean_inc_n(v_u_571_, 2);
v_semiringInst_572_ = lean_ctor_get(v_ring_566_, 4);
lean_inc_ref(v_semiringInst_572_);
lean_dec_ref(v_ring_566_);
v___x_573_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_574_ = lean_box(0);
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v_u_571_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
lean_inc_ref(v___x_575_);
v___x_576_ = l_Lean_mkConst(v___x_573_, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_578_ = l_Lean_mkConst(v___x_577_, v___x_575_);
v___x_579_ = l_Lean_mkAppB(v___x_578_, v_type_570_, v_semiringInst_572_);
v_expectedInst_580_ = l_Lean_mkAppB(v___x_576_, v_type_570_, v___x_579_);
v___x_581_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_582_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_583_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_560_, v_inst_561_, v_inst_562_, v_inst_563_, v_type_570_, v_u_571_, v___x_581_, v___x_582_, v_expectedInst_580_);
v___x_584_ = lean_apply_4(v_toBind_564_, lean_box(0), lean_box(0), v___x_583_, v___f_565_);
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_){
_start:
{
lean_object* v_toApplicative_590_; lean_object* v_toBind_591_; lean_object* v_getRing_592_; lean_object* v_modifyRing_593_; lean_object* v_toPure_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; 
v_toApplicative_590_ = lean_ctor_get(v_inst_587_, 0);
v_toBind_591_ = lean_ctor_get(v_inst_587_, 1);
lean_inc_n(v_toBind_591_, 3);
v_getRing_592_ = lean_ctor_get(v_inst_589_, 0);
lean_inc(v_getRing_592_);
v_modifyRing_593_ = lean_ctor_get(v_inst_589_, 1);
lean_inc(v_modifyRing_593_);
lean_dec_ref(v_inst_589_);
v_toPure_594_ = lean_ctor_get(v_toApplicative_590_, 1);
lean_inc_n(v_toPure_594_, 2);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_595_, 0, v_toPure_594_);
lean_closure_set(v___f_595_, 1, v_modifyRing_593_);
lean_closure_set(v___f_595_, 2, v_toBind_591_);
v___f_596_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_596_, 0, v_toPure_594_);
lean_closure_set(v___f_596_, 1, v_inst_585_);
lean_closure_set(v___f_596_, 2, v_inst_586_);
lean_closure_set(v___f_596_, 3, v_inst_587_);
lean_closure_set(v___f_596_, 4, v_inst_588_);
lean_closure_set(v___f_596_, 5, v_toBind_591_);
lean_closure_set(v___f_596_, 6, v___f_595_);
v___x_597_ = lean_apply_4(v_toBind_591_, lean_box(0), lean_box(0), v_getRing_592_, v___f_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object* v_m_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_599_, v_inst_600_, v_inst_601_, v_inst_602_, v_inst_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object* v_subFn_605_, lean_object* v_s_606_){
_start:
{
lean_object* v_id_607_; lean_object* v_type_608_; lean_object* v_u_609_; lean_object* v_ringInst_610_; lean_object* v_semiringInst_611_; lean_object* v_charInst_x3f_612_; lean_object* v_addFn_x3f_613_; lean_object* v_mulFn_x3f_614_; lean_object* v_negFn_x3f_615_; lean_object* v_powFn_x3f_616_; lean_object* v_intCastFn_x3f_617_; lean_object* v_natCastFn_x3f_618_; lean_object* v_one_x3f_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
v_id_607_ = lean_ctor_get(v_s_606_, 0);
v_type_608_ = lean_ctor_get(v_s_606_, 1);
v_u_609_ = lean_ctor_get(v_s_606_, 2);
v_ringInst_610_ = lean_ctor_get(v_s_606_, 3);
v_semiringInst_611_ = lean_ctor_get(v_s_606_, 4);
v_charInst_x3f_612_ = lean_ctor_get(v_s_606_, 5);
v_addFn_x3f_613_ = lean_ctor_get(v_s_606_, 6);
v_mulFn_x3f_614_ = lean_ctor_get(v_s_606_, 7);
v_negFn_x3f_615_ = lean_ctor_get(v_s_606_, 9);
v_powFn_x3f_616_ = lean_ctor_get(v_s_606_, 10);
v_intCastFn_x3f_617_ = lean_ctor_get(v_s_606_, 11);
v_natCastFn_x3f_618_ = lean_ctor_get(v_s_606_, 12);
v_one_x3f_619_ = lean_ctor_get(v_s_606_, 13);
v_isSharedCheck_627_ = !lean_is_exclusive(v_s_606_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_s_606_, 8);
lean_dec(v_unused_628_);
v___x_621_ = v_s_606_;
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_one_x3f_619_);
lean_inc(v_natCastFn_x3f_618_);
lean_inc(v_intCastFn_x3f_617_);
lean_inc(v_powFn_x3f_616_);
lean_inc(v_negFn_x3f_615_);
lean_inc(v_mulFn_x3f_614_);
lean_inc(v_addFn_x3f_613_);
lean_inc(v_charInst_x3f_612_);
lean_inc(v_semiringInst_611_);
lean_inc(v_ringInst_610_);
lean_inc(v_u_609_);
lean_inc(v_type_608_);
lean_inc(v_id_607_);
lean_dec(v_s_606_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v_subFn_605_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 8, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_id_607_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_type_608_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_u_609_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_ringInst_610_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_semiringInst_611_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v_charInst_x3f_612_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_addFn_x3f_613_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_mulFn_x3f_614_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 9, v_negFn_x3f_615_);
lean_ctor_set(v_reuseFailAlloc_626_, 10, v_powFn_x3f_616_);
lean_ctor_set(v_reuseFailAlloc_626_, 11, v_intCastFn_x3f_617_);
lean_ctor_set(v_reuseFailAlloc_626_, 12, v_natCastFn_x3f_618_);
lean_ctor_set(v_reuseFailAlloc_626_, 13, v_one_x3f_619_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_629_, lean_object* v_subFn_630_, lean_object* v_____r_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_apply_2(v_toPure_629_, lean_box(0), v_subFn_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_633_, lean_object* v_modifyRing_634_, lean_object* v_toBind_635_, lean_object* v_subFn_636_){
_start:
{
lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_inc_ref(v_subFn_636_);
v___f_637_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_637_, 0, v_subFn_636_);
v___f_638_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_638_, 0, v_toPure_633_);
lean_closure_set(v___f_638_, 1, v_subFn_636_);
v___x_639_ = lean_apply_1(v_modifyRing_634_, v___f_637_);
v___x_640_ = lean_apply_4(v_toBind_635_, lean_box(0), lean_box(0), v___x_639_, v___f_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_toBind_663_, lean_object* v___f_664_, lean_object* v_ring_665_){
_start:
{
lean_object* v_subFn_x3f_666_; 
v_subFn_x3f_666_ = lean_ctor_get(v_ring_665_, 8);
if (lean_obj_tag(v_subFn_x3f_666_) == 1)
{
lean_object* v_val_667_; lean_object* v___x_668_; 
lean_inc_ref(v_subFn_x3f_666_);
lean_dec_ref(v_ring_665_);
lean_dec(v___f_664_);
lean_dec(v_toBind_663_);
lean_dec_ref(v_inst_662_);
lean_dec_ref(v_inst_661_);
lean_dec_ref(v_inst_660_);
lean_dec(v_inst_659_);
v_val_667_ = lean_ctor_get(v_subFn_x3f_666_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v_subFn_x3f_666_, 1);
v___x_668_ = lean_apply_2(v_toPure_658_, lean_box(0), v_val_667_);
return v___x_668_;
}
else
{
lean_object* v_type_669_; lean_object* v_u_670_; lean_object* v_ringInst_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_expectedInst_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_toPure_658_);
v_type_669_ = lean_ctor_get(v_ring_665_, 1);
lean_inc_ref_n(v_type_669_, 3);
v_u_670_ = lean_ctor_get(v_ring_665_, 2);
lean_inc_n(v_u_670_, 2);
v_ringInst_671_ = lean_ctor_get(v_ring_665_, 3);
lean_inc_ref(v_ringInst_671_);
lean_dec_ref(v_ring_665_);
v___x_672_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_673_ = lean_box(0);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v_u_670_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
lean_inc_ref(v___x_674_);
v___x_675_ = l_Lean_mkConst(v___x_672_, v___x_674_);
v___x_676_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4));
v___x_677_ = l_Lean_mkConst(v___x_676_, v___x_674_);
v___x_678_ = l_Lean_mkAppB(v___x_677_, v_type_669_, v_ringInst_671_);
v_expectedInst_679_ = l_Lean_mkAppB(v___x_675_, v_type_669_, v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6));
v___x_681_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8));
v___x_682_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_659_, v_inst_660_, v_inst_661_, v_inst_662_, v_type_669_, v_u_670_, v___x_680_, v___x_681_, v_expectedInst_679_);
v___x_683_ = lean_apply_4(v_toBind_663_, lean_box(0), lean_box(0), v___x_682_, v___f_664_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_){
_start:
{
lean_object* v_toApplicative_689_; lean_object* v_toBind_690_; lean_object* v_getRing_691_; lean_object* v_modifyRing_692_; lean_object* v_toPure_693_; lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___x_696_; 
v_toApplicative_689_ = lean_ctor_get(v_inst_686_, 0);
v_toBind_690_ = lean_ctor_get(v_inst_686_, 1);
lean_inc_n(v_toBind_690_, 3);
v_getRing_691_ = lean_ctor_get(v_inst_688_, 0);
lean_inc(v_getRing_691_);
v_modifyRing_692_ = lean_ctor_get(v_inst_688_, 1);
lean_inc(v_modifyRing_692_);
lean_dec_ref(v_inst_688_);
v_toPure_693_ = lean_ctor_get(v_toApplicative_689_, 1);
lean_inc_n(v_toPure_693_, 2);
v___f_694_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_694_, 0, v_toPure_693_);
lean_closure_set(v___f_694_, 1, v_modifyRing_692_);
lean_closure_set(v___f_694_, 2, v_toBind_690_);
v___f_695_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_695_, 0, v_toPure_693_);
lean_closure_set(v___f_695_, 1, v_inst_684_);
lean_closure_set(v___f_695_, 2, v_inst_685_);
lean_closure_set(v___f_695_, 3, v_inst_686_);
lean_closure_set(v___f_695_, 4, v_inst_687_);
lean_closure_set(v___f_695_, 5, v_toBind_690_);
lean_closure_set(v___f_695_, 6, v___f_694_);
v___x_696_ = lean_apply_4(v_toBind_690_, lean_box(0), lean_box(0), v_getRing_691_, v___f_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_698_, v_inst_699_, v_inst_700_, v_inst_701_, v_inst_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_704_, lean_object* v_s_705_){
_start:
{
lean_object* v_id_706_; lean_object* v_type_707_; lean_object* v_u_708_; lean_object* v_ringInst_709_; lean_object* v_semiringInst_710_; lean_object* v_charInst_x3f_711_; lean_object* v_addFn_x3f_712_; lean_object* v_mulFn_x3f_713_; lean_object* v_subFn_x3f_714_; lean_object* v_powFn_x3f_715_; lean_object* v_intCastFn_x3f_716_; lean_object* v_natCastFn_x3f_717_; lean_object* v_one_x3f_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_id_706_ = lean_ctor_get(v_s_705_, 0);
v_type_707_ = lean_ctor_get(v_s_705_, 1);
v_u_708_ = lean_ctor_get(v_s_705_, 2);
v_ringInst_709_ = lean_ctor_get(v_s_705_, 3);
v_semiringInst_710_ = lean_ctor_get(v_s_705_, 4);
v_charInst_x3f_711_ = lean_ctor_get(v_s_705_, 5);
v_addFn_x3f_712_ = lean_ctor_get(v_s_705_, 6);
v_mulFn_x3f_713_ = lean_ctor_get(v_s_705_, 7);
v_subFn_x3f_714_ = lean_ctor_get(v_s_705_, 8);
v_powFn_x3f_715_ = lean_ctor_get(v_s_705_, 10);
v_intCastFn_x3f_716_ = lean_ctor_get(v_s_705_, 11);
v_natCastFn_x3f_717_ = lean_ctor_get(v_s_705_, 12);
v_one_x3f_718_ = lean_ctor_get(v_s_705_, 13);
v_isSharedCheck_726_ = !lean_is_exclusive(v_s_705_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_s_705_, 9);
lean_dec(v_unused_727_);
v___x_720_ = v_s_705_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_one_x3f_718_);
lean_inc(v_natCastFn_x3f_717_);
lean_inc(v_intCastFn_x3f_716_);
lean_inc(v_powFn_x3f_715_);
lean_inc(v_subFn_x3f_714_);
lean_inc(v_mulFn_x3f_713_);
lean_inc(v_addFn_x3f_712_);
lean_inc(v_charInst_x3f_711_);
lean_inc(v_semiringInst_710_);
lean_inc(v_ringInst_709_);
lean_inc(v_u_708_);
lean_inc(v_type_707_);
lean_inc(v_id_706_);
lean_dec(v_s_705_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v_negFn_704_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 9, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_id_706_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_type_707_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_u_708_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_ringInst_709_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_semiringInst_710_);
lean_ctor_set(v_reuseFailAlloc_725_, 5, v_charInst_x3f_711_);
lean_ctor_set(v_reuseFailAlloc_725_, 6, v_addFn_x3f_712_);
lean_ctor_set(v_reuseFailAlloc_725_, 7, v_mulFn_x3f_713_);
lean_ctor_set(v_reuseFailAlloc_725_, 8, v_subFn_x3f_714_);
lean_ctor_set(v_reuseFailAlloc_725_, 9, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 10, v_powFn_x3f_715_);
lean_ctor_set(v_reuseFailAlloc_725_, 11, v_intCastFn_x3f_716_);
lean_ctor_set(v_reuseFailAlloc_725_, 12, v_natCastFn_x3f_717_);
lean_ctor_set(v_reuseFailAlloc_725_, 13, v_one_x3f_718_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_728_, lean_object* v_negFn_729_, lean_object* v_____r_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_apply_2(v_toPure_728_, lean_box(0), v_negFn_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_732_, lean_object* v_modifyRing_733_, lean_object* v_toBind_734_, lean_object* v_negFn_735_){
_start:
{
lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_inc_ref(v_negFn_735_);
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_736_, 0, v_negFn_735_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_737_, 0, v_toPure_732_);
lean_closure_set(v___f_737_, 1, v_negFn_735_);
v___x_738_ = lean_apply_1(v_modifyRing_733_, v___f_736_);
v___x_739_ = lean_apply_4(v_toBind_734_, lean_box(0), lean_box(0), v___x_738_, v___f_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_toBind_758_, lean_object* v___f_759_, lean_object* v_ring_760_){
_start:
{
lean_object* v_negFn_x3f_761_; 
v_negFn_x3f_761_ = lean_ctor_get(v_ring_760_, 9);
if (lean_obj_tag(v_negFn_x3f_761_) == 1)
{
lean_object* v_val_762_; lean_object* v___x_763_; 
lean_inc_ref(v_negFn_x3f_761_);
lean_dec_ref(v_ring_760_);
lean_dec(v___f_759_);
lean_dec(v_toBind_758_);
lean_dec_ref(v_inst_757_);
lean_dec_ref(v_inst_756_);
lean_dec_ref(v_inst_755_);
lean_dec(v_inst_754_);
v_val_762_ = lean_ctor_get(v_negFn_x3f_761_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v_negFn_x3f_761_, 1);
v___x_763_ = lean_apply_2(v_toPure_753_, lean_box(0), v_val_762_);
return v___x_763_;
}
else
{
lean_object* v_type_764_; lean_object* v_u_765_; lean_object* v_ringInst_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_expectedInst_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_toPure_753_);
v_type_764_ = lean_ctor_get(v_ring_760_, 1);
lean_inc_ref_n(v_type_764_, 2);
v_u_765_ = lean_ctor_get(v_ring_760_, 2);
lean_inc_n(v_u_765_, 2);
v_ringInst_766_ = lean_ctor_get(v_ring_760_, 3);
lean_inc_ref(v_ringInst_766_);
lean_dec_ref(v_ring_760_);
v___x_767_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v_u_765_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_mkConst(v___x_767_, v___x_769_);
v_expectedInst_771_ = l_Lean_mkAppB(v___x_770_, v_type_764_, v_ringInst_766_);
v___x_772_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_773_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_774_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_754_, v_inst_755_, v_inst_756_, v_inst_757_, v_type_764_, v_u_765_, v___x_772_, v___x_773_, v_expectedInst_771_);
v___x_775_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_774_, v___f_759_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_){
_start:
{
lean_object* v_toApplicative_781_; lean_object* v_toBind_782_; lean_object* v_getRing_783_; lean_object* v_modifyRing_784_; lean_object* v_toPure_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_788_; 
v_toApplicative_781_ = lean_ctor_get(v_inst_778_, 0);
v_toBind_782_ = lean_ctor_get(v_inst_778_, 1);
lean_inc_n(v_toBind_782_, 3);
v_getRing_783_ = lean_ctor_get(v_inst_780_, 0);
lean_inc(v_getRing_783_);
v_modifyRing_784_ = lean_ctor_get(v_inst_780_, 1);
lean_inc(v_modifyRing_784_);
lean_dec_ref(v_inst_780_);
v_toPure_785_ = lean_ctor_get(v_toApplicative_781_, 1);
lean_inc_n(v_toPure_785_, 2);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_786_, 0, v_toPure_785_);
lean_closure_set(v___f_786_, 1, v_modifyRing_784_);
lean_closure_set(v___f_786_, 2, v_toBind_782_);
v___f_787_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_787_, 0, v_toPure_785_);
lean_closure_set(v___f_787_, 1, v_inst_776_);
lean_closure_set(v___f_787_, 2, v_inst_777_);
lean_closure_set(v___f_787_, 3, v_inst_778_);
lean_closure_set(v___f_787_, 4, v_inst_779_);
lean_closure_set(v___f_787_, 5, v_toBind_782_);
lean_closure_set(v___f_787_, 6, v___f_786_);
v___x_788_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v_getRing_783_, v___f_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_inst_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_790_, v_inst_791_, v_inst_792_, v_inst_793_, v_inst_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_796_, lean_object* v_s_797_){
_start:
{
lean_object* v_id_798_; lean_object* v_type_799_; lean_object* v_u_800_; lean_object* v_ringInst_801_; lean_object* v_semiringInst_802_; lean_object* v_charInst_x3f_803_; lean_object* v_addFn_x3f_804_; lean_object* v_mulFn_x3f_805_; lean_object* v_subFn_x3f_806_; lean_object* v_negFn_x3f_807_; lean_object* v_intCastFn_x3f_808_; lean_object* v_natCastFn_x3f_809_; lean_object* v_one_x3f_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_818_; 
v_id_798_ = lean_ctor_get(v_s_797_, 0);
v_type_799_ = lean_ctor_get(v_s_797_, 1);
v_u_800_ = lean_ctor_get(v_s_797_, 2);
v_ringInst_801_ = lean_ctor_get(v_s_797_, 3);
v_semiringInst_802_ = lean_ctor_get(v_s_797_, 4);
v_charInst_x3f_803_ = lean_ctor_get(v_s_797_, 5);
v_addFn_x3f_804_ = lean_ctor_get(v_s_797_, 6);
v_mulFn_x3f_805_ = lean_ctor_get(v_s_797_, 7);
v_subFn_x3f_806_ = lean_ctor_get(v_s_797_, 8);
v_negFn_x3f_807_ = lean_ctor_get(v_s_797_, 9);
v_intCastFn_x3f_808_ = lean_ctor_get(v_s_797_, 11);
v_natCastFn_x3f_809_ = lean_ctor_get(v_s_797_, 12);
v_one_x3f_810_ = lean_ctor_get(v_s_797_, 13);
v_isSharedCheck_818_ = !lean_is_exclusive(v_s_797_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_s_797_, 10);
lean_dec(v_unused_819_);
v___x_812_ = v_s_797_;
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_one_x3f_810_);
lean_inc(v_natCastFn_x3f_809_);
lean_inc(v_intCastFn_x3f_808_);
lean_inc(v_negFn_x3f_807_);
lean_inc(v_subFn_x3f_806_);
lean_inc(v_mulFn_x3f_805_);
lean_inc(v_addFn_x3f_804_);
lean_inc(v_charInst_x3f_803_);
lean_inc(v_semiringInst_802_);
lean_inc(v_ringInst_801_);
lean_inc(v_u_800_);
lean_inc(v_type_799_);
lean_inc(v_id_798_);
lean_dec(v_s_797_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v_powFn_796_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 10, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_id_798_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_type_799_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_u_800_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_ringInst_801_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_semiringInst_802_);
lean_ctor_set(v_reuseFailAlloc_817_, 5, v_charInst_x3f_803_);
lean_ctor_set(v_reuseFailAlloc_817_, 6, v_addFn_x3f_804_);
lean_ctor_set(v_reuseFailAlloc_817_, 7, v_mulFn_x3f_805_);
lean_ctor_set(v_reuseFailAlloc_817_, 8, v_subFn_x3f_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 9, v_negFn_x3f_807_);
lean_ctor_set(v_reuseFailAlloc_817_, 10, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_817_, 11, v_intCastFn_x3f_808_);
lean_ctor_set(v_reuseFailAlloc_817_, 12, v_natCastFn_x3f_809_);
lean_ctor_set(v_reuseFailAlloc_817_, 13, v_one_x3f_810_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_820_, lean_object* v_powFn_821_, lean_object* v_____r_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lean_apply_2(v_toPure_820_, lean_box(0), v_powFn_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_824_, lean_object* v_modifyRing_825_, lean_object* v_toBind_826_, lean_object* v_powFn_827_){
_start:
{
lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_inc_ref(v_powFn_827_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_828_, 0, v_powFn_827_);
v___f_829_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_829_, 0, v_toPure_824_);
lean_closure_set(v___f_829_, 1, v_powFn_827_);
v___x_830_ = lean_apply_1(v_modifyRing_825_, v___f_828_);
v___x_831_ = lean_apply_4(v_toBind_826_, lean_box(0), lean_box(0), v___x_830_, v___f_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_toBind_837_, lean_object* v___f_838_, lean_object* v_ring_839_){
_start:
{
lean_object* v_powFn_x3f_840_; 
v_powFn_x3f_840_ = lean_ctor_get(v_ring_839_, 10);
if (lean_obj_tag(v_powFn_x3f_840_) == 1)
{
lean_object* v_val_841_; lean_object* v___x_842_; 
lean_inc_ref(v_powFn_x3f_840_);
lean_dec_ref(v_ring_839_);
lean_dec(v___f_838_);
lean_dec(v_toBind_837_);
lean_dec_ref(v_inst_836_);
lean_dec_ref(v_inst_835_);
lean_dec_ref(v_inst_834_);
lean_dec(v_inst_833_);
v_val_841_ = lean_ctor_get(v_powFn_x3f_840_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v_powFn_x3f_840_, 1);
v___x_842_ = lean_apply_2(v_toPure_832_, lean_box(0), v_val_841_);
return v___x_842_;
}
else
{
lean_object* v_type_843_; lean_object* v_u_844_; lean_object* v_semiringInst_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v_toPure_832_);
v_type_843_ = lean_ctor_get(v_ring_839_, 1);
lean_inc_ref(v_type_843_);
v_u_844_ = lean_ctor_get(v_ring_839_, 2);
lean_inc(v_u_844_);
v_semiringInst_845_ = lean_ctor_get(v_ring_839_, 4);
lean_inc_ref(v_semiringInst_845_);
lean_dec_ref(v_ring_839_);
v___x_846_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_833_, v_inst_834_, v_inst_835_, v_inst_836_, v_u_844_, v_type_843_, v_semiringInst_845_);
v___x_847_ = lean_apply_4(v_toBind_837_, lean_box(0), lean_box(0), v___x_846_, v___f_838_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v_toApplicative_853_; lean_object* v_toBind_854_; lean_object* v_getRing_855_; lean_object* v_modifyRing_856_; lean_object* v_toPure_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___x_860_; 
v_toApplicative_853_ = lean_ctor_get(v_inst_850_, 0);
v_toBind_854_ = lean_ctor_get(v_inst_850_, 1);
lean_inc_n(v_toBind_854_, 3);
v_getRing_855_ = lean_ctor_get(v_inst_852_, 0);
lean_inc(v_getRing_855_);
v_modifyRing_856_ = lean_ctor_get(v_inst_852_, 1);
lean_inc(v_modifyRing_856_);
lean_dec_ref(v_inst_852_);
v_toPure_857_ = lean_ctor_get(v_toApplicative_853_, 1);
lean_inc_n(v_toPure_857_, 2);
v___f_858_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_858_, 0, v_toPure_857_);
lean_closure_set(v___f_858_, 1, v_modifyRing_856_);
lean_closure_set(v___f_858_, 2, v_toBind_854_);
v___f_859_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_859_, 0, v_toPure_857_);
lean_closure_set(v___f_859_, 1, v_inst_848_);
lean_closure_set(v___f_859_, 2, v_inst_849_);
lean_closure_set(v___f_859_, 3, v_inst_850_);
lean_closure_set(v___f_859_, 4, v_inst_851_);
lean_closure_set(v___f_859_, 5, v_toBind_854_);
lean_closure_set(v___f_859_, 6, v___f_858_);
v___x_860_ = lean_apply_4(v_toBind_854_, lean_box(0), lean_box(0), v_getRing_855_, v___f_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_inst_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_862_, v_inst_863_, v_inst_864_, v_inst_865_, v_inst_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_868_, lean_object* v_s_869_){
_start:
{
lean_object* v_id_870_; lean_object* v_type_871_; lean_object* v_u_872_; lean_object* v_ringInst_873_; lean_object* v_semiringInst_874_; lean_object* v_charInst_x3f_875_; lean_object* v_addFn_x3f_876_; lean_object* v_mulFn_x3f_877_; lean_object* v_subFn_x3f_878_; lean_object* v_negFn_x3f_879_; lean_object* v_powFn_x3f_880_; lean_object* v_natCastFn_x3f_881_; lean_object* v_one_x3f_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_890_; 
v_id_870_ = lean_ctor_get(v_s_869_, 0);
v_type_871_ = lean_ctor_get(v_s_869_, 1);
v_u_872_ = lean_ctor_get(v_s_869_, 2);
v_ringInst_873_ = lean_ctor_get(v_s_869_, 3);
v_semiringInst_874_ = lean_ctor_get(v_s_869_, 4);
v_charInst_x3f_875_ = lean_ctor_get(v_s_869_, 5);
v_addFn_x3f_876_ = lean_ctor_get(v_s_869_, 6);
v_mulFn_x3f_877_ = lean_ctor_get(v_s_869_, 7);
v_subFn_x3f_878_ = lean_ctor_get(v_s_869_, 8);
v_negFn_x3f_879_ = lean_ctor_get(v_s_869_, 9);
v_powFn_x3f_880_ = lean_ctor_get(v_s_869_, 10);
v_natCastFn_x3f_881_ = lean_ctor_get(v_s_869_, 12);
v_one_x3f_882_ = lean_ctor_get(v_s_869_, 13);
v_isSharedCheck_890_ = !lean_is_exclusive(v_s_869_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v_s_869_, 11);
lean_dec(v_unused_891_);
v___x_884_ = v_s_869_;
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_one_x3f_882_);
lean_inc(v_natCastFn_x3f_881_);
lean_inc(v_powFn_x3f_880_);
lean_inc(v_negFn_x3f_879_);
lean_inc(v_subFn_x3f_878_);
lean_inc(v_mulFn_x3f_877_);
lean_inc(v_addFn_x3f_876_);
lean_inc(v_charInst_x3f_875_);
lean_inc(v_semiringInst_874_);
lean_inc(v_ringInst_873_);
lean_inc(v_u_872_);
lean_inc(v_type_871_);
lean_inc(v_id_870_);
lean_dec(v_s_869_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v_intCastFn_868_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 11, v___x_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_id_870_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_type_871_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_u_872_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_ringInst_873_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_semiringInst_874_);
lean_ctor_set(v_reuseFailAlloc_889_, 5, v_charInst_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_889_, 6, v_addFn_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_889_, 7, v_mulFn_x3f_877_);
lean_ctor_set(v_reuseFailAlloc_889_, 8, v_subFn_x3f_878_);
lean_ctor_set(v_reuseFailAlloc_889_, 9, v_negFn_x3f_879_);
lean_ctor_set(v_reuseFailAlloc_889_, 10, v_powFn_x3f_880_);
lean_ctor_set(v_reuseFailAlloc_889_, 11, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_889_, 12, v_natCastFn_x3f_881_);
lean_ctor_set(v_reuseFailAlloc_889_, 13, v_one_x3f_882_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_892_, lean_object* v_intCastFn_893_, lean_object* v_____r_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_apply_2(v_toPure_892_, lean_box(0), v_intCastFn_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_896_, lean_object* v_modifyRing_897_, lean_object* v_toBind_898_, lean_object* v_intCastFn_899_){
_start:
{
lean_object* v___f_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
lean_inc_ref(v_intCastFn_899_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_900_, 0, v_intCastFn_899_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_901_, 0, v_toPure_896_);
lean_closure_set(v___f_901_, 1, v_intCastFn_899_);
v___x_902_ = lean_apply_1(v_modifyRing_897_, v___f_900_);
v___x_903_ = lean_apply_4(v_toBind_898_, lean_box(0), lean_box(0), v___x_902_, v___f_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v___x_906_, lean_object* v_type_907_, lean_object* v_canonExpr_908_, lean_object* v_toBind_909_, lean_object* v___f_910_, lean_object* v_inst_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_912_ = l_Lean_Name_mkStr2(v___x_904_, v___x_905_);
v___x_913_ = l_Lean_mkConst(v___x_912_, v___x_906_);
v___x_914_ = l_Lean_mkAppB(v___x_913_, v_type_907_, v_inst_911_);
v___x_915_ = lean_apply_1(v_canonExpr_908_, v___x_914_);
v___x_916_ = lean_apply_4(v_toBind_909_, lean_box(0), lean_box(0), v___x_915_, v___f_910_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_922_, lean_object* v_inst_x27_923_, lean_object* v_toBind_924_, lean_object* v___f_925_, lean_object* v___f_926_, lean_object* v_inst_927_, lean_object* v_____do__lift_928_){
_start:
{
if (lean_obj_tag(v_____do__lift_928_) == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v_inst_927_);
lean_dec(v___f_926_);
v___x_929_ = lean_apply_2(v_toPure_922_, lean_box(0), v_inst_x27_923_);
v___x_930_ = lean_apply_4(v_toBind_924_, lean_box(0), lean_box(0), v___x_929_, v___f_925_);
return v___x_930_;
}
else
{
lean_object* v_val_931_; lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v___f_925_);
v_val_931_ = lean_ctor_get(v_____do__lift_928_, 0);
lean_inc_n(v_val_931_, 2);
lean_dec_ref_known(v_____do__lift_928_, 1);
lean_inc(v_toBind_924_);
v___f_932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_932_, 0, v_toPure_922_);
lean_closure_set(v___f_932_, 1, v_val_931_);
lean_closure_set(v___f_932_, 2, v_toBind_924_);
lean_closure_set(v___f_932_, 3, v___f_926_);
v___x_933_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_934_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_934_, 0, v___x_933_);
lean_closure_set(v___x_934_, 1, v_val_931_);
lean_closure_set(v___x_934_, 2, v_inst_x27_923_);
v___x_935_ = lean_apply_2(v_inst_927_, lean_box(0), v___x_934_);
v___x_936_ = lean_apply_4(v_toBind_924_, lean_box(0), lean_box(0), v___x_935_, v___f_932_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_946_, lean_object* v_inst_947_, lean_object* v_toBind_948_, lean_object* v___f_949_, lean_object* v_inst_950_, lean_object* v_ring_951_){
_start:
{
lean_object* v_intCastFn_x3f_952_; 
v_intCastFn_x3f_952_ = lean_ctor_get(v_ring_951_, 11);
if (lean_obj_tag(v_intCastFn_x3f_952_) == 1)
{
lean_object* v_val_953_; lean_object* v___x_954_; 
lean_inc_ref(v_intCastFn_x3f_952_);
lean_dec_ref(v_ring_951_);
lean_dec(v_inst_950_);
lean_dec(v___f_949_);
lean_dec(v_toBind_948_);
lean_dec_ref(v_inst_947_);
v_val_953_ = lean_ctor_get(v_intCastFn_x3f_952_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v_intCastFn_x3f_952_, 1);
v___x_954_ = lean_apply_2(v_toPure_946_, lean_box(0), v_val_953_);
return v___x_954_;
}
else
{
lean_object* v_type_955_; lean_object* v_u_956_; lean_object* v_ringInst_957_; lean_object* v_canonExpr_958_; lean_object* v_synthInstance_x3f_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_980_; 
v_type_955_ = lean_ctor_get(v_ring_951_, 1);
lean_inc_ref(v_type_955_);
v_u_956_ = lean_ctor_get(v_ring_951_, 2);
lean_inc(v_u_956_);
v_ringInst_957_ = lean_ctor_get(v_ring_951_, 3);
lean_inc_ref(v_ringInst_957_);
lean_dec_ref(v_ring_951_);
v_canonExpr_958_ = lean_ctor_get(v_inst_947_, 0);
v_synthInstance_x3f_959_ = lean_ctor_get(v_inst_947_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_inst_947_);
if (v_isSharedCheck_980_ == 0)
{
v___x_961_ = v_inst_947_;
v_isShared_962_ = v_isSharedCheck_980_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_synthInstance_x3f_959_);
lean_inc(v_canonExpr_958_);
lean_dec(v_inst_947_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_980_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_963_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_964_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_965_ = lean_box(0);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 1);
lean_ctor_set(v___x_961_, 1, v___x_965_);
lean_ctor_set(v___x_961_, 0, v_u_956_);
v___x_967_ = v___x_961_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_u_956_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_979_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v_inst_x27_969_; lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_instType_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc_ref_n(v___x_967_, 2);
v___x_968_ = l_Lean_mkConst(v___x_964_, v___x_967_);
lean_inc_ref_n(v_type_955_, 2);
v_inst_x27_969_ = l_Lean_mkAppB(v___x_968_, v_type_955_, v_ringInst_957_);
v___x_970_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_948_, 2);
v___f_971_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_971_, 0, v___x_970_);
lean_closure_set(v___f_971_, 1, v___x_963_);
lean_closure_set(v___f_971_, 2, v___x_967_);
lean_closure_set(v___f_971_, 3, v_type_955_);
lean_closure_set(v___f_971_, 4, v_canonExpr_958_);
lean_closure_set(v___f_971_, 5, v_toBind_948_);
lean_closure_set(v___f_971_, 6, v___f_949_);
v___f_972_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_972_, 0, v___f_971_);
lean_inc_ref(v___f_972_);
v___f_973_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_973_, 0, v_toPure_946_);
lean_closure_set(v___f_973_, 1, v_inst_x27_969_);
lean_closure_set(v___f_973_, 2, v_toBind_948_);
lean_closure_set(v___f_973_, 3, v___f_972_);
lean_closure_set(v___f_973_, 4, v___f_972_);
lean_closure_set(v___f_973_, 5, v_inst_950_);
v___x_974_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_975_ = l_Lean_mkConst(v___x_974_, v___x_967_);
v_instType_976_ = l_Lean_Expr_app___override(v___x_975_, v_type_955_);
v___x_977_ = lean_apply_1(v_synthInstance_x3f_959_, v_instType_976_);
v___x_978_ = lean_apply_4(v_toBind_948_, lean_box(0), lean_box(0), v___x_977_, v___f_973_);
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_inst_984_){
_start:
{
lean_object* v_toApplicative_985_; lean_object* v_toBind_986_; lean_object* v_getRing_987_; lean_object* v_modifyRing_988_; lean_object* v_toPure_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___x_992_; 
v_toApplicative_985_ = lean_ctor_get(v_inst_982_, 0);
lean_inc_ref(v_toApplicative_985_);
v_toBind_986_ = lean_ctor_get(v_inst_982_, 1);
lean_inc_n(v_toBind_986_, 3);
lean_dec_ref(v_inst_982_);
v_getRing_987_ = lean_ctor_get(v_inst_984_, 0);
lean_inc(v_getRing_987_);
v_modifyRing_988_ = lean_ctor_get(v_inst_984_, 1);
lean_inc(v_modifyRing_988_);
lean_dec_ref(v_inst_984_);
v_toPure_989_ = lean_ctor_get(v_toApplicative_985_, 1);
lean_inc_n(v_toPure_989_, 2);
lean_dec_ref(v_toApplicative_985_);
v___f_990_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_990_, 0, v_toPure_989_);
lean_closure_set(v___f_990_, 1, v_modifyRing_988_);
lean_closure_set(v___f_990_, 2, v_toBind_986_);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_991_, 0, v_toPure_989_);
lean_closure_set(v___f_991_, 1, v_inst_983_);
lean_closure_set(v___f_991_, 2, v_toBind_986_);
lean_closure_set(v___f_991_, 3, v___f_990_);
lean_closure_set(v___f_991_, 4, v_inst_981_);
v___x_992_ = lean_apply_4(v_toBind_986_, lean_box(0), lean_box(0), v_getRing_987_, v___f_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v_inst_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_994_, v_inst_995_, v_inst_996_, v_inst_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_999_, lean_object* v_s_1000_){
_start:
{
lean_object* v_id_1001_; lean_object* v_type_1002_; lean_object* v_u_1003_; lean_object* v_ringInst_1004_; lean_object* v_semiringInst_1005_; lean_object* v_charInst_x3f_1006_; lean_object* v_addFn_x3f_1007_; lean_object* v_mulFn_x3f_1008_; lean_object* v_subFn_x3f_1009_; lean_object* v_negFn_x3f_1010_; lean_object* v_powFn_x3f_1011_; lean_object* v_intCastFn_x3f_1012_; lean_object* v_one_x3f_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1021_; 
v_id_1001_ = lean_ctor_get(v_s_1000_, 0);
v_type_1002_ = lean_ctor_get(v_s_1000_, 1);
v_u_1003_ = lean_ctor_get(v_s_1000_, 2);
v_ringInst_1004_ = lean_ctor_get(v_s_1000_, 3);
v_semiringInst_1005_ = lean_ctor_get(v_s_1000_, 4);
v_charInst_x3f_1006_ = lean_ctor_get(v_s_1000_, 5);
v_addFn_x3f_1007_ = lean_ctor_get(v_s_1000_, 6);
v_mulFn_x3f_1008_ = lean_ctor_get(v_s_1000_, 7);
v_subFn_x3f_1009_ = lean_ctor_get(v_s_1000_, 8);
v_negFn_x3f_1010_ = lean_ctor_get(v_s_1000_, 9);
v_powFn_x3f_1011_ = lean_ctor_get(v_s_1000_, 10);
v_intCastFn_x3f_1012_ = lean_ctor_get(v_s_1000_, 11);
v_one_x3f_1013_ = lean_ctor_get(v_s_1000_, 13);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_s_1000_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_s_1000_, 12);
lean_dec(v_unused_1022_);
v___x_1015_ = v_s_1000_;
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_one_x3f_1013_);
lean_inc(v_intCastFn_x3f_1012_);
lean_inc(v_powFn_x3f_1011_);
lean_inc(v_negFn_x3f_1010_);
lean_inc(v_subFn_x3f_1009_);
lean_inc(v_mulFn_x3f_1008_);
lean_inc(v_addFn_x3f_1007_);
lean_inc(v_charInst_x3f_1006_);
lean_inc(v_semiringInst_1005_);
lean_inc(v_ringInst_1004_);
lean_inc(v_u_1003_);
lean_inc(v_type_1002_);
lean_inc(v_id_1001_);
lean_dec(v_s_1000_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_natCastFn_999_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 12, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_id_1001_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_type_1002_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_u_1003_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_ringInst_1004_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_semiringInst_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 5, v_charInst_x3f_1006_);
lean_ctor_set(v_reuseFailAlloc_1020_, 6, v_addFn_x3f_1007_);
lean_ctor_set(v_reuseFailAlloc_1020_, 7, v_mulFn_x3f_1008_);
lean_ctor_set(v_reuseFailAlloc_1020_, 8, v_subFn_x3f_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 9, v_negFn_x3f_1010_);
lean_ctor_set(v_reuseFailAlloc_1020_, 10, v_powFn_x3f_1011_);
lean_ctor_set(v_reuseFailAlloc_1020_, 11, v_intCastFn_x3f_1012_);
lean_ctor_set(v_reuseFailAlloc_1020_, 12, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1020_, 13, v_one_x3f_1013_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1023_, lean_object* v_natCastFn_1024_, lean_object* v_____r_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_apply_2(v_toPure_1023_, lean_box(0), v_natCastFn_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1027_, lean_object* v_modifyRing_1028_, lean_object* v_toBind_1029_, lean_object* v_natCastFn_1030_){
_start:
{
lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_inc_ref(v_natCastFn_1030_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1031_, 0, v_natCastFn_1030_);
v___f_1032_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1032_, 0, v_toPure_1027_);
lean_closure_set(v___f_1032_, 1, v_natCastFn_1030_);
v___x_1033_ = lean_apply_1(v_modifyRing_1028_, v___f_1031_);
v___x_1034_ = lean_apply_4(v_toBind_1029_, lean_box(0), lean_box(0), v___x_1033_, v___f_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_toBind_1039_, lean_object* v___f_1040_, lean_object* v_ring_1041_){
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
lean_dec_ref_known(v_natCastFn_x3f_1042_, 1);
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
v___x_1048_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1036_, v_inst_1037_, v_inst_1038_, v_u_1046_, v_type_1045_, v_semiringInst_1047_);
v___x_1049_ = lean_apply_4(v_toBind_1039_, lean_box(0), lean_box(0), v___x_1048_, v___f_1040_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_){
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
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1059_, 0, v_toPure_1058_);
lean_closure_set(v___f_1059_, 1, v_modifyRing_1057_);
lean_closure_set(v___f_1059_, 2, v_toBind_1055_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1068_, lean_object* v_s_1069_){
_start:
{
lean_object* v_toRing_1070_; lean_object* v_semiringId_x3f_1071_; lean_object* v_commSemiringInst_1072_; lean_object* v_commRingInst_1073_; lean_object* v_noZeroDivInst_x3f_1074_; lean_object* v_fieldInst_x3f_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_toRing_1070_ = lean_ctor_get(v_s_1069_, 0);
v_semiringId_x3f_1071_ = lean_ctor_get(v_s_1069_, 2);
v_commSemiringInst_1072_ = lean_ctor_get(v_s_1069_, 3);
v_commRingInst_1073_ = lean_ctor_get(v_s_1069_, 4);
v_noZeroDivInst_x3f_1074_ = lean_ctor_get(v_s_1069_, 5);
v_fieldInst_x3f_1075_ = lean_ctor_get(v_s_1069_, 6);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_s_1069_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_s_1069_, 1);
lean_dec(v_unused_1084_);
v___x_1077_ = v_s_1069_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_fieldInst_x3f_1075_);
lean_inc(v_noZeroDivInst_x3f_1074_);
lean_inc(v_commRingInst_1073_);
lean_inc(v_commSemiringInst_1072_);
lean_inc(v_semiringId_x3f_1071_);
lean_inc(v_toRing_1070_);
lean_dec(v_s_1069_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_invFn_1068_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_toRing_1070_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_semiringId_x3f_1071_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_commSemiringInst_1072_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_commRingInst_1073_);
lean_ctor_set(v_reuseFailAlloc_1082_, 5, v_noZeroDivInst_x3f_1074_);
lean_ctor_set(v_reuseFailAlloc_1082_, 6, v_fieldInst_x3f_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1085_, lean_object* v_invFn_1086_, lean_object* v_____r_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_apply_2(v_toPure_1085_, lean_box(0), v_invFn_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1089_, lean_object* v_modifyCommRing_1090_, lean_object* v_toBind_1091_, lean_object* v_invFn_1092_){
_start:
{
lean_object* v___f_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_inc_ref(v_invFn_1092_);
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1093_, 0, v_invFn_1092_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1094_, 0, v_toPure_1089_);
lean_closure_set(v___f_1094_, 1, v_invFn_1092_);
v___x_1095_ = lean_apply_1(v_modifyCommRing_1090_, v___f_1093_);
v___x_1096_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v___x_1095_, v___f_1094_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_toBind_1119_, lean_object* v___f_1120_, lean_object* v_ring_1121_){
_start:
{
lean_object* v_fieldInst_x3f_1122_; 
v_fieldInst_x3f_1122_ = lean_ctor_get(v_ring_1121_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1122_) == 1)
{
lean_object* v_invFn_x3f_1123_; 
lean_inc_ref(v_fieldInst_x3f_1122_);
v_invFn_x3f_1123_ = lean_ctor_get(v_ring_1121_, 1);
if (lean_obj_tag(v_invFn_x3f_1123_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1125_; 
lean_inc_ref(v_invFn_x3f_1123_);
lean_dec_ref_known(v_fieldInst_x3f_1122_, 1);
lean_dec_ref(v_ring_1121_);
lean_dec(v___f_1120_);
lean_dec(v_toBind_1119_);
lean_dec_ref(v_inst_1118_);
lean_dec_ref(v_inst_1117_);
lean_dec_ref(v_inst_1116_);
lean_dec(v_inst_1115_);
v_val_1124_ = lean_ctor_get(v_invFn_x3f_1123_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v_invFn_x3f_1123_, 1);
v___x_1125_ = lean_apply_2(v_toPure_1114_, lean_box(0), v_val_1124_);
return v___x_1125_;
}
else
{
lean_object* v_toRing_1126_; lean_object* v_val_1127_; lean_object* v_type_1128_; lean_object* v_u_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_expectedInst_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec(v_toPure_1114_);
v_toRing_1126_ = lean_ctor_get(v_ring_1121_, 0);
lean_inc_ref(v_toRing_1126_);
lean_dec_ref(v_ring_1121_);
v_val_1127_ = lean_ctor_get(v_fieldInst_x3f_1122_, 0);
lean_inc(v_val_1127_);
lean_dec_ref_known(v_fieldInst_x3f_1122_, 1);
v_type_1128_ = lean_ctor_get(v_toRing_1126_, 1);
lean_inc_ref_n(v_type_1128_, 2);
v_u_1129_ = lean_ctor_get(v_toRing_1126_, 2);
lean_inc_n(v_u_1129_, 2);
lean_dec_ref(v_toRing_1126_);
v___x_1130_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_u_1129_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_mkConst(v___x_1130_, v___x_1132_);
v_expectedInst_1134_ = l_Lean_mkAppB(v___x_1133_, v_type_1128_, v_val_1127_);
v___x_1135_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1136_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1137_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1115_, v_inst_1116_, v_inst_1117_, v_inst_1118_, v_type_1128_, v_u_1129_, v___x_1135_, v___x_1136_, v_expectedInst_1134_);
v___x_1138_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1137_, v___f_1120_);
return v___x_1138_;
}
}
else
{
lean_object* v_toRing_1139_; lean_object* v_type_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v___f_1120_);
lean_dec(v_toBind_1119_);
lean_dec_ref(v_inst_1118_);
lean_dec(v_inst_1115_);
lean_dec(v_toPure_1114_);
v_toRing_1139_ = lean_ctor_get(v_ring_1121_, 0);
lean_inc_ref(v_toRing_1139_);
lean_dec_ref(v_ring_1121_);
v_type_1140_ = lean_ctor_get(v_toRing_1139_, 1);
lean_inc_ref(v_type_1140_);
lean_dec_ref(v_toRing_1139_);
v___x_1141_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1142_ = l_Lean_indentExpr(v_type_1140_);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_throwError___redArg(v_inst_1117_, v_inst_1116_, v___x_1143_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_){
_start:
{
lean_object* v_toApplicative_1150_; lean_object* v_toBind_1151_; lean_object* v_getCommRing_1152_; lean_object* v_modifyCommRing_1153_; lean_object* v_toPure_1154_; lean_object* v___f_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; 
v_toApplicative_1150_ = lean_ctor_get(v_inst_1147_, 0);
v_toBind_1151_ = lean_ctor_get(v_inst_1147_, 1);
lean_inc_n(v_toBind_1151_, 3);
v_getCommRing_1152_ = lean_ctor_get(v_inst_1149_, 0);
lean_inc(v_getCommRing_1152_);
v_modifyCommRing_1153_ = lean_ctor_get(v_inst_1149_, 1);
lean_inc(v_modifyCommRing_1153_);
lean_dec_ref(v_inst_1149_);
v_toPure_1154_ = lean_ctor_get(v_toApplicative_1150_, 1);
lean_inc_n(v_toPure_1154_, 2);
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1155_, 0, v_toPure_1154_);
lean_closure_set(v___f_1155_, 1, v_modifyCommRing_1153_);
lean_closure_set(v___f_1155_, 2, v_toBind_1151_);
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1156_, 0, v_toPure_1154_);
lean_closure_set(v___f_1156_, 1, v_inst_1145_);
lean_closure_set(v___f_1156_, 2, v_inst_1146_);
lean_closure_set(v___f_1156_, 3, v_inst_1147_);
lean_closure_set(v___f_1156_, 4, v_inst_1148_);
lean_closure_set(v___f_1156_, 5, v_toBind_1151_);
lean_closure_set(v___f_1156_, 6, v___f_1155_);
v___x_1157_ = lean_apply_4(v_toBind_1151_, lean_box(0), lean_box(0), v_getCommRing_1152_, v___f_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1159_, v_inst_1160_, v_inst_1161_, v_inst_1162_, v_inst_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_1165_, lean_object* v_s_1166_){
_start:
{
lean_object* v_id_1167_; lean_object* v_type_1168_; lean_object* v_u_1169_; lean_object* v_semiringInst_1170_; lean_object* v_mulFn_x3f_1171_; lean_object* v_powFn_x3f_1172_; lean_object* v_natCastFn_x3f_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
v_id_1167_ = lean_ctor_get(v_s_1166_, 0);
v_type_1168_ = lean_ctor_get(v_s_1166_, 1);
v_u_1169_ = lean_ctor_get(v_s_1166_, 2);
v_semiringInst_1170_ = lean_ctor_get(v_s_1166_, 3);
v_mulFn_x3f_1171_ = lean_ctor_get(v_s_1166_, 5);
v_powFn_x3f_1172_ = lean_ctor_get(v_s_1166_, 6);
v_natCastFn_x3f_1173_ = lean_ctor_get(v_s_1166_, 7);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_s_1166_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v_s_1166_, 4);
lean_dec(v_unused_1182_);
v___x_1175_ = v_s_1166_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_natCastFn_x3f_1173_);
lean_inc(v_powFn_x3f_1172_);
lean_inc(v_mulFn_x3f_1171_);
lean_inc(v_semiringInst_1170_);
lean_inc(v_u_1169_);
lean_inc(v_type_1168_);
lean_inc(v_id_1167_);
lean_dec(v_s_1166_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_addFn_1165_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 4, v___x_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_id_1167_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_type_1168_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_u_1169_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_semiringInst_1170_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1180_, 5, v_mulFn_x3f_1171_);
lean_ctor_set(v_reuseFailAlloc_1180_, 6, v_powFn_x3f_1172_);
lean_ctor_set(v_reuseFailAlloc_1180_, 7, v_natCastFn_x3f_1173_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_1183_, lean_object* v_modifySemiring_1184_, lean_object* v_toBind_1185_, lean_object* v_addFn_1186_){
_start:
{
lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_inc_ref(v_addFn_1186_);
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1187_, 0, v_addFn_1186_);
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1188_, 0, v_toPure_1183_);
lean_closure_set(v___f_1188_, 1, v_addFn_1186_);
v___x_1189_ = lean_apply_1(v_modifySemiring_1184_, v___f_1187_);
v___x_1190_ = lean_apply_4(v_toBind_1185_, lean_box(0), lean_box(0), v___x_1189_, v___f_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_toBind_1196_, lean_object* v___f_1197_, lean_object* v_sr_1198_){
_start:
{
lean_object* v_addFn_x3f_1199_; 
v_addFn_x3f_1199_ = lean_ctor_get(v_sr_1198_, 4);
if (lean_obj_tag(v_addFn_x3f_1199_) == 1)
{
lean_object* v_val_1200_; lean_object* v___x_1201_; 
lean_inc_ref(v_addFn_x3f_1199_);
lean_dec_ref(v_sr_1198_);
lean_dec(v___f_1197_);
lean_dec(v_toBind_1196_);
lean_dec_ref(v_inst_1195_);
lean_dec_ref(v_inst_1194_);
lean_dec_ref(v_inst_1193_);
lean_dec(v_inst_1192_);
v_val_1200_ = lean_ctor_get(v_addFn_x3f_1199_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v_addFn_x3f_1199_, 1);
v___x_1201_ = lean_apply_2(v_toPure_1191_, lean_box(0), v_val_1200_);
return v___x_1201_;
}
else
{
lean_object* v_type_1202_; lean_object* v_u_1203_; lean_object* v_semiringInst_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_expectedInst_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec(v_toPure_1191_);
v_type_1202_ = lean_ctor_get(v_sr_1198_, 1);
lean_inc_ref_n(v_type_1202_, 3);
v_u_1203_ = lean_ctor_get(v_sr_1198_, 2);
lean_inc_n(v_u_1203_, 2);
v_semiringInst_1204_ = lean_ctor_get(v_sr_1198_, 3);
lean_inc_ref(v_semiringInst_1204_);
lean_dec_ref(v_sr_1198_);
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_u_1203_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
lean_inc_ref(v___x_1207_);
v___x_1208_ = l_Lean_mkConst(v___x_1205_, v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1210_ = l_Lean_mkConst(v___x_1209_, v___x_1207_);
v___x_1211_ = l_Lean_mkAppB(v___x_1210_, v_type_1202_, v_semiringInst_1204_);
v_expectedInst_1212_ = l_Lean_mkAppB(v___x_1208_, v_type_1202_, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1214_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1215_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1192_, v_inst_1193_, v_inst_1194_, v_inst_1195_, v_type_1202_, v_u_1203_, v___x_1213_, v___x_1214_, v_expectedInst_1212_);
v___x_1216_ = lean_apply_4(v_toBind_1196_, lean_box(0), lean_box(0), v___x_1215_, v___f_1197_);
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v_toApplicative_1222_; lean_object* v_toBind_1223_; lean_object* v_getSemiring_1224_; lean_object* v_modifySemiring_1225_; lean_object* v_toPure_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; 
v_toApplicative_1222_ = lean_ctor_get(v_inst_1219_, 0);
v_toBind_1223_ = lean_ctor_get(v_inst_1219_, 1);
lean_inc_n(v_toBind_1223_, 3);
v_getSemiring_1224_ = lean_ctor_get(v_inst_1221_, 0);
lean_inc(v_getSemiring_1224_);
v_modifySemiring_1225_ = lean_ctor_get(v_inst_1221_, 1);
lean_inc(v_modifySemiring_1225_);
lean_dec_ref(v_inst_1221_);
v_toPure_1226_ = lean_ctor_get(v_toApplicative_1222_, 1);
lean_inc_n(v_toPure_1226_, 2);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1227_, 0, v_toPure_1226_);
lean_closure_set(v___f_1227_, 1, v_modifySemiring_1225_);
lean_closure_set(v___f_1227_, 2, v_toBind_1223_);
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1228_, 0, v_toPure_1226_);
lean_closure_set(v___f_1228_, 1, v_inst_1217_);
lean_closure_set(v___f_1228_, 2, v_inst_1218_);
lean_closure_set(v___f_1228_, 3, v_inst_1219_);
lean_closure_set(v___f_1228_, 4, v_inst_1220_);
lean_closure_set(v___f_1228_, 5, v_toBind_1223_);
lean_closure_set(v___f_1228_, 6, v___f_1227_);
v___x_1229_ = lean_apply_4(v_toBind_1223_, lean_box(0), lean_box(0), v_getSemiring_1224_, v___f_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1231_, v_inst_1232_, v_inst_1233_, v_inst_1234_, v_inst_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_1237_, lean_object* v_s_1238_){
_start:
{
lean_object* v_id_1239_; lean_object* v_type_1240_; lean_object* v_u_1241_; lean_object* v_semiringInst_1242_; lean_object* v_addFn_x3f_1243_; lean_object* v_powFn_x3f_1244_; lean_object* v_natCastFn_x3f_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1253_; 
v_id_1239_ = lean_ctor_get(v_s_1238_, 0);
v_type_1240_ = lean_ctor_get(v_s_1238_, 1);
v_u_1241_ = lean_ctor_get(v_s_1238_, 2);
v_semiringInst_1242_ = lean_ctor_get(v_s_1238_, 3);
v_addFn_x3f_1243_ = lean_ctor_get(v_s_1238_, 4);
v_powFn_x3f_1244_ = lean_ctor_get(v_s_1238_, 6);
v_natCastFn_x3f_1245_ = lean_ctor_get(v_s_1238_, 7);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_s_1238_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v_s_1238_, 5);
lean_dec(v_unused_1254_);
v___x_1247_ = v_s_1238_;
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_natCastFn_x3f_1245_);
lean_inc(v_powFn_x3f_1244_);
lean_inc(v_addFn_x3f_1243_);
lean_inc(v_semiringInst_1242_);
lean_inc(v_u_1241_);
lean_inc(v_type_1240_);
lean_inc(v_id_1239_);
lean_dec(v_s_1238_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_mulFn_1237_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 5, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_id_1239_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_type_1240_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_u_1241_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_semiringInst_1242_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_addFn_x3f_1243_);
lean_ctor_set(v_reuseFailAlloc_1252_, 5, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1252_, 6, v_powFn_x3f_1244_);
lean_ctor_set(v_reuseFailAlloc_1252_, 7, v_natCastFn_x3f_1245_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1255_, lean_object* v_modifySemiring_1256_, lean_object* v_toBind_1257_, lean_object* v_mulFn_1258_){
_start:
{
lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_inc_ref(v_mulFn_1258_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1259_, 0, v_mulFn_1258_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1260_, 0, v_toPure_1255_);
lean_closure_set(v___f_1260_, 1, v_mulFn_1258_);
v___x_1261_ = lean_apply_1(v_modifySemiring_1256_, v___f_1259_);
v___x_1262_ = lean_apply_4(v_toBind_1257_, lean_box(0), lean_box(0), v___x_1261_, v___f_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_toBind_1268_, lean_object* v___f_1269_, lean_object* v_sr_1270_){
_start:
{
lean_object* v_mulFn_x3f_1271_; 
v_mulFn_x3f_1271_ = lean_ctor_get(v_sr_1270_, 5);
if (lean_obj_tag(v_mulFn_x3f_1271_) == 1)
{
lean_object* v_val_1272_; lean_object* v___x_1273_; 
lean_inc_ref(v_mulFn_x3f_1271_);
lean_dec_ref(v_sr_1270_);
lean_dec(v___f_1269_);
lean_dec(v_toBind_1268_);
lean_dec_ref(v_inst_1267_);
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
lean_dec(v_inst_1264_);
v_val_1272_ = lean_ctor_get(v_mulFn_x3f_1271_, 0);
lean_inc(v_val_1272_);
lean_dec_ref_known(v_mulFn_x3f_1271_, 1);
v___x_1273_ = lean_apply_2(v_toPure_1263_, lean_box(0), v_val_1272_);
return v___x_1273_;
}
else
{
lean_object* v_type_1274_; lean_object* v_u_1275_; lean_object* v_semiringInst_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_expectedInst_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec(v_toPure_1263_);
v_type_1274_ = lean_ctor_get(v_sr_1270_, 1);
lean_inc_ref_n(v_type_1274_, 3);
v_u_1275_ = lean_ctor_get(v_sr_1270_, 2);
lean_inc_n(v_u_1275_, 2);
v_semiringInst_1276_ = lean_ctor_get(v_sr_1270_, 3);
lean_inc_ref(v_semiringInst_1276_);
lean_dec_ref(v_sr_1270_);
v___x_1277_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_u_1275_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
lean_inc_ref(v___x_1279_);
v___x_1280_ = l_Lean_mkConst(v___x_1277_, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1282_ = l_Lean_mkConst(v___x_1281_, v___x_1279_);
v___x_1283_ = l_Lean_mkAppB(v___x_1282_, v_type_1274_, v_semiringInst_1276_);
v_expectedInst_1284_ = l_Lean_mkAppB(v___x_1280_, v_type_1274_, v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1286_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1287_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1264_, v_inst_1265_, v_inst_1266_, v_inst_1267_, v_type_1274_, v_u_1275_, v___x_1285_, v___x_1286_, v_expectedInst_1284_);
v___x_1288_ = lean_apply_4(v_toBind_1268_, lean_box(0), lean_box(0), v___x_1287_, v___f_1269_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_){
_start:
{
lean_object* v_toApplicative_1294_; lean_object* v_toBind_1295_; lean_object* v_getSemiring_1296_; lean_object* v_modifySemiring_1297_; lean_object* v_toPure_1298_; lean_object* v___f_1299_; lean_object* v___f_1300_; lean_object* v___x_1301_; 
v_toApplicative_1294_ = lean_ctor_get(v_inst_1291_, 0);
v_toBind_1295_ = lean_ctor_get(v_inst_1291_, 1);
lean_inc_n(v_toBind_1295_, 3);
v_getSemiring_1296_ = lean_ctor_get(v_inst_1293_, 0);
lean_inc(v_getSemiring_1296_);
v_modifySemiring_1297_ = lean_ctor_get(v_inst_1293_, 1);
lean_inc(v_modifySemiring_1297_);
lean_dec_ref(v_inst_1293_);
v_toPure_1298_ = lean_ctor_get(v_toApplicative_1294_, 1);
lean_inc_n(v_toPure_1298_, 2);
v___f_1299_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1299_, 0, v_toPure_1298_);
lean_closure_set(v___f_1299_, 1, v_modifySemiring_1297_);
lean_closure_set(v___f_1299_, 2, v_toBind_1295_);
v___f_1300_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1300_, 0, v_toPure_1298_);
lean_closure_set(v___f_1300_, 1, v_inst_1289_);
lean_closure_set(v___f_1300_, 2, v_inst_1290_);
lean_closure_set(v___f_1300_, 3, v_inst_1291_);
lean_closure_set(v___f_1300_, 4, v_inst_1292_);
lean_closure_set(v___f_1300_, 5, v_toBind_1295_);
lean_closure_set(v___f_1300_, 6, v___f_1299_);
v___x_1301_ = lean_apply_4(v_toBind_1295_, lean_box(0), lean_box(0), v_getSemiring_1296_, v___f_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1303_, v_inst_1304_, v_inst_1305_, v_inst_1306_, v_inst_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1309_, lean_object* v_s_1310_){
_start:
{
lean_object* v_id_1311_; lean_object* v_type_1312_; lean_object* v_u_1313_; lean_object* v_semiringInst_1314_; lean_object* v_addFn_x3f_1315_; lean_object* v_mulFn_x3f_1316_; lean_object* v_natCastFn_x3f_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
v_id_1311_ = lean_ctor_get(v_s_1310_, 0);
v_type_1312_ = lean_ctor_get(v_s_1310_, 1);
v_u_1313_ = lean_ctor_get(v_s_1310_, 2);
v_semiringInst_1314_ = lean_ctor_get(v_s_1310_, 3);
v_addFn_x3f_1315_ = lean_ctor_get(v_s_1310_, 4);
v_mulFn_x3f_1316_ = lean_ctor_get(v_s_1310_, 5);
v_natCastFn_x3f_1317_ = lean_ctor_get(v_s_1310_, 7);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_s_1310_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v_s_1310_, 6);
lean_dec(v_unused_1326_);
v___x_1319_ = v_s_1310_;
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_natCastFn_x3f_1317_);
lean_inc(v_mulFn_x3f_1316_);
lean_inc(v_addFn_x3f_1315_);
lean_inc(v_semiringInst_1314_);
lean_inc(v_u_1313_);
lean_inc(v_type_1312_);
lean_inc(v_id_1311_);
lean_dec(v_s_1310_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_powFn_1309_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 6, v___x_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_id_1311_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_type_1312_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_u_1313_);
lean_ctor_set(v_reuseFailAlloc_1324_, 3, v_semiringInst_1314_);
lean_ctor_set(v_reuseFailAlloc_1324_, 4, v_addFn_x3f_1315_);
lean_ctor_set(v_reuseFailAlloc_1324_, 5, v_mulFn_x3f_1316_);
lean_ctor_set(v_reuseFailAlloc_1324_, 6, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1324_, 7, v_natCastFn_x3f_1317_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1327_, lean_object* v_modifySemiring_1328_, lean_object* v_toBind_1329_, lean_object* v_powFn_1330_){
_start:
{
lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_inc_ref(v_powFn_1330_);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1331_, 0, v_powFn_1330_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1332_, 0, v_toPure_1327_);
lean_closure_set(v___f_1332_, 1, v_powFn_1330_);
v___x_1333_ = lean_apply_1(v_modifySemiring_1328_, v___f_1331_);
v___x_1334_ = lean_apply_4(v_toBind_1329_, lean_box(0), lean_box(0), v___x_1333_, v___f_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_toBind_1340_, lean_object* v___f_1341_, lean_object* v_sr_1342_){
_start:
{
lean_object* v_powFn_x3f_1343_; 
v_powFn_x3f_1343_ = lean_ctor_get(v_sr_1342_, 6);
if (lean_obj_tag(v_powFn_x3f_1343_) == 1)
{
lean_object* v_val_1344_; lean_object* v___x_1345_; 
lean_inc_ref(v_powFn_x3f_1343_);
lean_dec_ref(v_sr_1342_);
lean_dec(v___f_1341_);
lean_dec(v_toBind_1340_);
lean_dec_ref(v_inst_1339_);
lean_dec_ref(v_inst_1338_);
lean_dec_ref(v_inst_1337_);
lean_dec(v_inst_1336_);
v_val_1344_ = lean_ctor_get(v_powFn_x3f_1343_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v_powFn_x3f_1343_, 1);
v___x_1345_ = lean_apply_2(v_toPure_1335_, lean_box(0), v_val_1344_);
return v___x_1345_;
}
else
{
lean_object* v_type_1346_; lean_object* v_u_1347_; lean_object* v_semiringInst_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_toPure_1335_);
v_type_1346_ = lean_ctor_get(v_sr_1342_, 1);
lean_inc_ref(v_type_1346_);
v_u_1347_ = lean_ctor_get(v_sr_1342_, 2);
lean_inc(v_u_1347_);
v_semiringInst_1348_ = lean_ctor_get(v_sr_1342_, 3);
lean_inc_ref(v_semiringInst_1348_);
lean_dec_ref(v_sr_1342_);
v___x_1349_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_u_1347_, v_type_1346_, v_semiringInst_1348_);
v___x_1350_ = lean_apply_4(v_toBind_1340_, lean_box(0), lean_box(0), v___x_1349_, v___f_1341_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_){
_start:
{
lean_object* v_toApplicative_1356_; lean_object* v_toBind_1357_; lean_object* v_getSemiring_1358_; lean_object* v_modifySemiring_1359_; lean_object* v_toPure_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; 
v_toApplicative_1356_ = lean_ctor_get(v_inst_1353_, 0);
v_toBind_1357_ = lean_ctor_get(v_inst_1353_, 1);
lean_inc_n(v_toBind_1357_, 3);
v_getSemiring_1358_ = lean_ctor_get(v_inst_1355_, 0);
lean_inc(v_getSemiring_1358_);
v_modifySemiring_1359_ = lean_ctor_get(v_inst_1355_, 1);
lean_inc(v_modifySemiring_1359_);
lean_dec_ref(v_inst_1355_);
v_toPure_1360_ = lean_ctor_get(v_toApplicative_1356_, 1);
lean_inc_n(v_toPure_1360_, 2);
v___f_1361_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1361_, 0, v_toPure_1360_);
lean_closure_set(v___f_1361_, 1, v_modifySemiring_1359_);
lean_closure_set(v___f_1361_, 2, v_toBind_1357_);
v___f_1362_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1362_, 0, v_toPure_1360_);
lean_closure_set(v___f_1362_, 1, v_inst_1351_);
lean_closure_set(v___f_1362_, 2, v_inst_1352_);
lean_closure_set(v___f_1362_, 3, v_inst_1353_);
lean_closure_set(v___f_1362_, 4, v_inst_1354_);
lean_closure_set(v___f_1362_, 5, v_toBind_1357_);
lean_closure_set(v___f_1362_, 6, v___f_1361_);
v___x_1363_ = lean_apply_4(v_toBind_1357_, lean_box(0), lean_box(0), v_getSemiring_1358_, v___f_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1365_, v_inst_1366_, v_inst_1367_, v_inst_1368_, v_inst_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1371_, lean_object* v_s_1372_){
_start:
{
lean_object* v_id_1373_; lean_object* v_type_1374_; lean_object* v_u_1375_; lean_object* v_semiringInst_1376_; lean_object* v_addFn_x3f_1377_; lean_object* v_mulFn_x3f_1378_; lean_object* v_powFn_x3f_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1387_; 
v_id_1373_ = lean_ctor_get(v_s_1372_, 0);
v_type_1374_ = lean_ctor_get(v_s_1372_, 1);
v_u_1375_ = lean_ctor_get(v_s_1372_, 2);
v_semiringInst_1376_ = lean_ctor_get(v_s_1372_, 3);
v_addFn_x3f_1377_ = lean_ctor_get(v_s_1372_, 4);
v_mulFn_x3f_1378_ = lean_ctor_get(v_s_1372_, 5);
v_powFn_x3f_1379_ = lean_ctor_get(v_s_1372_, 6);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_s_1372_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v_s_1372_, 7);
lean_dec(v_unused_1388_);
v___x_1381_ = v_s_1372_;
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_powFn_x3f_1379_);
lean_inc(v_mulFn_x3f_1378_);
lean_inc(v_addFn_x3f_1377_);
lean_inc(v_semiringInst_1376_);
lean_inc(v_u_1375_);
lean_inc(v_type_1374_);
lean_inc(v_id_1373_);
lean_dec(v_s_1372_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_natCastFn_1371_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 7, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_id_1373_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_type_1374_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_u_1375_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_semiringInst_1376_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_addFn_x3f_1377_);
lean_ctor_set(v_reuseFailAlloc_1386_, 5, v_mulFn_x3f_1378_);
lean_ctor_set(v_reuseFailAlloc_1386_, 6, v_powFn_x3f_1379_);
lean_ctor_set(v_reuseFailAlloc_1386_, 7, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1389_, lean_object* v_modifySemiring_1390_, lean_object* v_toBind_1391_, lean_object* v_natCastFn_1392_){
_start:
{
lean_object* v___f_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_inc_ref(v_natCastFn_1392_);
v___f_1393_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1393_, 0, v_natCastFn_1392_);
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1394_, 0, v_toPure_1389_);
lean_closure_set(v___f_1394_, 1, v_natCastFn_1392_);
v___x_1395_ = lean_apply_1(v_modifySemiring_1390_, v___f_1393_);
v___x_1396_ = lean_apply_4(v_toBind_1391_, lean_box(0), lean_box(0), v___x_1395_, v___f_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_toBind_1401_, lean_object* v___f_1402_, lean_object* v_sr_1403_){
_start:
{
lean_object* v_natCastFn_x3f_1404_; 
v_natCastFn_x3f_1404_ = lean_ctor_get(v_sr_1403_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1404_) == 1)
{
lean_object* v_val_1405_; lean_object* v___x_1406_; 
lean_inc_ref(v_natCastFn_x3f_1404_);
lean_dec_ref(v_sr_1403_);
lean_dec(v___f_1402_);
lean_dec(v_toBind_1401_);
lean_dec_ref(v_inst_1400_);
lean_dec_ref(v_inst_1399_);
lean_dec(v_inst_1398_);
v_val_1405_ = lean_ctor_get(v_natCastFn_x3f_1404_, 0);
lean_inc(v_val_1405_);
lean_dec_ref_known(v_natCastFn_x3f_1404_, 1);
v___x_1406_ = lean_apply_2(v_toPure_1397_, lean_box(0), v_val_1405_);
return v___x_1406_;
}
else
{
lean_object* v_type_1407_; lean_object* v_u_1408_; lean_object* v_semiringInst_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec(v_toPure_1397_);
v_type_1407_ = lean_ctor_get(v_sr_1403_, 1);
lean_inc_ref(v_type_1407_);
v_u_1408_ = lean_ctor_get(v_sr_1403_, 2);
lean_inc(v_u_1408_);
v_semiringInst_1409_ = lean_ctor_get(v_sr_1403_, 3);
lean_inc_ref(v_semiringInst_1409_);
lean_dec_ref(v_sr_1403_);
v___x_1410_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1398_, v_inst_1399_, v_inst_1400_, v_u_1408_, v_type_1407_, v_semiringInst_1409_);
v___x_1411_ = lean_apply_4(v_toBind_1401_, lean_box(0), lean_box(0), v___x_1410_, v___f_1402_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_){
_start:
{
lean_object* v_toApplicative_1416_; lean_object* v_toBind_1417_; lean_object* v_getSemiring_1418_; lean_object* v_modifySemiring_1419_; lean_object* v_toPure_1420_; lean_object* v___f_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; 
v_toApplicative_1416_ = lean_ctor_get(v_inst_1413_, 0);
v_toBind_1417_ = lean_ctor_get(v_inst_1413_, 1);
lean_inc_n(v_toBind_1417_, 3);
v_getSemiring_1418_ = lean_ctor_get(v_inst_1415_, 0);
lean_inc(v_getSemiring_1418_);
v_modifySemiring_1419_ = lean_ctor_get(v_inst_1415_, 1);
lean_inc(v_modifySemiring_1419_);
lean_dec_ref(v_inst_1415_);
v_toPure_1420_ = lean_ctor_get(v_toApplicative_1416_, 1);
lean_inc_n(v_toPure_1420_, 2);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1421_, 0, v_toPure_1420_);
lean_closure_set(v___f_1421_, 1, v_modifySemiring_1419_);
lean_closure_set(v___f_1421_, 2, v_toBind_1417_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1422_, 0, v_toPure_1420_);
lean_closure_set(v___f_1422_, 1, v_inst_1412_);
lean_closure_set(v___f_1422_, 2, v_inst_1413_);
lean_closure_set(v___f_1422_, 3, v_inst_1414_);
lean_closure_set(v___f_1422_, 4, v_toBind_1417_);
lean_closure_set(v___f_1422_, 5, v___f_1421_);
v___x_1423_ = lean_apply_4(v_toBind_1417_, lean_box(0), lean_box(0), v_getSemiring_1418_, v___f_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_inst_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1425_, v_inst_1426_, v_inst_1427_, v_inst_1428_);
return v___x_1429_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Functions(builtin);
}
#ifdef __cplusplus
}
#endif
