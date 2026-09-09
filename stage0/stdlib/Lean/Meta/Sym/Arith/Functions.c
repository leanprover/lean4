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
v_options_12_ = lean_ctor_get(v___y_4_, 1);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 4);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object* v_declName_59_, lean_object* v_inst_60_, lean_object* v_inst_x27_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___y_68_; lean_object* v___x_101_; uint8_t v_transparency_102_; uint8_t v___x_103_; uint8_t v___x_104_; 
v___x_101_ = l_Lean_Meta_Context_config(v_a_62_);
v_transparency_102_ = lean_ctor_get_uint8(v___x_101_, 9);
lean_dec_ref(v___x_101_);
v___x_103_ = 3;
v___x_104_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v_keyedConfig_105_; uint8_t v_trackZetaDelta_106_; lean_object* v_zetaDeltaSet_107_; lean_object* v_lctx_108_; lean_object* v_localInstances_109_; lean_object* v_defEqCtx_x3f_110_; lean_object* v_synthPendingDepth_111_; lean_object* v_customCanUnfoldPredicate_x3f_112_; uint8_t v_univApprox_113_; uint8_t v_inTypeClassResolution_114_; uint8_t v_cacheInferType_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_keyedConfig_105_ = lean_ctor_get(v_a_62_, 0);
v_trackZetaDelta_106_ = lean_ctor_get_uint8(v_a_62_, sizeof(void*)*7);
v_zetaDeltaSet_107_ = lean_ctor_get(v_a_62_, 1);
v_lctx_108_ = lean_ctor_get(v_a_62_, 2);
v_localInstances_109_ = lean_ctor_get(v_a_62_, 3);
v_defEqCtx_x3f_110_ = lean_ctor_get(v_a_62_, 4);
v_synthPendingDepth_111_ = lean_ctor_get(v_a_62_, 5);
v_customCanUnfoldPredicate_x3f_112_ = lean_ctor_get(v_a_62_, 6);
v_univApprox_113_ = lean_ctor_get_uint8(v_a_62_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_114_ = lean_ctor_get_uint8(v_a_62_, sizeof(void*)*7 + 2);
v_cacheInferType_115_ = lean_ctor_get_uint8(v_a_62_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_105_);
v___x_116_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_103_, v_keyedConfig_105_);
lean_inc(v_customCanUnfoldPredicate_x3f_112_);
lean_inc(v_synthPendingDepth_111_);
lean_inc(v_defEqCtx_x3f_110_);
lean_inc_ref(v_localInstances_109_);
lean_inc_ref(v_lctx_108_);
lean_inc(v_zetaDeltaSet_107_);
v___x_117_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_zetaDeltaSet_107_);
lean_ctor_set(v___x_117_, 2, v_lctx_108_);
lean_ctor_set(v___x_117_, 3, v_localInstances_109_);
lean_ctor_set(v___x_117_, 4, v_defEqCtx_x3f_110_);
lean_ctor_set(v___x_117_, 5, v_synthPendingDepth_111_);
lean_ctor_set(v___x_117_, 6, v_customCanUnfoldPredicate_x3f_112_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*7, v_trackZetaDelta_106_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*7 + 1, v_univApprox_113_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*7 + 2, v_inTypeClassResolution_114_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*7 + 3, v_cacheInferType_115_);
lean_inc_ref(v_inst_x27_61_);
lean_inc_ref(v_inst_60_);
v___x_118_ = l_Lean_Meta_isExprDefEq(v_inst_60_, v_inst_x27_61_, v___x_117_, v_a_63_, v_a_64_, v_a_65_);
lean_dec_ref_known(v___x_117_, 7);
v___y_68_ = v___x_118_;
goto v___jp_67_;
}
else
{
lean_object* v___x_119_; 
lean_inc_ref(v_inst_x27_61_);
lean_inc_ref(v_inst_60_);
v___x_119_ = l_Lean_Meta_isExprDefEq(v_inst_60_, v_inst_x27_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
v___y_68_ = v___x_119_;
goto v___jp_67_;
}
v___jp_67_:
{
if (lean_obj_tag(v___y_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_92_; 
v_a_69_ = lean_ctor_get(v___y_68_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___y_68_);
if (v_isSharedCheck_92_ == 0)
{
v___x_71_ = v___y_68_;
v_isShared_72_ = v_isSharedCheck_92_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___y_68_);
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
v___x_74_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1);
v___x_75_ = l_Lean_MessageData_ofName(v_declName_59_);
v___x_76_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3);
v___x_78_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = l_Lean_indentExpr(v_inst_60_);
v___x_80_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5);
v___x_82_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = l_Lean_indentExpr(v_inst_x27_61_);
v___x_84_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7);
v___x_86_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_86_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_90_; 
lean_dec_ref(v_inst_x27_61_);
lean_dec_ref(v_inst_60_);
lean_dec(v_declName_59_);
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
lean_dec_ref(v_inst_x27_61_);
lean_dec_ref(v_inst_60_);
lean_dec(v_declName_59_);
v_a_93_ = lean_ctor_get(v___y_68_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___y_68_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___y_68_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___y_68_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object* v_declName_120_, lean_object* v_inst_121_, lean_object* v_inst_x27_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_120_, v_inst_121_, v_inst_x27_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object* v_00_u03b1_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(lean_object* v_00_u03b1_137_, lean_object* v_msg_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(v_00_u03b1_137_, v_msg_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object* v_inst_145_, lean_object* v_declName_146_, lean_object* v___x_147_, lean_object* v_type_148_, lean_object* v_inst_149_, lean_object* v_____r_150_){
_start:
{
lean_object* v_canonExpr_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_canonExpr_151_ = lean_ctor_get(v_inst_145_, 0);
lean_inc(v_canonExpr_151_);
lean_dec_ref(v_inst_145_);
v___x_152_ = l_Lean_mkConst(v_declName_146_, v___x_147_);
v___x_153_ = l_Lean_mkAppB(v___x_152_, v_type_148_, v_inst_149_);
v___x_154_ = lean_apply_1(v_canonExpr_151_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object* v_inst_155_, lean_object* v_declName_156_, lean_object* v___x_157_, lean_object* v_type_158_, lean_object* v_expectedInst_159_, lean_object* v_inst_160_, lean_object* v_toBind_161_, lean_object* v_inst_162_){
_start:
{
lean_object* v___f_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
lean_inc_ref(v_inst_162_);
lean_inc(v_declName_156_);
v___f_163_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_163_, 0, v_inst_155_);
lean_closure_set(v___f_163_, 1, v_declName_156_);
lean_closure_set(v___f_163_, 2, v___x_157_);
lean_closure_set(v___f_163_, 3, v_type_158_);
lean_closure_set(v___f_163_, 4, v_inst_162_);
v___x_164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_164_, 0, v_declName_156_);
lean_closure_set(v___x_164_, 1, v_inst_162_);
lean_closure_set(v___x_164_, 2, v_expectedInst_159_);
v___x_165_ = lean_apply_2(v_inst_160_, lean_box(0), v___x_164_);
v___x_166_ = lean_apply_4(v_toBind_161_, lean_box(0), lean_box(0), v___x_165_, v___f_163_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_type_171_, lean_object* v_u_172_, lean_object* v_instDeclName_173_, lean_object* v_declName_174_, lean_object* v_expectedInst_175_){
_start:
{
lean_object* v_toBind_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_toBind_176_ = lean_ctor_get(v_inst_169_, 1);
lean_inc_n(v_toBind_176_, 2);
v___x_177_ = lean_box(0);
v___x_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_178_, 0, v_u_172_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
lean_inc_ref(v_type_171_);
lean_inc_ref(v___x_178_);
lean_inc_ref(v_inst_170_);
v___f_179_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_179_, 0, v_inst_170_);
lean_closure_set(v___f_179_, 1, v_declName_174_);
lean_closure_set(v___f_179_, 2, v___x_178_);
lean_closure_set(v___f_179_, 3, v_type_171_);
lean_closure_set(v___f_179_, 4, v_expectedInst_175_);
lean_closure_set(v___f_179_, 5, v_inst_167_);
lean_closure_set(v___f_179_, 6, v_toBind_176_);
v___x_180_ = l_Lean_mkConst(v_instDeclName_173_, v___x_178_);
v___x_181_ = l_Lean_Expr_app___override(v___x_180_, v_type_171_);
v___x_182_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_169_, v_inst_168_, v_inst_170_, v___x_181_);
v___x_183_ = lean_apply_4(v_toBind_176_, lean_box(0), lean_box(0), v___x_182_, v___f_179_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object* v_m_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_type_189_, lean_object* v_u_190_, lean_object* v_instDeclName_191_, lean_object* v_declName_192_, lean_object* v_expectedInst_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_185_, v_inst_186_, v_inst_187_, v_inst_188_, v_type_189_, v_u_190_, v_instDeclName_191_, v_declName_192_, v_expectedInst_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_195_, lean_object* v_declName_196_, lean_object* v___x_197_, lean_object* v_type_198_, lean_object* v_inst_199_, lean_object* v_____r_200_){
_start:
{
lean_object* v_canonExpr_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_canonExpr_201_ = lean_ctor_get(v_inst_195_, 0);
lean_inc(v_canonExpr_201_);
lean_dec_ref(v_inst_195_);
v___x_202_ = l_Lean_mkConst(v_declName_196_, v___x_197_);
lean_inc_ref_n(v_type_198_, 2);
v___x_203_ = l_Lean_mkApp4(v___x_202_, v_type_198_, v_type_198_, v_type_198_, v_inst_199_);
v___x_204_ = lean_apply_1(v_canonExpr_201_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_205_, lean_object* v_declName_206_, lean_object* v___x_207_, lean_object* v_type_208_, lean_object* v_expectedInst_209_, lean_object* v_inst_210_, lean_object* v_toBind_211_, lean_object* v_inst_212_){
_start:
{
lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
lean_inc_ref(v_inst_212_);
lean_inc(v_declName_206_);
v___f_213_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_213_, 0, v_inst_205_);
lean_closure_set(v___f_213_, 1, v_declName_206_);
lean_closure_set(v___f_213_, 2, v___x_207_);
lean_closure_set(v___f_213_, 3, v_type_208_);
lean_closure_set(v___f_213_, 4, v_inst_212_);
v___x_214_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_214_, 0, v_declName_206_);
lean_closure_set(v___x_214_, 1, v_inst_212_);
lean_closure_set(v___x_214_, 2, v_expectedInst_209_);
v___x_215_ = lean_apply_2(v_inst_210_, lean_box(0), v___x_214_);
v___x_216_ = lean_apply_4(v_toBind_211_, lean_box(0), lean_box(0), v___x_215_, v___f_213_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_type_221_, lean_object* v_u_222_, lean_object* v_instDeclName_223_, lean_object* v_declName_224_, lean_object* v_expectedInst_225_){
_start:
{
lean_object* v_toBind_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_toBind_226_ = lean_ctor_get(v_inst_219_, 1);
lean_inc_n(v_toBind_226_, 2);
v___x_227_ = lean_box(0);
lean_inc_n(v_u_222_, 2);
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v_u_222_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v_u_222_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v_u_222_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
lean_inc_ref_n(v_type_221_, 3);
lean_inc_ref(v___x_230_);
lean_inc_ref(v_inst_220_);
v___f_231_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_231_, 0, v_inst_220_);
lean_closure_set(v___f_231_, 1, v_declName_224_);
lean_closure_set(v___f_231_, 2, v___x_230_);
lean_closure_set(v___f_231_, 3, v_type_221_);
lean_closure_set(v___f_231_, 4, v_expectedInst_225_);
lean_closure_set(v___f_231_, 5, v_inst_217_);
lean_closure_set(v___f_231_, 6, v_toBind_226_);
v___x_232_ = l_Lean_mkConst(v_instDeclName_223_, v___x_230_);
v___x_233_ = l_Lean_mkApp3(v___x_232_, v_type_221_, v_type_221_, v_type_221_);
v___x_234_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_219_, v_inst_218_, v_inst_220_, v___x_233_);
v___x_235_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v___x_234_, v___f_231_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object* v_m_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_type_241_, lean_object* v_u_242_, lean_object* v_instDeclName_243_, lean_object* v_declName_244_, lean_object* v_expectedInst_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_237_, v_inst_238_, v_inst_239_, v_inst_240_, v_type_241_, v_u_242_, v_instDeclName_243_, v_declName_244_, v_expectedInst_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object* v_inst_247_, lean_object* v___x_248_, lean_object* v___x_249_, lean_object* v_type_250_, lean_object* v___x_251_, lean_object* v_inst_252_, lean_object* v_____r_253_){
_start:
{
lean_object* v_canonExpr_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_canonExpr_254_ = lean_ctor_get(v_inst_247_, 0);
lean_inc(v_canonExpr_254_);
lean_dec_ref(v_inst_247_);
v___x_255_ = l_Lean_mkConst(v___x_248_, v___x_249_);
lean_inc_ref(v_type_250_);
v___x_256_ = l_Lean_mkApp4(v___x_255_, v_type_250_, v___x_251_, v_type_250_, v_inst_252_);
v___x_257_ = lean_apply_1(v_canonExpr_254_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object* v___x_268_, lean_object* v_type_269_, lean_object* v_semiringInst_270_, lean_object* v___x_271_, lean_object* v_inst_272_, lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v_inst_275_, lean_object* v_toBind_276_, lean_object* v_inst_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_inst_x27_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___f_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4));
v___x_279_ = l_Lean_mkConst(v___x_278_, v___x_268_);
lean_inc_ref(v_type_269_);
v_inst_x27_280_ = l_Lean_mkAppB(v___x_279_, v_type_269_, v_semiringInst_270_);
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5));
v___x_282_ = l_Lean_Name_mkStr2(v___x_271_, v___x_281_);
lean_inc_ref(v_inst_277_);
lean_inc(v___x_282_);
v___f_283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_283_, 0, v_inst_272_);
lean_closure_set(v___f_283_, 1, v___x_282_);
lean_closure_set(v___f_283_, 2, v___x_273_);
lean_closure_set(v___f_283_, 3, v_type_269_);
lean_closure_set(v___f_283_, 4, v___x_274_);
lean_closure_set(v___f_283_, 5, v_inst_277_);
v___x_284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_284_, 0, v___x_282_);
lean_closure_set(v___x_284_, 1, v_inst_277_);
lean_closure_set(v___x_284_, 2, v_inst_x27_280_);
v___x_285_ = lean_apply_2(v_inst_275_, lean_box(0), v___x_284_);
v___x_286_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_285_, v___f_283_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Lean_Level_ofNat(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_u_296_, lean_object* v_type_297_, lean_object* v_semiringInst_298_){
_start:
{
lean_object* v_toBind_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_toBind_299_ = lean_ctor_get(v_inst_294_, 1);
lean_inc_n(v_toBind_299_, 2);
v___x_300_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0));
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1));
v___x_302_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_303_ = lean_box(0);
lean_inc(v_u_296_);
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v_u_296_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
lean_inc_ref(v___x_304_);
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v_u_296_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
lean_inc_ref(v___x_306_);
v___x_307_ = l_Lean_mkConst(v___x_301_, v___x_306_);
v___x_308_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_295_);
lean_inc_ref_n(v_type_297_, 2);
v___f_309_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_309_, 0, v___x_304_);
lean_closure_set(v___f_309_, 1, v_type_297_);
lean_closure_set(v___f_309_, 2, v_semiringInst_298_);
lean_closure_set(v___f_309_, 3, v___x_300_);
lean_closure_set(v___f_309_, 4, v_inst_295_);
lean_closure_set(v___f_309_, 5, v___x_306_);
lean_closure_set(v___f_309_, 6, v___x_308_);
lean_closure_set(v___f_309_, 7, v_inst_292_);
lean_closure_set(v___f_309_, 8, v_toBind_299_);
v___x_310_ = l_Lean_mkApp3(v___x_307_, v_type_297_, v___x_308_, v_type_297_);
v___x_311_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_294_, v_inst_293_, v_inst_295_, v___x_310_);
v___x_312_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v___x_311_, v___f_309_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object* v_m_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_u_318_, lean_object* v_type_319_, lean_object* v_semiringInst_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_314_, v_inst_315_, v_inst_316_, v_inst_317_, v_u_318_, v_type_319_, v_semiringInst_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object* v___x_322_, lean_object* v___x_323_, lean_object* v___x_324_, lean_object* v_type_325_, lean_object* v_canonExpr_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = l_Lean_Name_mkStr2(v___x_322_, v___x_323_);
v___x_329_ = l_Lean_mkConst(v___x_328_, v___x_324_);
v___x_330_ = l_Lean_mkAppB(v___x_329_, v_type_325_, v_inst_327_);
v___x_331_ = lean_apply_1(v_canonExpr_326_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object* v___f_332_, lean_object* v_inst_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_apply_1(v___f_332_, v_inst_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_335_, lean_object* v_val_336_, lean_object* v_toBind_337_, lean_object* v___f_338_, lean_object* v_____r_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_apply_2(v_toPure_335_, lean_box(0), v_val_336_);
v___x_341_ = lean_apply_4(v_toBind_337_, lean_box(0), lean_box(0), v___x_340_, v___f_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_342_, lean_object* v_inst_x27_343_, lean_object* v_toBind_344_, lean_object* v___f_345_, lean_object* v___f_346_, lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v_inst_349_, lean_object* v_____do__lift_350_){
_start:
{
if (lean_obj_tag(v_____do__lift_350_) == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_inst_349_);
lean_dec_ref(v___x_348_);
lean_dec_ref(v___x_347_);
lean_dec(v___f_346_);
v___x_351_ = lean_apply_2(v_toPure_342_, lean_box(0), v_inst_x27_343_);
v___x_352_ = lean_apply_4(v_toBind_344_, lean_box(0), lean_box(0), v___x_351_, v___f_345_);
return v___x_352_;
}
else
{
lean_object* v_val_353_; lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___f_345_);
v_val_353_ = lean_ctor_get(v_____do__lift_350_, 0);
lean_inc_n(v_val_353_, 2);
lean_dec_ref_known(v_____do__lift_350_, 1);
lean_inc(v_toBind_344_);
v___f_354_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_354_, 0, v_toPure_342_);
lean_closure_set(v___f_354_, 1, v_val_353_);
lean_closure_set(v___f_354_, 2, v_toBind_344_);
lean_closure_set(v___f_354_, 3, v___f_346_);
v___x_355_ = l_Lean_Name_mkStr2(v___x_347_, v___x_348_);
v___x_356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_356_, 0, v___x_355_);
lean_closure_set(v___x_356_, 1, v_val_353_);
lean_closure_set(v___x_356_, 2, v_inst_x27_343_);
v___x_357_ = lean_apply_2(v_inst_349_, lean_box(0), v___x_356_);
v___x_358_ = lean_apply_4(v_toBind_344_, lean_box(0), lean_box(0), v___x_357_, v___f_354_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_u_371_, lean_object* v_type_372_, lean_object* v_semiringInst_373_){
_start:
{
lean_object* v_toApplicative_374_; lean_object* v_toBind_375_; lean_object* v_canonExpr_376_; lean_object* v_synthInstance_x3f_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_399_; 
v_toApplicative_374_ = lean_ctor_get(v_inst_369_, 0);
lean_inc_ref(v_toApplicative_374_);
v_toBind_375_ = lean_ctor_get(v_inst_369_, 1);
lean_inc(v_toBind_375_);
lean_dec_ref(v_inst_369_);
v_canonExpr_376_ = lean_ctor_get(v_inst_370_, 0);
v_synthInstance_x3f_377_ = lean_ctor_get(v_inst_370_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_inst_370_);
if (v_isSharedCheck_399_ == 0)
{
v___x_379_ = v_inst_370_;
v_isShared_380_ = v_isSharedCheck_399_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_synthInstance_x3f_377_);
lean_inc(v_canonExpr_376_);
lean_dec(v_inst_370_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_399_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_toPure_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v_toPure_381_ = lean_ctor_get(v_toApplicative_374_, 1);
lean_inc(v_toPure_381_);
lean_dec_ref(v_toApplicative_374_);
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0));
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1));
v___x_384_ = lean_box(0);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 1);
lean_ctor_set(v___x_379_, 1, v___x_384_);
lean_ctor_set(v___x_379_, 0, v_u_371_);
v___x_386_ = v___x_379_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_u_371_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_398_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v_inst_x27_388_; lean_object* v___x_389_; lean_object* v___f_390_; lean_object* v___f_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_instType_394_; lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___x_397_; 
lean_inc_ref_n(v___x_386_, 2);
v___x_387_ = l_Lean_mkConst(v___x_383_, v___x_386_);
lean_inc_ref_n(v_type_372_, 2);
v_inst_x27_388_ = l_Lean_mkAppB(v___x_387_, v_type_372_, v_semiringInst_373_);
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2));
v___f_390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_390_, 0, v___x_389_);
lean_closure_set(v___f_390_, 1, v___x_382_);
lean_closure_set(v___f_390_, 2, v___x_386_);
lean_closure_set(v___f_390_, 3, v_type_372_);
lean_closure_set(v___f_390_, 4, v_canonExpr_376_);
v___f_391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_391_, 0, v___f_390_);
v___x_392_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3));
v___x_393_ = l_Lean_mkConst(v___x_392_, v___x_386_);
v_instType_394_ = l_Lean_Expr_app___override(v___x_393_, v_type_372_);
v___x_395_ = lean_apply_1(v_synthInstance_x3f_377_, v_instType_394_);
lean_inc_ref(v___f_391_);
lean_inc(v_toBind_375_);
v___f_396_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_396_, 0, v_toPure_381_);
lean_closure_set(v___f_396_, 1, v_inst_x27_388_);
lean_closure_set(v___f_396_, 2, v_toBind_375_);
lean_closure_set(v___f_396_, 3, v___f_391_);
lean_closure_set(v___f_396_, 4, v___f_391_);
lean_closure_set(v___f_396_, 5, v___x_389_);
lean_closure_set(v___f_396_, 6, v___x_382_);
lean_closure_set(v___f_396_, 7, v_inst_368_);
v___x_397_ = lean_apply_4(v_toBind_375_, lean_box(0), lean_box(0), v___x_395_, v___f_396_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object* v_m_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_u_404_, lean_object* v_type_405_, lean_object* v_semiringInst_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_401_, v_inst_402_, v_inst_403_, v_u_404_, v_type_405_, v_semiringInst_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_408_, lean_object* v_s_409_){
_start:
{
lean_object* v_id_410_; lean_object* v_type_411_; lean_object* v_u_412_; lean_object* v_ringInst_413_; lean_object* v_semiringInst_414_; lean_object* v_charInst_x3f_415_; lean_object* v_mulFn_x3f_416_; lean_object* v_subFn_x3f_417_; lean_object* v_negFn_x3f_418_; lean_object* v_powFn_x3f_419_; lean_object* v_intCastFn_x3f_420_; lean_object* v_natCastFn_x3f_421_; lean_object* v_one_x3f_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_id_410_ = lean_ctor_get(v_s_409_, 0);
v_type_411_ = lean_ctor_get(v_s_409_, 1);
v_u_412_ = lean_ctor_get(v_s_409_, 2);
v_ringInst_413_ = lean_ctor_get(v_s_409_, 3);
v_semiringInst_414_ = lean_ctor_get(v_s_409_, 4);
v_charInst_x3f_415_ = lean_ctor_get(v_s_409_, 5);
v_mulFn_x3f_416_ = lean_ctor_get(v_s_409_, 7);
v_subFn_x3f_417_ = lean_ctor_get(v_s_409_, 8);
v_negFn_x3f_418_ = lean_ctor_get(v_s_409_, 9);
v_powFn_x3f_419_ = lean_ctor_get(v_s_409_, 10);
v_intCastFn_x3f_420_ = lean_ctor_get(v_s_409_, 11);
v_natCastFn_x3f_421_ = lean_ctor_get(v_s_409_, 12);
v_one_x3f_422_ = lean_ctor_get(v_s_409_, 13);
v_isSharedCheck_430_ = !lean_is_exclusive(v_s_409_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_s_409_, 6);
lean_dec(v_unused_431_);
v___x_424_ = v_s_409_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_one_x3f_422_);
lean_inc(v_natCastFn_x3f_421_);
lean_inc(v_intCastFn_x3f_420_);
lean_inc(v_powFn_x3f_419_);
lean_inc(v_negFn_x3f_418_);
lean_inc(v_subFn_x3f_417_);
lean_inc(v_mulFn_x3f_416_);
lean_inc(v_charInst_x3f_415_);
lean_inc(v_semiringInst_414_);
lean_inc(v_ringInst_413_);
lean_inc(v_u_412_);
lean_inc(v_type_411_);
lean_inc(v_id_410_);
lean_dec(v_s_409_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v_addFn_408_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 6, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_id_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_type_411_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_u_412_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_ringInst_413_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_semiringInst_414_);
lean_ctor_set(v_reuseFailAlloc_429_, 5, v_charInst_x3f_415_);
lean_ctor_set(v_reuseFailAlloc_429_, 6, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_429_, 7, v_mulFn_x3f_416_);
lean_ctor_set(v_reuseFailAlloc_429_, 8, v_subFn_x3f_417_);
lean_ctor_set(v_reuseFailAlloc_429_, 9, v_negFn_x3f_418_);
lean_ctor_set(v_reuseFailAlloc_429_, 10, v_powFn_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_429_, 11, v_intCastFn_x3f_420_);
lean_ctor_set(v_reuseFailAlloc_429_, 12, v_natCastFn_x3f_421_);
lean_ctor_set(v_reuseFailAlloc_429_, 13, v_one_x3f_422_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_432_, lean_object* v_addFn_433_, lean_object* v_____r_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_apply_2(v_toPure_432_, lean_box(0), v_addFn_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_436_, lean_object* v_modifyRing_437_, lean_object* v_toBind_438_, lean_object* v_addFn_439_){
_start:
{
lean_object* v___f_440_; lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_inc_ref(v_addFn_439_);
v___f_440_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_440_, 0, v_addFn_439_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_441_, 0, v_toPure_436_);
lean_closure_set(v___f_441_, 1, v_addFn_439_);
v___x_442_ = lean_apply_1(v_modifyRing_437_, v___f_440_);
v___x_443_ = lean_apply_4(v_toBind_438_, lean_box(0), lean_box(0), v___x_442_, v___f_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_toBind_465_, lean_object* v___f_466_, lean_object* v_ring_467_){
_start:
{
lean_object* v_addFn_x3f_468_; 
v_addFn_x3f_468_ = lean_ctor_get(v_ring_467_, 6);
if (lean_obj_tag(v_addFn_x3f_468_) == 1)
{
lean_object* v_val_469_; lean_object* v___x_470_; 
lean_inc_ref(v_addFn_x3f_468_);
lean_dec_ref(v_ring_467_);
lean_dec(v___f_466_);
lean_dec(v_toBind_465_);
lean_dec_ref(v_inst_464_);
lean_dec_ref(v_inst_463_);
lean_dec_ref(v_inst_462_);
lean_dec(v_inst_461_);
v_val_469_ = lean_ctor_get(v_addFn_x3f_468_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v_addFn_x3f_468_, 1);
v___x_470_ = lean_apply_2(v_toPure_460_, lean_box(0), v_val_469_);
return v___x_470_;
}
else
{
lean_object* v_type_471_; lean_object* v_u_472_; lean_object* v_semiringInst_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v_expectedInst_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_toPure_460_);
v_type_471_ = lean_ctor_get(v_ring_467_, 1);
lean_inc_ref_n(v_type_471_, 3);
v_u_472_ = lean_ctor_get(v_ring_467_, 2);
lean_inc_n(v_u_472_, 2);
v_semiringInst_473_ = lean_ctor_get(v_ring_467_, 4);
lean_inc_ref(v_semiringInst_473_);
lean_dec_ref(v_ring_467_);
v___x_474_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_475_ = lean_box(0);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v_u_472_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
lean_inc_ref(v___x_476_);
v___x_477_ = l_Lean_mkConst(v___x_474_, v___x_476_);
v___x_478_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_479_ = l_Lean_mkConst(v___x_478_, v___x_476_);
v___x_480_ = l_Lean_mkAppB(v___x_479_, v_type_471_, v_semiringInst_473_);
v_expectedInst_481_ = l_Lean_mkAppB(v___x_477_, v_type_471_, v___x_480_);
v___x_482_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_483_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_484_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_461_, v_inst_462_, v_inst_463_, v_inst_464_, v_type_471_, v_u_472_, v___x_482_, v___x_483_, v_expectedInst_481_);
v___x_485_ = lean_apply_4(v_toBind_465_, lean_box(0), lean_box(0), v___x_484_, v___f_466_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_){
_start:
{
lean_object* v_toApplicative_491_; lean_object* v_toBind_492_; lean_object* v_getRing_493_; lean_object* v_modifyRing_494_; lean_object* v_toPure_495_; lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___x_498_; 
v_toApplicative_491_ = lean_ctor_get(v_inst_488_, 0);
v_toBind_492_ = lean_ctor_get(v_inst_488_, 1);
lean_inc_n(v_toBind_492_, 3);
v_getRing_493_ = lean_ctor_get(v_inst_490_, 0);
lean_inc(v_getRing_493_);
v_modifyRing_494_ = lean_ctor_get(v_inst_490_, 1);
lean_inc(v_modifyRing_494_);
lean_dec_ref(v_inst_490_);
v_toPure_495_ = lean_ctor_get(v_toApplicative_491_, 1);
lean_inc_n(v_toPure_495_, 2);
v___f_496_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_496_, 0, v_toPure_495_);
lean_closure_set(v___f_496_, 1, v_modifyRing_494_);
lean_closure_set(v___f_496_, 2, v_toBind_492_);
v___f_497_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_497_, 0, v_toPure_495_);
lean_closure_set(v___f_497_, 1, v_inst_486_);
lean_closure_set(v___f_497_, 2, v_inst_487_);
lean_closure_set(v___f_497_, 3, v_inst_488_);
lean_closure_set(v___f_497_, 4, v_inst_489_);
lean_closure_set(v___f_497_, 5, v_toBind_492_);
lean_closure_set(v___f_497_, 6, v___f_496_);
v___x_498_ = lean_apply_4(v_toBind_492_, lean_box(0), lean_box(0), v_getRing_493_, v___f_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_500_, v_inst_501_, v_inst_502_, v_inst_503_, v_inst_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_506_, lean_object* v_s_507_){
_start:
{
lean_object* v_id_508_; lean_object* v_type_509_; lean_object* v_u_510_; lean_object* v_ringInst_511_; lean_object* v_semiringInst_512_; lean_object* v_charInst_x3f_513_; lean_object* v_addFn_x3f_514_; lean_object* v_subFn_x3f_515_; lean_object* v_negFn_x3f_516_; lean_object* v_powFn_x3f_517_; lean_object* v_intCastFn_x3f_518_; lean_object* v_natCastFn_x3f_519_; lean_object* v_one_x3f_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_id_508_ = lean_ctor_get(v_s_507_, 0);
v_type_509_ = lean_ctor_get(v_s_507_, 1);
v_u_510_ = lean_ctor_get(v_s_507_, 2);
v_ringInst_511_ = lean_ctor_get(v_s_507_, 3);
v_semiringInst_512_ = lean_ctor_get(v_s_507_, 4);
v_charInst_x3f_513_ = lean_ctor_get(v_s_507_, 5);
v_addFn_x3f_514_ = lean_ctor_get(v_s_507_, 6);
v_subFn_x3f_515_ = lean_ctor_get(v_s_507_, 8);
v_negFn_x3f_516_ = lean_ctor_get(v_s_507_, 9);
v_powFn_x3f_517_ = lean_ctor_get(v_s_507_, 10);
v_intCastFn_x3f_518_ = lean_ctor_get(v_s_507_, 11);
v_natCastFn_x3f_519_ = lean_ctor_get(v_s_507_, 12);
v_one_x3f_520_ = lean_ctor_get(v_s_507_, 13);
v_isSharedCheck_528_ = !lean_is_exclusive(v_s_507_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_s_507_, 7);
lean_dec(v_unused_529_);
v___x_522_ = v_s_507_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_one_x3f_520_);
lean_inc(v_natCastFn_x3f_519_);
lean_inc(v_intCastFn_x3f_518_);
lean_inc(v_powFn_x3f_517_);
lean_inc(v_negFn_x3f_516_);
lean_inc(v_subFn_x3f_515_);
lean_inc(v_addFn_x3f_514_);
lean_inc(v_charInst_x3f_513_);
lean_inc(v_semiringInst_512_);
lean_inc(v_ringInst_511_);
lean_inc(v_u_510_);
lean_inc(v_type_509_);
lean_inc(v_id_508_);
lean_dec(v_s_507_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v_mulFn_506_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 7, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_id_508_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_type_509_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_u_510_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_ringInst_511_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v_semiringInst_512_);
lean_ctor_set(v_reuseFailAlloc_527_, 5, v_charInst_x3f_513_);
lean_ctor_set(v_reuseFailAlloc_527_, 6, v_addFn_x3f_514_);
lean_ctor_set(v_reuseFailAlloc_527_, 7, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 8, v_subFn_x3f_515_);
lean_ctor_set(v_reuseFailAlloc_527_, 9, v_negFn_x3f_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 10, v_powFn_x3f_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 11, v_intCastFn_x3f_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 12, v_natCastFn_x3f_519_);
lean_ctor_set(v_reuseFailAlloc_527_, 13, v_one_x3f_520_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object* v_toPure_530_, lean_object* v_mulFn_531_, lean_object* v_____r_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_apply_2(v_toPure_530_, lean_box(0), v_mulFn_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object* v_toPure_534_, lean_object* v_modifyRing_535_, lean_object* v_toBind_536_, lean_object* v_mulFn_537_){
_start:
{
lean_object* v___f_538_; lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_inc_ref(v_mulFn_537_);
v___f_538_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_538_, 0, v_mulFn_537_);
v___f_539_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_539_, 0, v_toPure_534_);
lean_closure_set(v___f_539_, 1, v_mulFn_537_);
v___x_540_ = lean_apply_1(v_modifyRing_535_, v___f_538_);
v___x_541_ = lean_apply_4(v_toBind_536_, lean_box(0), lean_box(0), v___x_540_, v___f_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object* v_toPure_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_toBind_563_, lean_object* v___f_564_, lean_object* v_ring_565_){
_start:
{
lean_object* v_mulFn_x3f_566_; 
v_mulFn_x3f_566_ = lean_ctor_get(v_ring_565_, 7);
if (lean_obj_tag(v_mulFn_x3f_566_) == 1)
{
lean_object* v_val_567_; lean_object* v___x_568_; 
lean_inc_ref(v_mulFn_x3f_566_);
lean_dec_ref(v_ring_565_);
lean_dec(v___f_564_);
lean_dec(v_toBind_563_);
lean_dec_ref(v_inst_562_);
lean_dec_ref(v_inst_561_);
lean_dec_ref(v_inst_560_);
lean_dec(v_inst_559_);
v_val_567_ = lean_ctor_get(v_mulFn_x3f_566_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v_mulFn_x3f_566_, 1);
v___x_568_ = lean_apply_2(v_toPure_558_, lean_box(0), v_val_567_);
return v___x_568_;
}
else
{
lean_object* v_type_569_; lean_object* v_u_570_; lean_object* v_semiringInst_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_expectedInst_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_toPure_558_);
v_type_569_ = lean_ctor_get(v_ring_565_, 1);
lean_inc_ref_n(v_type_569_, 3);
v_u_570_ = lean_ctor_get(v_ring_565_, 2);
lean_inc_n(v_u_570_, 2);
v_semiringInst_571_ = lean_ctor_get(v_ring_565_, 4);
lean_inc_ref(v_semiringInst_571_);
lean_dec_ref(v_ring_565_);
v___x_572_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v_u_570_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
lean_inc_ref(v___x_574_);
v___x_575_ = l_Lean_mkConst(v___x_572_, v___x_574_);
v___x_576_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_577_ = l_Lean_mkConst(v___x_576_, v___x_574_);
v___x_578_ = l_Lean_mkAppB(v___x_577_, v_type_569_, v_semiringInst_571_);
v_expectedInst_579_ = l_Lean_mkAppB(v___x_575_, v_type_569_, v___x_578_);
v___x_580_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_581_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_582_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_559_, v_inst_560_, v_inst_561_, v_inst_562_, v_type_569_, v_u_570_, v___x_580_, v___x_581_, v_expectedInst_579_);
v___x_583_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_582_, v___f_564_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_){
_start:
{
lean_object* v_toApplicative_589_; lean_object* v_toBind_590_; lean_object* v_getRing_591_; lean_object* v_modifyRing_592_; lean_object* v_toPure_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_596_; 
v_toApplicative_589_ = lean_ctor_get(v_inst_586_, 0);
v_toBind_590_ = lean_ctor_get(v_inst_586_, 1);
lean_inc_n(v_toBind_590_, 3);
v_getRing_591_ = lean_ctor_get(v_inst_588_, 0);
lean_inc(v_getRing_591_);
v_modifyRing_592_ = lean_ctor_get(v_inst_588_, 1);
lean_inc(v_modifyRing_592_);
lean_dec_ref(v_inst_588_);
v_toPure_593_ = lean_ctor_get(v_toApplicative_589_, 1);
lean_inc_n(v_toPure_593_, 2);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_594_, 0, v_toPure_593_);
lean_closure_set(v___f_594_, 1, v_modifyRing_592_);
lean_closure_set(v___f_594_, 2, v_toBind_590_);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_595_, 0, v_toPure_593_);
lean_closure_set(v___f_595_, 1, v_inst_584_);
lean_closure_set(v___f_595_, 2, v_inst_585_);
lean_closure_set(v___f_595_, 3, v_inst_586_);
lean_closure_set(v___f_595_, 4, v_inst_587_);
lean_closure_set(v___f_595_, 5, v_toBind_590_);
lean_closure_set(v___f_595_, 6, v___f_594_);
v___x_596_ = lean_apply_4(v_toBind_590_, lean_box(0), lean_box(0), v_getRing_591_, v___f_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object* v_m_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_598_, v_inst_599_, v_inst_600_, v_inst_601_, v_inst_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object* v_subFn_604_, lean_object* v_s_605_){
_start:
{
lean_object* v_id_606_; lean_object* v_type_607_; lean_object* v_u_608_; lean_object* v_ringInst_609_; lean_object* v_semiringInst_610_; lean_object* v_charInst_x3f_611_; lean_object* v_addFn_x3f_612_; lean_object* v_mulFn_x3f_613_; lean_object* v_negFn_x3f_614_; lean_object* v_powFn_x3f_615_; lean_object* v_intCastFn_x3f_616_; lean_object* v_natCastFn_x3f_617_; lean_object* v_one_x3f_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
v_id_606_ = lean_ctor_get(v_s_605_, 0);
v_type_607_ = lean_ctor_get(v_s_605_, 1);
v_u_608_ = lean_ctor_get(v_s_605_, 2);
v_ringInst_609_ = lean_ctor_get(v_s_605_, 3);
v_semiringInst_610_ = lean_ctor_get(v_s_605_, 4);
v_charInst_x3f_611_ = lean_ctor_get(v_s_605_, 5);
v_addFn_x3f_612_ = lean_ctor_get(v_s_605_, 6);
v_mulFn_x3f_613_ = lean_ctor_get(v_s_605_, 7);
v_negFn_x3f_614_ = lean_ctor_get(v_s_605_, 9);
v_powFn_x3f_615_ = lean_ctor_get(v_s_605_, 10);
v_intCastFn_x3f_616_ = lean_ctor_get(v_s_605_, 11);
v_natCastFn_x3f_617_ = lean_ctor_get(v_s_605_, 12);
v_one_x3f_618_ = lean_ctor_get(v_s_605_, 13);
v_isSharedCheck_626_ = !lean_is_exclusive(v_s_605_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v_s_605_, 8);
lean_dec(v_unused_627_);
v___x_620_ = v_s_605_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_one_x3f_618_);
lean_inc(v_natCastFn_x3f_617_);
lean_inc(v_intCastFn_x3f_616_);
lean_inc(v_powFn_x3f_615_);
lean_inc(v_negFn_x3f_614_);
lean_inc(v_mulFn_x3f_613_);
lean_inc(v_addFn_x3f_612_);
lean_inc(v_charInst_x3f_611_);
lean_inc(v_semiringInst_610_);
lean_inc(v_ringInst_609_);
lean_inc(v_u_608_);
lean_inc(v_type_607_);
lean_inc(v_id_606_);
lean_dec(v_s_605_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_subFn_604_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 8, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_id_606_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_type_607_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_u_608_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_ringInst_609_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_semiringInst_610_);
lean_ctor_set(v_reuseFailAlloc_625_, 5, v_charInst_x3f_611_);
lean_ctor_set(v_reuseFailAlloc_625_, 6, v_addFn_x3f_612_);
lean_ctor_set(v_reuseFailAlloc_625_, 7, v_mulFn_x3f_613_);
lean_ctor_set(v_reuseFailAlloc_625_, 8, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 9, v_negFn_x3f_614_);
lean_ctor_set(v_reuseFailAlloc_625_, 10, v_powFn_x3f_615_);
lean_ctor_set(v_reuseFailAlloc_625_, 11, v_intCastFn_x3f_616_);
lean_ctor_set(v_reuseFailAlloc_625_, 12, v_natCastFn_x3f_617_);
lean_ctor_set(v_reuseFailAlloc_625_, 13, v_one_x3f_618_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_628_, lean_object* v_subFn_629_, lean_object* v_____r_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_apply_2(v_toPure_628_, lean_box(0), v_subFn_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_632_, lean_object* v_modifyRing_633_, lean_object* v_toBind_634_, lean_object* v_subFn_635_){
_start:
{
lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
lean_inc_ref(v_subFn_635_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_636_, 0, v_subFn_635_);
v___f_637_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_637_, 0, v_toPure_632_);
lean_closure_set(v___f_637_, 1, v_subFn_635_);
v___x_638_ = lean_apply_1(v_modifyRing_633_, v___f_636_);
v___x_639_ = lean_apply_4(v_toBind_634_, lean_box(0), lean_box(0), v___x_638_, v___f_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_toBind_662_, lean_object* v___f_663_, lean_object* v_ring_664_){
_start:
{
lean_object* v_subFn_x3f_665_; 
v_subFn_x3f_665_ = lean_ctor_get(v_ring_664_, 8);
if (lean_obj_tag(v_subFn_x3f_665_) == 1)
{
lean_object* v_val_666_; lean_object* v___x_667_; 
lean_inc_ref(v_subFn_x3f_665_);
lean_dec_ref(v_ring_664_);
lean_dec(v___f_663_);
lean_dec(v_toBind_662_);
lean_dec_ref(v_inst_661_);
lean_dec_ref(v_inst_660_);
lean_dec_ref(v_inst_659_);
lean_dec(v_inst_658_);
v_val_666_ = lean_ctor_get(v_subFn_x3f_665_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v_subFn_x3f_665_, 1);
v___x_667_ = lean_apply_2(v_toPure_657_, lean_box(0), v_val_666_);
return v___x_667_;
}
else
{
lean_object* v_type_668_; lean_object* v_u_669_; lean_object* v_ringInst_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_expectedInst_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v_toPure_657_);
v_type_668_ = lean_ctor_get(v_ring_664_, 1);
lean_inc_ref_n(v_type_668_, 3);
v_u_669_ = lean_ctor_get(v_ring_664_, 2);
lean_inc_n(v_u_669_, 2);
v_ringInst_670_ = lean_ctor_get(v_ring_664_, 3);
lean_inc_ref(v_ringInst_670_);
lean_dec_ref(v_ring_664_);
v___x_671_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_672_ = lean_box(0);
v___x_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_673_, 0, v_u_669_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
lean_inc_ref(v___x_673_);
v___x_674_ = l_Lean_mkConst(v___x_671_, v___x_673_);
v___x_675_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4));
v___x_676_ = l_Lean_mkConst(v___x_675_, v___x_673_);
v___x_677_ = l_Lean_mkAppB(v___x_676_, v_type_668_, v_ringInst_670_);
v_expectedInst_678_ = l_Lean_mkAppB(v___x_674_, v_type_668_, v___x_677_);
v___x_679_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6));
v___x_680_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8));
v___x_681_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_658_, v_inst_659_, v_inst_660_, v_inst_661_, v_type_668_, v_u_669_, v___x_679_, v___x_680_, v_expectedInst_678_);
v___x_682_ = lean_apply_4(v_toBind_662_, lean_box(0), lean_box(0), v___x_681_, v___f_663_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_){
_start:
{
lean_object* v_toApplicative_688_; lean_object* v_toBind_689_; lean_object* v_getRing_690_; lean_object* v_modifyRing_691_; lean_object* v_toPure_692_; lean_object* v___f_693_; lean_object* v___f_694_; lean_object* v___x_695_; 
v_toApplicative_688_ = lean_ctor_get(v_inst_685_, 0);
v_toBind_689_ = lean_ctor_get(v_inst_685_, 1);
lean_inc_n(v_toBind_689_, 3);
v_getRing_690_ = lean_ctor_get(v_inst_687_, 0);
lean_inc(v_getRing_690_);
v_modifyRing_691_ = lean_ctor_get(v_inst_687_, 1);
lean_inc(v_modifyRing_691_);
lean_dec_ref(v_inst_687_);
v_toPure_692_ = lean_ctor_get(v_toApplicative_688_, 1);
lean_inc_n(v_toPure_692_, 2);
v___f_693_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_693_, 0, v_toPure_692_);
lean_closure_set(v___f_693_, 1, v_modifyRing_691_);
lean_closure_set(v___f_693_, 2, v_toBind_689_);
v___f_694_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_694_, 0, v_toPure_692_);
lean_closure_set(v___f_694_, 1, v_inst_683_);
lean_closure_set(v___f_694_, 2, v_inst_684_);
lean_closure_set(v___f_694_, 3, v_inst_685_);
lean_closure_set(v___f_694_, 4, v_inst_686_);
lean_closure_set(v___f_694_, 5, v_toBind_689_);
lean_closure_set(v___f_694_, 6, v___f_693_);
v___x_695_ = lean_apply_4(v_toBind_689_, lean_box(0), lean_box(0), v_getRing_690_, v___f_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_697_, v_inst_698_, v_inst_699_, v_inst_700_, v_inst_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_703_, lean_object* v_s_704_){
_start:
{
lean_object* v_id_705_; lean_object* v_type_706_; lean_object* v_u_707_; lean_object* v_ringInst_708_; lean_object* v_semiringInst_709_; lean_object* v_charInst_x3f_710_; lean_object* v_addFn_x3f_711_; lean_object* v_mulFn_x3f_712_; lean_object* v_subFn_x3f_713_; lean_object* v_powFn_x3f_714_; lean_object* v_intCastFn_x3f_715_; lean_object* v_natCastFn_x3f_716_; lean_object* v_one_x3f_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_725_; 
v_id_705_ = lean_ctor_get(v_s_704_, 0);
v_type_706_ = lean_ctor_get(v_s_704_, 1);
v_u_707_ = lean_ctor_get(v_s_704_, 2);
v_ringInst_708_ = lean_ctor_get(v_s_704_, 3);
v_semiringInst_709_ = lean_ctor_get(v_s_704_, 4);
v_charInst_x3f_710_ = lean_ctor_get(v_s_704_, 5);
v_addFn_x3f_711_ = lean_ctor_get(v_s_704_, 6);
v_mulFn_x3f_712_ = lean_ctor_get(v_s_704_, 7);
v_subFn_x3f_713_ = lean_ctor_get(v_s_704_, 8);
v_powFn_x3f_714_ = lean_ctor_get(v_s_704_, 10);
v_intCastFn_x3f_715_ = lean_ctor_get(v_s_704_, 11);
v_natCastFn_x3f_716_ = lean_ctor_get(v_s_704_, 12);
v_one_x3f_717_ = lean_ctor_get(v_s_704_, 13);
v_isSharedCheck_725_ = !lean_is_exclusive(v_s_704_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_s_704_, 9);
lean_dec(v_unused_726_);
v___x_719_ = v_s_704_;
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_one_x3f_717_);
lean_inc(v_natCastFn_x3f_716_);
lean_inc(v_intCastFn_x3f_715_);
lean_inc(v_powFn_x3f_714_);
lean_inc(v_subFn_x3f_713_);
lean_inc(v_mulFn_x3f_712_);
lean_inc(v_addFn_x3f_711_);
lean_inc(v_charInst_x3f_710_);
lean_inc(v_semiringInst_709_);
lean_inc(v_ringInst_708_);
lean_inc(v_u_707_);
lean_inc(v_type_706_);
lean_inc(v_id_705_);
lean_dec(v_s_704_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v_negFn_703_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 9, v___x_721_);
v___x_723_ = v___x_719_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_id_705_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_type_706_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_u_707_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_ringInst_708_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v_semiringInst_709_);
lean_ctor_set(v_reuseFailAlloc_724_, 5, v_charInst_x3f_710_);
lean_ctor_set(v_reuseFailAlloc_724_, 6, v_addFn_x3f_711_);
lean_ctor_set(v_reuseFailAlloc_724_, 7, v_mulFn_x3f_712_);
lean_ctor_set(v_reuseFailAlloc_724_, 8, v_subFn_x3f_713_);
lean_ctor_set(v_reuseFailAlloc_724_, 9, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_724_, 10, v_powFn_x3f_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 11, v_intCastFn_x3f_715_);
lean_ctor_set(v_reuseFailAlloc_724_, 12, v_natCastFn_x3f_716_);
lean_ctor_set(v_reuseFailAlloc_724_, 13, v_one_x3f_717_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_727_, lean_object* v_negFn_728_, lean_object* v_____r_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_apply_2(v_toPure_727_, lean_box(0), v_negFn_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_731_, lean_object* v_modifyRing_732_, lean_object* v_toBind_733_, lean_object* v_negFn_734_){
_start:
{
lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_inc_ref(v_negFn_734_);
v___f_735_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_735_, 0, v_negFn_734_);
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_736_, 0, v_toPure_731_);
lean_closure_set(v___f_736_, 1, v_negFn_734_);
v___x_737_ = lean_apply_1(v_modifyRing_732_, v___f_735_);
v___x_738_ = lean_apply_4(v_toBind_733_, lean_box(0), lean_box(0), v___x_737_, v___f_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_toBind_757_, lean_object* v___f_758_, lean_object* v_ring_759_){
_start:
{
lean_object* v_negFn_x3f_760_; 
v_negFn_x3f_760_ = lean_ctor_get(v_ring_759_, 9);
if (lean_obj_tag(v_negFn_x3f_760_) == 1)
{
lean_object* v_val_761_; lean_object* v___x_762_; 
lean_inc_ref(v_negFn_x3f_760_);
lean_dec_ref(v_ring_759_);
lean_dec(v___f_758_);
lean_dec(v_toBind_757_);
lean_dec_ref(v_inst_756_);
lean_dec_ref(v_inst_755_);
lean_dec_ref(v_inst_754_);
lean_dec(v_inst_753_);
v_val_761_ = lean_ctor_get(v_negFn_x3f_760_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v_negFn_x3f_760_, 1);
v___x_762_ = lean_apply_2(v_toPure_752_, lean_box(0), v_val_761_);
return v___x_762_;
}
else
{
lean_object* v_type_763_; lean_object* v_u_764_; lean_object* v_ringInst_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_expectedInst_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec(v_toPure_752_);
v_type_763_ = lean_ctor_get(v_ring_759_, 1);
lean_inc_ref_n(v_type_763_, 2);
v_u_764_ = lean_ctor_get(v_ring_759_, 2);
lean_inc_n(v_u_764_, 2);
v_ringInst_765_ = lean_ctor_get(v_ring_759_, 3);
lean_inc_ref(v_ringInst_765_);
lean_dec_ref(v_ring_759_);
v___x_766_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v_u_764_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_mkConst(v___x_766_, v___x_768_);
v_expectedInst_770_ = l_Lean_mkAppB(v___x_769_, v_type_763_, v_ringInst_765_);
v___x_771_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_772_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_773_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_753_, v_inst_754_, v_inst_755_, v_inst_756_, v_type_763_, v_u_764_, v___x_771_, v___x_772_, v_expectedInst_770_);
v___x_774_ = lean_apply_4(v_toBind_757_, lean_box(0), lean_box(0), v___x_773_, v___f_758_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_){
_start:
{
lean_object* v_toApplicative_780_; lean_object* v_toBind_781_; lean_object* v_getRing_782_; lean_object* v_modifyRing_783_; lean_object* v_toPure_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___x_787_; 
v_toApplicative_780_ = lean_ctor_get(v_inst_777_, 0);
v_toBind_781_ = lean_ctor_get(v_inst_777_, 1);
lean_inc_n(v_toBind_781_, 3);
v_getRing_782_ = lean_ctor_get(v_inst_779_, 0);
lean_inc(v_getRing_782_);
v_modifyRing_783_ = lean_ctor_get(v_inst_779_, 1);
lean_inc(v_modifyRing_783_);
lean_dec_ref(v_inst_779_);
v_toPure_784_ = lean_ctor_get(v_toApplicative_780_, 1);
lean_inc_n(v_toPure_784_, 2);
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_785_, 0, v_toPure_784_);
lean_closure_set(v___f_785_, 1, v_modifyRing_783_);
lean_closure_set(v___f_785_, 2, v_toBind_781_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_786_, 0, v_toPure_784_);
lean_closure_set(v___f_786_, 1, v_inst_775_);
lean_closure_set(v___f_786_, 2, v_inst_776_);
lean_closure_set(v___f_786_, 3, v_inst_777_);
lean_closure_set(v___f_786_, 4, v_inst_778_);
lean_closure_set(v___f_786_, 5, v_toBind_781_);
lean_closure_set(v___f_786_, 6, v___f_785_);
v___x_787_ = lean_apply_4(v_toBind_781_, lean_box(0), lean_box(0), v_getRing_782_, v___f_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_inst_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_789_, v_inst_790_, v_inst_791_, v_inst_792_, v_inst_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_795_, lean_object* v_s_796_){
_start:
{
lean_object* v_id_797_; lean_object* v_type_798_; lean_object* v_u_799_; lean_object* v_ringInst_800_; lean_object* v_semiringInst_801_; lean_object* v_charInst_x3f_802_; lean_object* v_addFn_x3f_803_; lean_object* v_mulFn_x3f_804_; lean_object* v_subFn_x3f_805_; lean_object* v_negFn_x3f_806_; lean_object* v_intCastFn_x3f_807_; lean_object* v_natCastFn_x3f_808_; lean_object* v_one_x3f_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
v_id_797_ = lean_ctor_get(v_s_796_, 0);
v_type_798_ = lean_ctor_get(v_s_796_, 1);
v_u_799_ = lean_ctor_get(v_s_796_, 2);
v_ringInst_800_ = lean_ctor_get(v_s_796_, 3);
v_semiringInst_801_ = lean_ctor_get(v_s_796_, 4);
v_charInst_x3f_802_ = lean_ctor_get(v_s_796_, 5);
v_addFn_x3f_803_ = lean_ctor_get(v_s_796_, 6);
v_mulFn_x3f_804_ = lean_ctor_get(v_s_796_, 7);
v_subFn_x3f_805_ = lean_ctor_get(v_s_796_, 8);
v_negFn_x3f_806_ = lean_ctor_get(v_s_796_, 9);
v_intCastFn_x3f_807_ = lean_ctor_get(v_s_796_, 11);
v_natCastFn_x3f_808_ = lean_ctor_get(v_s_796_, 12);
v_one_x3f_809_ = lean_ctor_get(v_s_796_, 13);
v_isSharedCheck_817_ = !lean_is_exclusive(v_s_796_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_s_796_, 10);
lean_dec(v_unused_818_);
v___x_811_ = v_s_796_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_one_x3f_809_);
lean_inc(v_natCastFn_x3f_808_);
lean_inc(v_intCastFn_x3f_807_);
lean_inc(v_negFn_x3f_806_);
lean_inc(v_subFn_x3f_805_);
lean_inc(v_mulFn_x3f_804_);
lean_inc(v_addFn_x3f_803_);
lean_inc(v_charInst_x3f_802_);
lean_inc(v_semiringInst_801_);
lean_inc(v_ringInst_800_);
lean_inc(v_u_799_);
lean_inc(v_type_798_);
lean_inc(v_id_797_);
lean_dec(v_s_796_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v_powFn_795_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 10, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_id_797_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_type_798_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_u_799_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_ringInst_800_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_semiringInst_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 5, v_charInst_x3f_802_);
lean_ctor_set(v_reuseFailAlloc_816_, 6, v_addFn_x3f_803_);
lean_ctor_set(v_reuseFailAlloc_816_, 7, v_mulFn_x3f_804_);
lean_ctor_set(v_reuseFailAlloc_816_, 8, v_subFn_x3f_805_);
lean_ctor_set(v_reuseFailAlloc_816_, 9, v_negFn_x3f_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 10, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 11, v_intCastFn_x3f_807_);
lean_ctor_set(v_reuseFailAlloc_816_, 12, v_natCastFn_x3f_808_);
lean_ctor_set(v_reuseFailAlloc_816_, 13, v_one_x3f_809_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_819_, lean_object* v_powFn_820_, lean_object* v_____r_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = lean_apply_2(v_toPure_819_, lean_box(0), v_powFn_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_823_, lean_object* v_modifyRing_824_, lean_object* v_toBind_825_, lean_object* v_powFn_826_){
_start:
{
lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_inc_ref(v_powFn_826_);
v___f_827_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_827_, 0, v_powFn_826_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_828_, 0, v_toPure_823_);
lean_closure_set(v___f_828_, 1, v_powFn_826_);
v___x_829_ = lean_apply_1(v_modifyRing_824_, v___f_827_);
v___x_830_ = lean_apply_4(v_toBind_825_, lean_box(0), lean_box(0), v___x_829_, v___f_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_toBind_836_, lean_object* v___f_837_, lean_object* v_ring_838_){
_start:
{
lean_object* v_powFn_x3f_839_; 
v_powFn_x3f_839_ = lean_ctor_get(v_ring_838_, 10);
if (lean_obj_tag(v_powFn_x3f_839_) == 1)
{
lean_object* v_val_840_; lean_object* v___x_841_; 
lean_inc_ref(v_powFn_x3f_839_);
lean_dec_ref(v_ring_838_);
lean_dec(v___f_837_);
lean_dec(v_toBind_836_);
lean_dec_ref(v_inst_835_);
lean_dec_ref(v_inst_834_);
lean_dec_ref(v_inst_833_);
lean_dec(v_inst_832_);
v_val_840_ = lean_ctor_get(v_powFn_x3f_839_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v_powFn_x3f_839_, 1);
v___x_841_ = lean_apply_2(v_toPure_831_, lean_box(0), v_val_840_);
return v___x_841_;
}
else
{
lean_object* v_type_842_; lean_object* v_u_843_; lean_object* v_semiringInst_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_toPure_831_);
v_type_842_ = lean_ctor_get(v_ring_838_, 1);
lean_inc_ref(v_type_842_);
v_u_843_ = lean_ctor_get(v_ring_838_, 2);
lean_inc(v_u_843_);
v_semiringInst_844_ = lean_ctor_get(v_ring_838_, 4);
lean_inc_ref(v_semiringInst_844_);
lean_dec_ref(v_ring_838_);
v___x_845_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_832_, v_inst_833_, v_inst_834_, v_inst_835_, v_u_843_, v_type_842_, v_semiringInst_844_);
v___x_846_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_845_, v___f_837_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_){
_start:
{
lean_object* v_toApplicative_852_; lean_object* v_toBind_853_; lean_object* v_getRing_854_; lean_object* v_modifyRing_855_; lean_object* v_toPure_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___x_859_; 
v_toApplicative_852_ = lean_ctor_get(v_inst_849_, 0);
v_toBind_853_ = lean_ctor_get(v_inst_849_, 1);
lean_inc_n(v_toBind_853_, 3);
v_getRing_854_ = lean_ctor_get(v_inst_851_, 0);
lean_inc(v_getRing_854_);
v_modifyRing_855_ = lean_ctor_get(v_inst_851_, 1);
lean_inc(v_modifyRing_855_);
lean_dec_ref(v_inst_851_);
v_toPure_856_ = lean_ctor_get(v_toApplicative_852_, 1);
lean_inc_n(v_toPure_856_, 2);
v___f_857_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_857_, 0, v_toPure_856_);
lean_closure_set(v___f_857_, 1, v_modifyRing_855_);
lean_closure_set(v___f_857_, 2, v_toBind_853_);
v___f_858_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_858_, 0, v_toPure_856_);
lean_closure_set(v___f_858_, 1, v_inst_847_);
lean_closure_set(v___f_858_, 2, v_inst_848_);
lean_closure_set(v___f_858_, 3, v_inst_849_);
lean_closure_set(v___f_858_, 4, v_inst_850_);
lean_closure_set(v___f_858_, 5, v_toBind_853_);
lean_closure_set(v___f_858_, 6, v___f_857_);
v___x_859_ = lean_apply_4(v_toBind_853_, lean_box(0), lean_box(0), v_getRing_854_, v___f_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_inst_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_861_, v_inst_862_, v_inst_863_, v_inst_864_, v_inst_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_867_, lean_object* v_s_868_){
_start:
{
lean_object* v_id_869_; lean_object* v_type_870_; lean_object* v_u_871_; lean_object* v_ringInst_872_; lean_object* v_semiringInst_873_; lean_object* v_charInst_x3f_874_; lean_object* v_addFn_x3f_875_; lean_object* v_mulFn_x3f_876_; lean_object* v_subFn_x3f_877_; lean_object* v_negFn_x3f_878_; lean_object* v_powFn_x3f_879_; lean_object* v_natCastFn_x3f_880_; lean_object* v_one_x3f_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_id_869_ = lean_ctor_get(v_s_868_, 0);
v_type_870_ = lean_ctor_get(v_s_868_, 1);
v_u_871_ = lean_ctor_get(v_s_868_, 2);
v_ringInst_872_ = lean_ctor_get(v_s_868_, 3);
v_semiringInst_873_ = lean_ctor_get(v_s_868_, 4);
v_charInst_x3f_874_ = lean_ctor_get(v_s_868_, 5);
v_addFn_x3f_875_ = lean_ctor_get(v_s_868_, 6);
v_mulFn_x3f_876_ = lean_ctor_get(v_s_868_, 7);
v_subFn_x3f_877_ = lean_ctor_get(v_s_868_, 8);
v_negFn_x3f_878_ = lean_ctor_get(v_s_868_, 9);
v_powFn_x3f_879_ = lean_ctor_get(v_s_868_, 10);
v_natCastFn_x3f_880_ = lean_ctor_get(v_s_868_, 12);
v_one_x3f_881_ = lean_ctor_get(v_s_868_, 13);
v_isSharedCheck_889_ = !lean_is_exclusive(v_s_868_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_s_868_, 11);
lean_dec(v_unused_890_);
v___x_883_ = v_s_868_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_one_x3f_881_);
lean_inc(v_natCastFn_x3f_880_);
lean_inc(v_powFn_x3f_879_);
lean_inc(v_negFn_x3f_878_);
lean_inc(v_subFn_x3f_877_);
lean_inc(v_mulFn_x3f_876_);
lean_inc(v_addFn_x3f_875_);
lean_inc(v_charInst_x3f_874_);
lean_inc(v_semiringInst_873_);
lean_inc(v_ringInst_872_);
lean_inc(v_u_871_);
lean_inc(v_type_870_);
lean_inc(v_id_869_);
lean_dec(v_s_868_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_intCastFn_867_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 11, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_id_869_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_type_870_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_u_871_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_ringInst_872_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_semiringInst_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v_charInst_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_888_, 6, v_addFn_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_888_, 7, v_mulFn_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_888_, 8, v_subFn_x3f_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 9, v_negFn_x3f_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 10, v_powFn_x3f_879_);
lean_ctor_set(v_reuseFailAlloc_888_, 11, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_888_, 12, v_natCastFn_x3f_880_);
lean_ctor_set(v_reuseFailAlloc_888_, 13, v_one_x3f_881_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_891_, lean_object* v_intCastFn_892_, lean_object* v_____r_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_apply_2(v_toPure_891_, lean_box(0), v_intCastFn_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_895_, lean_object* v_modifyRing_896_, lean_object* v_toBind_897_, lean_object* v_intCastFn_898_){
_start:
{
lean_object* v___f_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_inc_ref(v_intCastFn_898_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_899_, 0, v_intCastFn_898_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_900_, 0, v_toPure_895_);
lean_closure_set(v___f_900_, 1, v_intCastFn_898_);
v___x_901_ = lean_apply_1(v_modifyRing_896_, v___f_899_);
v___x_902_ = lean_apply_4(v_toBind_897_, lean_box(0), lean_box(0), v___x_901_, v___f_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_type_906_, lean_object* v_canonExpr_907_, lean_object* v_toBind_908_, lean_object* v___f_909_, lean_object* v_inst_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_911_ = l_Lean_Name_mkStr2(v___x_903_, v___x_904_);
v___x_912_ = l_Lean_mkConst(v___x_911_, v___x_905_);
v___x_913_ = l_Lean_mkAppB(v___x_912_, v_type_906_, v_inst_910_);
v___x_914_ = lean_apply_1(v_canonExpr_907_, v___x_913_);
v___x_915_ = lean_apply_4(v_toBind_908_, lean_box(0), lean_box(0), v___x_914_, v___f_909_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_921_, lean_object* v_inst_x27_922_, lean_object* v_toBind_923_, lean_object* v___f_924_, lean_object* v___f_925_, lean_object* v_inst_926_, lean_object* v_____do__lift_927_){
_start:
{
if (lean_obj_tag(v_____do__lift_927_) == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec(v_inst_926_);
lean_dec(v___f_925_);
v___x_928_ = lean_apply_2(v_toPure_921_, lean_box(0), v_inst_x27_922_);
v___x_929_ = lean_apply_4(v_toBind_923_, lean_box(0), lean_box(0), v___x_928_, v___f_924_);
return v___x_929_;
}
else
{
lean_object* v_val_930_; lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v___f_924_);
v_val_930_ = lean_ctor_get(v_____do__lift_927_, 0);
lean_inc_n(v_val_930_, 2);
lean_dec_ref_known(v_____do__lift_927_, 1);
lean_inc(v_toBind_923_);
v___f_931_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_931_, 0, v_toPure_921_);
lean_closure_set(v___f_931_, 1, v_val_930_);
lean_closure_set(v___f_931_, 2, v_toBind_923_);
lean_closure_set(v___f_931_, 3, v___f_925_);
v___x_932_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_933_, 0, v___x_932_);
lean_closure_set(v___x_933_, 1, v_val_930_);
lean_closure_set(v___x_933_, 2, v_inst_x27_922_);
v___x_934_ = lean_apply_2(v_inst_926_, lean_box(0), v___x_933_);
v___x_935_ = lean_apply_4(v_toBind_923_, lean_box(0), lean_box(0), v___x_934_, v___f_931_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_945_, lean_object* v_inst_946_, lean_object* v_toBind_947_, lean_object* v___f_948_, lean_object* v_inst_949_, lean_object* v_ring_950_){
_start:
{
lean_object* v_intCastFn_x3f_951_; 
v_intCastFn_x3f_951_ = lean_ctor_get(v_ring_950_, 11);
if (lean_obj_tag(v_intCastFn_x3f_951_) == 1)
{
lean_object* v_val_952_; lean_object* v___x_953_; 
lean_inc_ref(v_intCastFn_x3f_951_);
lean_dec_ref(v_ring_950_);
lean_dec(v_inst_949_);
lean_dec(v___f_948_);
lean_dec(v_toBind_947_);
lean_dec_ref(v_inst_946_);
v_val_952_ = lean_ctor_get(v_intCastFn_x3f_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v_intCastFn_x3f_951_, 1);
v___x_953_ = lean_apply_2(v_toPure_945_, lean_box(0), v_val_952_);
return v___x_953_;
}
else
{
lean_object* v_type_954_; lean_object* v_u_955_; lean_object* v_ringInst_956_; lean_object* v_canonExpr_957_; lean_object* v_synthInstance_x3f_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_979_; 
v_type_954_ = lean_ctor_get(v_ring_950_, 1);
lean_inc_ref(v_type_954_);
v_u_955_ = lean_ctor_get(v_ring_950_, 2);
lean_inc(v_u_955_);
v_ringInst_956_ = lean_ctor_get(v_ring_950_, 3);
lean_inc_ref(v_ringInst_956_);
lean_dec_ref(v_ring_950_);
v_canonExpr_957_ = lean_ctor_get(v_inst_946_, 0);
v_synthInstance_x3f_958_ = lean_ctor_get(v_inst_946_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_inst_946_);
if (v_isSharedCheck_979_ == 0)
{
v___x_960_ = v_inst_946_;
v_isShared_961_ = v_isSharedCheck_979_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_synthInstance_x3f_958_);
lean_inc(v_canonExpr_957_);
lean_dec(v_inst_946_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_979_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_962_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_963_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_964_ = lean_box(0);
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 1);
lean_ctor_set(v___x_960_, 1, v___x_964_);
lean_ctor_set(v___x_960_, 0, v_u_955_);
v___x_966_ = v___x_960_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_u_955_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_978_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; lean_object* v_inst_x27_968_; lean_object* v___x_969_; lean_object* v___f_970_; lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_instType_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_inc_ref_n(v___x_966_, 2);
v___x_967_ = l_Lean_mkConst(v___x_963_, v___x_966_);
lean_inc_ref_n(v_type_954_, 2);
v_inst_x27_968_ = l_Lean_mkAppB(v___x_967_, v_type_954_, v_ringInst_956_);
v___x_969_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_947_, 2);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_970_, 0, v___x_969_);
lean_closure_set(v___f_970_, 1, v___x_962_);
lean_closure_set(v___f_970_, 2, v___x_966_);
lean_closure_set(v___f_970_, 3, v_type_954_);
lean_closure_set(v___f_970_, 4, v_canonExpr_957_);
lean_closure_set(v___f_970_, 5, v_toBind_947_);
lean_closure_set(v___f_970_, 6, v___f_948_);
v___f_971_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_971_, 0, v___f_970_);
lean_inc_ref(v___f_971_);
v___f_972_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_972_, 0, v_toPure_945_);
lean_closure_set(v___f_972_, 1, v_inst_x27_968_);
lean_closure_set(v___f_972_, 2, v_toBind_947_);
lean_closure_set(v___f_972_, 3, v___f_971_);
lean_closure_set(v___f_972_, 4, v___f_971_);
lean_closure_set(v___f_972_, 5, v_inst_949_);
v___x_973_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_974_ = l_Lean_mkConst(v___x_973_, v___x_966_);
v_instType_975_ = l_Lean_Expr_app___override(v___x_974_, v_type_954_);
v___x_976_ = lean_apply_1(v_synthInstance_x3f_958_, v_instType_975_);
v___x_977_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_976_, v___f_972_);
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_inst_983_){
_start:
{
lean_object* v_toApplicative_984_; lean_object* v_toBind_985_; lean_object* v_getRing_986_; lean_object* v_modifyRing_987_; lean_object* v_toPure_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___x_991_; 
v_toApplicative_984_ = lean_ctor_get(v_inst_981_, 0);
lean_inc_ref(v_toApplicative_984_);
v_toBind_985_ = lean_ctor_get(v_inst_981_, 1);
lean_inc_n(v_toBind_985_, 3);
lean_dec_ref(v_inst_981_);
v_getRing_986_ = lean_ctor_get(v_inst_983_, 0);
lean_inc(v_getRing_986_);
v_modifyRing_987_ = lean_ctor_get(v_inst_983_, 1);
lean_inc(v_modifyRing_987_);
lean_dec_ref(v_inst_983_);
v_toPure_988_ = lean_ctor_get(v_toApplicative_984_, 1);
lean_inc_n(v_toPure_988_, 2);
lean_dec_ref(v_toApplicative_984_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_989_, 0, v_toPure_988_);
lean_closure_set(v___f_989_, 1, v_modifyRing_987_);
lean_closure_set(v___f_989_, 2, v_toBind_985_);
v___f_990_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_990_, 0, v_toPure_988_);
lean_closure_set(v___f_990_, 1, v_inst_982_);
lean_closure_set(v___f_990_, 2, v_toBind_985_);
lean_closure_set(v___f_990_, 3, v___f_989_);
lean_closure_set(v___f_990_, 4, v_inst_980_);
v___x_991_ = lean_apply_4(v_toBind_985_, lean_box(0), lean_box(0), v_getRing_986_, v___f_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_inst_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_993_, v_inst_994_, v_inst_995_, v_inst_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_998_, lean_object* v_s_999_){
_start:
{
lean_object* v_id_1000_; lean_object* v_type_1001_; lean_object* v_u_1002_; lean_object* v_ringInst_1003_; lean_object* v_semiringInst_1004_; lean_object* v_charInst_x3f_1005_; lean_object* v_addFn_x3f_1006_; lean_object* v_mulFn_x3f_1007_; lean_object* v_subFn_x3f_1008_; lean_object* v_negFn_x3f_1009_; lean_object* v_powFn_x3f_1010_; lean_object* v_intCastFn_x3f_1011_; lean_object* v_one_x3f_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_id_1000_ = lean_ctor_get(v_s_999_, 0);
v_type_1001_ = lean_ctor_get(v_s_999_, 1);
v_u_1002_ = lean_ctor_get(v_s_999_, 2);
v_ringInst_1003_ = lean_ctor_get(v_s_999_, 3);
v_semiringInst_1004_ = lean_ctor_get(v_s_999_, 4);
v_charInst_x3f_1005_ = lean_ctor_get(v_s_999_, 5);
v_addFn_x3f_1006_ = lean_ctor_get(v_s_999_, 6);
v_mulFn_x3f_1007_ = lean_ctor_get(v_s_999_, 7);
v_subFn_x3f_1008_ = lean_ctor_get(v_s_999_, 8);
v_negFn_x3f_1009_ = lean_ctor_get(v_s_999_, 9);
v_powFn_x3f_1010_ = lean_ctor_get(v_s_999_, 10);
v_intCastFn_x3f_1011_ = lean_ctor_get(v_s_999_, 11);
v_one_x3f_1012_ = lean_ctor_get(v_s_999_, 13);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_s_999_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_s_999_, 12);
lean_dec(v_unused_1021_);
v___x_1014_ = v_s_999_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_one_x3f_1012_);
lean_inc(v_intCastFn_x3f_1011_);
lean_inc(v_powFn_x3f_1010_);
lean_inc(v_negFn_x3f_1009_);
lean_inc(v_subFn_x3f_1008_);
lean_inc(v_mulFn_x3f_1007_);
lean_inc(v_addFn_x3f_1006_);
lean_inc(v_charInst_x3f_1005_);
lean_inc(v_semiringInst_1004_);
lean_inc(v_ringInst_1003_);
lean_inc(v_u_1002_);
lean_inc(v_type_1001_);
lean_inc(v_id_1000_);
lean_dec(v_s_999_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_natCastFn_998_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 12, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_id_1000_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_type_1001_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_u_1002_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_ringInst_1003_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_semiringInst_1004_);
lean_ctor_set(v_reuseFailAlloc_1019_, 5, v_charInst_x3f_1005_);
lean_ctor_set(v_reuseFailAlloc_1019_, 6, v_addFn_x3f_1006_);
lean_ctor_set(v_reuseFailAlloc_1019_, 7, v_mulFn_x3f_1007_);
lean_ctor_set(v_reuseFailAlloc_1019_, 8, v_subFn_x3f_1008_);
lean_ctor_set(v_reuseFailAlloc_1019_, 9, v_negFn_x3f_1009_);
lean_ctor_set(v_reuseFailAlloc_1019_, 10, v_powFn_x3f_1010_);
lean_ctor_set(v_reuseFailAlloc_1019_, 11, v_intCastFn_x3f_1011_);
lean_ctor_set(v_reuseFailAlloc_1019_, 12, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1019_, 13, v_one_x3f_1012_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1022_, lean_object* v_natCastFn_1023_, lean_object* v_____r_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_apply_2(v_toPure_1022_, lean_box(0), v_natCastFn_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1026_, lean_object* v_modifyRing_1027_, lean_object* v_toBind_1028_, lean_object* v_natCastFn_1029_){
_start:
{
lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_inc_ref(v_natCastFn_1029_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1030_, 0, v_natCastFn_1029_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1031_, 0, v_toPure_1026_);
lean_closure_set(v___f_1031_, 1, v_natCastFn_1029_);
v___x_1032_ = lean_apply_1(v_modifyRing_1027_, v___f_1030_);
v___x_1033_ = lean_apply_4(v_toBind_1028_, lean_box(0), lean_box(0), v___x_1032_, v___f_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_toBind_1038_, lean_object* v___f_1039_, lean_object* v_ring_1040_){
_start:
{
lean_object* v_natCastFn_x3f_1041_; 
v_natCastFn_x3f_1041_ = lean_ctor_get(v_ring_1040_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1041_) == 1)
{
lean_object* v_val_1042_; lean_object* v___x_1043_; 
lean_inc_ref(v_natCastFn_x3f_1041_);
lean_dec_ref(v_ring_1040_);
lean_dec(v___f_1039_);
lean_dec(v_toBind_1038_);
lean_dec_ref(v_inst_1037_);
lean_dec_ref(v_inst_1036_);
lean_dec(v_inst_1035_);
v_val_1042_ = lean_ctor_get(v_natCastFn_x3f_1041_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v_natCastFn_x3f_1041_, 1);
v___x_1043_ = lean_apply_2(v_toPure_1034_, lean_box(0), v_val_1042_);
return v___x_1043_;
}
else
{
lean_object* v_type_1044_; lean_object* v_u_1045_; lean_object* v_semiringInst_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_toPure_1034_);
v_type_1044_ = lean_ctor_get(v_ring_1040_, 1);
lean_inc_ref(v_type_1044_);
v_u_1045_ = lean_ctor_get(v_ring_1040_, 2);
lean_inc(v_u_1045_);
v_semiringInst_1046_ = lean_ctor_get(v_ring_1040_, 4);
lean_inc_ref(v_semiringInst_1046_);
lean_dec_ref(v_ring_1040_);
v___x_1047_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1035_, v_inst_1036_, v_inst_1037_, v_u_1045_, v_type_1044_, v_semiringInst_1046_);
v___x_1048_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v___x_1047_, v___f_1039_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_){
_start:
{
lean_object* v_toApplicative_1053_; lean_object* v_toBind_1054_; lean_object* v_getRing_1055_; lean_object* v_modifyRing_1056_; lean_object* v_toPure_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
v_toApplicative_1053_ = lean_ctor_get(v_inst_1050_, 0);
v_toBind_1054_ = lean_ctor_get(v_inst_1050_, 1);
lean_inc_n(v_toBind_1054_, 3);
v_getRing_1055_ = lean_ctor_get(v_inst_1052_, 0);
lean_inc(v_getRing_1055_);
v_modifyRing_1056_ = lean_ctor_get(v_inst_1052_, 1);
lean_inc(v_modifyRing_1056_);
lean_dec_ref(v_inst_1052_);
v_toPure_1057_ = lean_ctor_get(v_toApplicative_1053_, 1);
lean_inc_n(v_toPure_1057_, 2);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1058_, 0, v_toPure_1057_);
lean_closure_set(v___f_1058_, 1, v_modifyRing_1056_);
lean_closure_set(v___f_1058_, 2, v_toBind_1054_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1059_, 0, v_toPure_1057_);
lean_closure_set(v___f_1059_, 1, v_inst_1049_);
lean_closure_set(v___f_1059_, 2, v_inst_1050_);
lean_closure_set(v___f_1059_, 3, v_inst_1051_);
lean_closure_set(v___f_1059_, 4, v_toBind_1054_);
lean_closure_set(v___f_1059_, 5, v___f_1058_);
v___x_1060_ = lean_apply_4(v_toBind_1054_, lean_box(0), lean_box(0), v_getRing_1055_, v___f_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1062_, v_inst_1063_, v_inst_1064_, v_inst_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1067_, lean_object* v_s_1068_){
_start:
{
lean_object* v_toRing_1069_; lean_object* v_semiringId_x3f_1070_; lean_object* v_commSemiringInst_1071_; lean_object* v_commRingInst_1072_; lean_object* v_noZeroDivInst_x3f_1073_; lean_object* v_fieldInst_x3f_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_toRing_1069_ = lean_ctor_get(v_s_1068_, 0);
v_semiringId_x3f_1070_ = lean_ctor_get(v_s_1068_, 2);
v_commSemiringInst_1071_ = lean_ctor_get(v_s_1068_, 3);
v_commRingInst_1072_ = lean_ctor_get(v_s_1068_, 4);
v_noZeroDivInst_x3f_1073_ = lean_ctor_get(v_s_1068_, 5);
v_fieldInst_x3f_1074_ = lean_ctor_get(v_s_1068_, 6);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_s_1068_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_s_1068_, 1);
lean_dec(v_unused_1083_);
v___x_1076_ = v_s_1068_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_fieldInst_x3f_1074_);
lean_inc(v_noZeroDivInst_x3f_1073_);
lean_inc(v_commRingInst_1072_);
lean_inc(v_commSemiringInst_1071_);
lean_inc(v_semiringId_x3f_1070_);
lean_inc(v_toRing_1069_);
lean_dec(v_s_1068_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_invFn_1067_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_toRing_1069_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_semiringId_x3f_1070_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_commSemiringInst_1071_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v_commRingInst_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 5, v_noZeroDivInst_x3f_1073_);
lean_ctor_set(v_reuseFailAlloc_1081_, 6, v_fieldInst_x3f_1074_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1084_, lean_object* v_invFn_1085_, lean_object* v_____r_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_apply_2(v_toPure_1084_, lean_box(0), v_invFn_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1088_, lean_object* v_modifyCommRing_1089_, lean_object* v_toBind_1090_, lean_object* v_invFn_1091_){
_start:
{
lean_object* v___f_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_inc_ref(v_invFn_1091_);
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1092_, 0, v_invFn_1091_);
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1093_, 0, v_toPure_1088_);
lean_closure_set(v___f_1093_, 1, v_invFn_1091_);
v___x_1094_ = lean_apply_1(v_modifyCommRing_1089_, v___f_1092_);
v___x_1095_ = lean_apply_4(v_toBind_1090_, lean_box(0), lean_box(0), v___x_1094_, v___f_1093_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_toBind_1118_, lean_object* v___f_1119_, lean_object* v_ring_1120_){
_start:
{
lean_object* v_fieldInst_x3f_1121_; 
v_fieldInst_x3f_1121_ = lean_ctor_get(v_ring_1120_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1121_) == 1)
{
lean_object* v_invFn_x3f_1122_; 
lean_inc_ref(v_fieldInst_x3f_1121_);
v_invFn_x3f_1122_ = lean_ctor_get(v_ring_1120_, 1);
if (lean_obj_tag(v_invFn_x3f_1122_) == 1)
{
lean_object* v_val_1123_; lean_object* v___x_1124_; 
lean_inc_ref(v_invFn_x3f_1122_);
lean_dec_ref_known(v_fieldInst_x3f_1121_, 1);
lean_dec_ref(v_ring_1120_);
lean_dec(v___f_1119_);
lean_dec(v_toBind_1118_);
lean_dec_ref(v_inst_1117_);
lean_dec_ref(v_inst_1116_);
lean_dec_ref(v_inst_1115_);
lean_dec(v_inst_1114_);
v_val_1123_ = lean_ctor_get(v_invFn_x3f_1122_, 0);
lean_inc(v_val_1123_);
lean_dec_ref_known(v_invFn_x3f_1122_, 1);
v___x_1124_ = lean_apply_2(v_toPure_1113_, lean_box(0), v_val_1123_);
return v___x_1124_;
}
else
{
lean_object* v_toRing_1125_; lean_object* v_val_1126_; lean_object* v_type_1127_; lean_object* v_u_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_expectedInst_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v_toPure_1113_);
v_toRing_1125_ = lean_ctor_get(v_ring_1120_, 0);
lean_inc_ref(v_toRing_1125_);
lean_dec_ref(v_ring_1120_);
v_val_1126_ = lean_ctor_get(v_fieldInst_x3f_1121_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v_fieldInst_x3f_1121_, 1);
v_type_1127_ = lean_ctor_get(v_toRing_1125_, 1);
lean_inc_ref_n(v_type_1127_, 2);
v_u_1128_ = lean_ctor_get(v_toRing_1125_, 2);
lean_inc_n(v_u_1128_, 2);
lean_dec_ref(v_toRing_1125_);
v___x_1129_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_u_1128_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_mkConst(v___x_1129_, v___x_1131_);
v_expectedInst_1133_ = l_Lean_mkAppB(v___x_1132_, v_type_1127_, v_val_1126_);
v___x_1134_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1135_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1136_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1114_, v_inst_1115_, v_inst_1116_, v_inst_1117_, v_type_1127_, v_u_1128_, v___x_1134_, v___x_1135_, v_expectedInst_1133_);
v___x_1137_ = lean_apply_4(v_toBind_1118_, lean_box(0), lean_box(0), v___x_1136_, v___f_1119_);
return v___x_1137_;
}
}
else
{
lean_object* v_toRing_1138_; lean_object* v_type_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v___f_1119_);
lean_dec(v_toBind_1118_);
lean_dec_ref(v_inst_1117_);
lean_dec(v_inst_1114_);
lean_dec(v_toPure_1113_);
v_toRing_1138_ = lean_ctor_get(v_ring_1120_, 0);
lean_inc_ref(v_toRing_1138_);
lean_dec_ref(v_ring_1120_);
v_type_1139_ = lean_ctor_get(v_toRing_1138_, 1);
lean_inc_ref(v_type_1139_);
lean_dec_ref(v_toRing_1138_);
v___x_1140_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1141_ = l_Lean_indentExpr(v_type_1139_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_throwError___redArg(v_inst_1116_, v_inst_1115_, v___x_1142_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_){
_start:
{
lean_object* v_toApplicative_1149_; lean_object* v_toBind_1150_; lean_object* v_getCommRing_1151_; lean_object* v_modifyCommRing_1152_; lean_object* v_toPure_1153_; lean_object* v___f_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; 
v_toApplicative_1149_ = lean_ctor_get(v_inst_1146_, 0);
v_toBind_1150_ = lean_ctor_get(v_inst_1146_, 1);
lean_inc_n(v_toBind_1150_, 3);
v_getCommRing_1151_ = lean_ctor_get(v_inst_1148_, 0);
lean_inc(v_getCommRing_1151_);
v_modifyCommRing_1152_ = lean_ctor_get(v_inst_1148_, 1);
lean_inc(v_modifyCommRing_1152_);
lean_dec_ref(v_inst_1148_);
v_toPure_1153_ = lean_ctor_get(v_toApplicative_1149_, 1);
lean_inc_n(v_toPure_1153_, 2);
v___f_1154_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1154_, 0, v_toPure_1153_);
lean_closure_set(v___f_1154_, 1, v_modifyCommRing_1152_);
lean_closure_set(v___f_1154_, 2, v_toBind_1150_);
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1155_, 0, v_toPure_1153_);
lean_closure_set(v___f_1155_, 1, v_inst_1144_);
lean_closure_set(v___f_1155_, 2, v_inst_1145_);
lean_closure_set(v___f_1155_, 3, v_inst_1146_);
lean_closure_set(v___f_1155_, 4, v_inst_1147_);
lean_closure_set(v___f_1155_, 5, v_toBind_1150_);
lean_closure_set(v___f_1155_, 6, v___f_1154_);
v___x_1156_ = lean_apply_4(v_toBind_1150_, lean_box(0), lean_box(0), v_getCommRing_1151_, v___f_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1158_, v_inst_1159_, v_inst_1160_, v_inst_1161_, v_inst_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_1164_, lean_object* v_s_1165_){
_start:
{
lean_object* v_id_1166_; lean_object* v_type_1167_; lean_object* v_u_1168_; lean_object* v_semiringInst_1169_; lean_object* v_mulFn_x3f_1170_; lean_object* v_powFn_x3f_1171_; lean_object* v_natCastFn_x3f_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
v_id_1166_ = lean_ctor_get(v_s_1165_, 0);
v_type_1167_ = lean_ctor_get(v_s_1165_, 1);
v_u_1168_ = lean_ctor_get(v_s_1165_, 2);
v_semiringInst_1169_ = lean_ctor_get(v_s_1165_, 3);
v_mulFn_x3f_1170_ = lean_ctor_get(v_s_1165_, 5);
v_powFn_x3f_1171_ = lean_ctor_get(v_s_1165_, 6);
v_natCastFn_x3f_1172_ = lean_ctor_get(v_s_1165_, 7);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_s_1165_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v_s_1165_, 4);
lean_dec(v_unused_1181_);
v___x_1174_ = v_s_1165_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_natCastFn_x3f_1172_);
lean_inc(v_powFn_x3f_1171_);
lean_inc(v_mulFn_x3f_1170_);
lean_inc(v_semiringInst_1169_);
lean_inc(v_u_1168_);
lean_inc(v_type_1167_);
lean_inc(v_id_1166_);
lean_dec(v_s_1165_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_addFn_1164_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v___x_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_id_1166_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_type_1167_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_u_1168_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_semiringInst_1169_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_mulFn_x3f_1170_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_powFn_x3f_1171_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v_natCastFn_x3f_1172_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_1182_, lean_object* v_modifySemiring_1183_, lean_object* v_toBind_1184_, lean_object* v_addFn_1185_){
_start:
{
lean_object* v___f_1186_; lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_inc_ref(v_addFn_1185_);
v___f_1186_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1186_, 0, v_addFn_1185_);
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1187_, 0, v_toPure_1182_);
lean_closure_set(v___f_1187_, 1, v_addFn_1185_);
v___x_1188_ = lean_apply_1(v_modifySemiring_1183_, v___f_1186_);
v___x_1189_ = lean_apply_4(v_toBind_1184_, lean_box(0), lean_box(0), v___x_1188_, v___f_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_toBind_1195_, lean_object* v___f_1196_, lean_object* v_sr_1197_){
_start:
{
lean_object* v_addFn_x3f_1198_; 
v_addFn_x3f_1198_ = lean_ctor_get(v_sr_1197_, 4);
if (lean_obj_tag(v_addFn_x3f_1198_) == 1)
{
lean_object* v_val_1199_; lean_object* v___x_1200_; 
lean_inc_ref(v_addFn_x3f_1198_);
lean_dec_ref(v_sr_1197_);
lean_dec(v___f_1196_);
lean_dec(v_toBind_1195_);
lean_dec_ref(v_inst_1194_);
lean_dec_ref(v_inst_1193_);
lean_dec_ref(v_inst_1192_);
lean_dec(v_inst_1191_);
v_val_1199_ = lean_ctor_get(v_addFn_x3f_1198_, 0);
lean_inc(v_val_1199_);
lean_dec_ref_known(v_addFn_x3f_1198_, 1);
v___x_1200_ = lean_apply_2(v_toPure_1190_, lean_box(0), v_val_1199_);
return v___x_1200_;
}
else
{
lean_object* v_type_1201_; lean_object* v_u_1202_; lean_object* v_semiringInst_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_expectedInst_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v_toPure_1190_);
v_type_1201_ = lean_ctor_get(v_sr_1197_, 1);
lean_inc_ref_n(v_type_1201_, 3);
v_u_1202_ = lean_ctor_get(v_sr_1197_, 2);
lean_inc_n(v_u_1202_, 2);
v_semiringInst_1203_ = lean_ctor_get(v_sr_1197_, 3);
lean_inc_ref(v_semiringInst_1203_);
lean_dec_ref(v_sr_1197_);
v___x_1204_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_u_1202_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
lean_inc_ref(v___x_1206_);
v___x_1207_ = l_Lean_mkConst(v___x_1204_, v___x_1206_);
v___x_1208_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1209_ = l_Lean_mkConst(v___x_1208_, v___x_1206_);
v___x_1210_ = l_Lean_mkAppB(v___x_1209_, v_type_1201_, v_semiringInst_1203_);
v_expectedInst_1211_ = l_Lean_mkAppB(v___x_1207_, v_type_1201_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1213_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1214_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1191_, v_inst_1192_, v_inst_1193_, v_inst_1194_, v_type_1201_, v_u_1202_, v___x_1212_, v___x_1213_, v_expectedInst_1211_);
v___x_1215_ = lean_apply_4(v_toBind_1195_, lean_box(0), lean_box(0), v___x_1214_, v___f_1196_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_){
_start:
{
lean_object* v_toApplicative_1221_; lean_object* v_toBind_1222_; lean_object* v_getSemiring_1223_; lean_object* v_modifySemiring_1224_; lean_object* v_toPure_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; 
v_toApplicative_1221_ = lean_ctor_get(v_inst_1218_, 0);
v_toBind_1222_ = lean_ctor_get(v_inst_1218_, 1);
lean_inc_n(v_toBind_1222_, 3);
v_getSemiring_1223_ = lean_ctor_get(v_inst_1220_, 0);
lean_inc(v_getSemiring_1223_);
v_modifySemiring_1224_ = lean_ctor_get(v_inst_1220_, 1);
lean_inc(v_modifySemiring_1224_);
lean_dec_ref(v_inst_1220_);
v_toPure_1225_ = lean_ctor_get(v_toApplicative_1221_, 1);
lean_inc_n(v_toPure_1225_, 2);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1226_, 0, v_toPure_1225_);
lean_closure_set(v___f_1226_, 1, v_modifySemiring_1224_);
lean_closure_set(v___f_1226_, 2, v_toBind_1222_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1227_, 0, v_toPure_1225_);
lean_closure_set(v___f_1227_, 1, v_inst_1216_);
lean_closure_set(v___f_1227_, 2, v_inst_1217_);
lean_closure_set(v___f_1227_, 3, v_inst_1218_);
lean_closure_set(v___f_1227_, 4, v_inst_1219_);
lean_closure_set(v___f_1227_, 5, v_toBind_1222_);
lean_closure_set(v___f_1227_, 6, v___f_1226_);
v___x_1228_ = lean_apply_4(v_toBind_1222_, lean_box(0), lean_box(0), v_getSemiring_1223_, v___f_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_inst_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_1236_, lean_object* v_s_1237_){
_start:
{
lean_object* v_id_1238_; lean_object* v_type_1239_; lean_object* v_u_1240_; lean_object* v_semiringInst_1241_; lean_object* v_addFn_x3f_1242_; lean_object* v_powFn_x3f_1243_; lean_object* v_natCastFn_x3f_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1252_; 
v_id_1238_ = lean_ctor_get(v_s_1237_, 0);
v_type_1239_ = lean_ctor_get(v_s_1237_, 1);
v_u_1240_ = lean_ctor_get(v_s_1237_, 2);
v_semiringInst_1241_ = lean_ctor_get(v_s_1237_, 3);
v_addFn_x3f_1242_ = lean_ctor_get(v_s_1237_, 4);
v_powFn_x3f_1243_ = lean_ctor_get(v_s_1237_, 6);
v_natCastFn_x3f_1244_ = lean_ctor_get(v_s_1237_, 7);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_s_1237_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_s_1237_, 5);
lean_dec(v_unused_1253_);
v___x_1246_ = v_s_1237_;
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_natCastFn_x3f_1244_);
lean_inc(v_powFn_x3f_1243_);
lean_inc(v_addFn_x3f_1242_);
lean_inc(v_semiringInst_1241_);
lean_inc(v_u_1240_);
lean_inc(v_type_1239_);
lean_inc(v_id_1238_);
lean_dec(v_s_1237_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_mulFn_1236_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 5, v___x_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_id_1238_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_type_1239_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_u_1240_);
lean_ctor_set(v_reuseFailAlloc_1251_, 3, v_semiringInst_1241_);
lean_ctor_set(v_reuseFailAlloc_1251_, 4, v_addFn_x3f_1242_);
lean_ctor_set(v_reuseFailAlloc_1251_, 5, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1251_, 6, v_powFn_x3f_1243_);
lean_ctor_set(v_reuseFailAlloc_1251_, 7, v_natCastFn_x3f_1244_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1254_, lean_object* v_modifySemiring_1255_, lean_object* v_toBind_1256_, lean_object* v_mulFn_1257_){
_start:
{
lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_inc_ref(v_mulFn_1257_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1258_, 0, v_mulFn_1257_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1259_, 0, v_toPure_1254_);
lean_closure_set(v___f_1259_, 1, v_mulFn_1257_);
v___x_1260_ = lean_apply_1(v_modifySemiring_1255_, v___f_1258_);
v___x_1261_ = lean_apply_4(v_toBind_1256_, lean_box(0), lean_box(0), v___x_1260_, v___f_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_toBind_1267_, lean_object* v___f_1268_, lean_object* v_sr_1269_){
_start:
{
lean_object* v_mulFn_x3f_1270_; 
v_mulFn_x3f_1270_ = lean_ctor_get(v_sr_1269_, 5);
if (lean_obj_tag(v_mulFn_x3f_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1272_; 
lean_inc_ref(v_mulFn_x3f_1270_);
lean_dec_ref(v_sr_1269_);
lean_dec(v___f_1268_);
lean_dec(v_toBind_1267_);
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
lean_dec_ref(v_inst_1264_);
lean_dec(v_inst_1263_);
v_val_1271_ = lean_ctor_get(v_mulFn_x3f_1270_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v_mulFn_x3f_1270_, 1);
v___x_1272_ = lean_apply_2(v_toPure_1262_, lean_box(0), v_val_1271_);
return v___x_1272_;
}
else
{
lean_object* v_type_1273_; lean_object* v_u_1274_; lean_object* v_semiringInst_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_expectedInst_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_toPure_1262_);
v_type_1273_ = lean_ctor_get(v_sr_1269_, 1);
lean_inc_ref_n(v_type_1273_, 3);
v_u_1274_ = lean_ctor_get(v_sr_1269_, 2);
lean_inc_n(v_u_1274_, 2);
v_semiringInst_1275_ = lean_ctor_get(v_sr_1269_, 3);
lean_inc_ref(v_semiringInst_1275_);
lean_dec_ref(v_sr_1269_);
v___x_1276_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_u_1274_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
lean_inc_ref(v___x_1278_);
v___x_1279_ = l_Lean_mkConst(v___x_1276_, v___x_1278_);
v___x_1280_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1281_ = l_Lean_mkConst(v___x_1280_, v___x_1278_);
v___x_1282_ = l_Lean_mkAppB(v___x_1281_, v_type_1273_, v_semiringInst_1275_);
v_expectedInst_1283_ = l_Lean_mkAppB(v___x_1279_, v_type_1273_, v___x_1282_);
v___x_1284_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1285_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1286_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1263_, v_inst_1264_, v_inst_1265_, v_inst_1266_, v_type_1273_, v_u_1274_, v___x_1284_, v___x_1285_, v_expectedInst_1283_);
v___x_1287_ = lean_apply_4(v_toBind_1267_, lean_box(0), lean_box(0), v___x_1286_, v___f_1268_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_){
_start:
{
lean_object* v_toApplicative_1293_; lean_object* v_toBind_1294_; lean_object* v_getSemiring_1295_; lean_object* v_modifySemiring_1296_; lean_object* v_toPure_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; 
v_toApplicative_1293_ = lean_ctor_get(v_inst_1290_, 0);
v_toBind_1294_ = lean_ctor_get(v_inst_1290_, 1);
lean_inc_n(v_toBind_1294_, 3);
v_getSemiring_1295_ = lean_ctor_get(v_inst_1292_, 0);
lean_inc(v_getSemiring_1295_);
v_modifySemiring_1296_ = lean_ctor_get(v_inst_1292_, 1);
lean_inc(v_modifySemiring_1296_);
lean_dec_ref(v_inst_1292_);
v_toPure_1297_ = lean_ctor_get(v_toApplicative_1293_, 1);
lean_inc_n(v_toPure_1297_, 2);
v___f_1298_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1298_, 0, v_toPure_1297_);
lean_closure_set(v___f_1298_, 1, v_modifySemiring_1296_);
lean_closure_set(v___f_1298_, 2, v_toBind_1294_);
v___f_1299_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1299_, 0, v_toPure_1297_);
lean_closure_set(v___f_1299_, 1, v_inst_1288_);
lean_closure_set(v___f_1299_, 2, v_inst_1289_);
lean_closure_set(v___f_1299_, 3, v_inst_1290_);
lean_closure_set(v___f_1299_, 4, v_inst_1291_);
lean_closure_set(v___f_1299_, 5, v_toBind_1294_);
lean_closure_set(v___f_1299_, 6, v___f_1298_);
v___x_1300_ = lean_apply_4(v_toBind_1294_, lean_box(0), lean_box(0), v_getSemiring_1295_, v___f_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1302_, v_inst_1303_, v_inst_1304_, v_inst_1305_, v_inst_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1308_, lean_object* v_s_1309_){
_start:
{
lean_object* v_id_1310_; lean_object* v_type_1311_; lean_object* v_u_1312_; lean_object* v_semiringInst_1313_; lean_object* v_addFn_x3f_1314_; lean_object* v_mulFn_x3f_1315_; lean_object* v_natCastFn_x3f_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_id_1310_ = lean_ctor_get(v_s_1309_, 0);
v_type_1311_ = lean_ctor_get(v_s_1309_, 1);
v_u_1312_ = lean_ctor_get(v_s_1309_, 2);
v_semiringInst_1313_ = lean_ctor_get(v_s_1309_, 3);
v_addFn_x3f_1314_ = lean_ctor_get(v_s_1309_, 4);
v_mulFn_x3f_1315_ = lean_ctor_get(v_s_1309_, 5);
v_natCastFn_x3f_1316_ = lean_ctor_get(v_s_1309_, 7);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_s_1309_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_s_1309_, 6);
lean_dec(v_unused_1325_);
v___x_1318_ = v_s_1309_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_natCastFn_x3f_1316_);
lean_inc(v_mulFn_x3f_1315_);
lean_inc(v_addFn_x3f_1314_);
lean_inc(v_semiringInst_1313_);
lean_inc(v_u_1312_);
lean_inc(v_type_1311_);
lean_inc(v_id_1310_);
lean_dec(v_s_1309_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_powFn_1308_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 6, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_id_1310_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_type_1311_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_u_1312_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_semiringInst_1313_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_addFn_x3f_1314_);
lean_ctor_set(v_reuseFailAlloc_1323_, 5, v_mulFn_x3f_1315_);
lean_ctor_set(v_reuseFailAlloc_1323_, 6, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1323_, 7, v_natCastFn_x3f_1316_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1326_, lean_object* v_modifySemiring_1327_, lean_object* v_toBind_1328_, lean_object* v_powFn_1329_){
_start:
{
lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_inc_ref(v_powFn_1329_);
v___f_1330_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1330_, 0, v_powFn_1329_);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1331_, 0, v_toPure_1326_);
lean_closure_set(v___f_1331_, 1, v_powFn_1329_);
v___x_1332_ = lean_apply_1(v_modifySemiring_1327_, v___f_1330_);
v___x_1333_ = lean_apply_4(v_toBind_1328_, lean_box(0), lean_box(0), v___x_1332_, v___f_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_toBind_1339_, lean_object* v___f_1340_, lean_object* v_sr_1341_){
_start:
{
lean_object* v_powFn_x3f_1342_; 
v_powFn_x3f_1342_ = lean_ctor_get(v_sr_1341_, 6);
if (lean_obj_tag(v_powFn_x3f_1342_) == 1)
{
lean_object* v_val_1343_; lean_object* v___x_1344_; 
lean_inc_ref(v_powFn_x3f_1342_);
lean_dec_ref(v_sr_1341_);
lean_dec(v___f_1340_);
lean_dec(v_toBind_1339_);
lean_dec_ref(v_inst_1338_);
lean_dec_ref(v_inst_1337_);
lean_dec_ref(v_inst_1336_);
lean_dec(v_inst_1335_);
v_val_1343_ = lean_ctor_get(v_powFn_x3f_1342_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v_powFn_x3f_1342_, 1);
v___x_1344_ = lean_apply_2(v_toPure_1334_, lean_box(0), v_val_1343_);
return v___x_1344_;
}
else
{
lean_object* v_type_1345_; lean_object* v_u_1346_; lean_object* v_semiringInst_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v_toPure_1334_);
v_type_1345_ = lean_ctor_get(v_sr_1341_, 1);
lean_inc_ref(v_type_1345_);
v_u_1346_ = lean_ctor_get(v_sr_1341_, 2);
lean_inc(v_u_1346_);
v_semiringInst_1347_ = lean_ctor_get(v_sr_1341_, 3);
lean_inc_ref(v_semiringInst_1347_);
lean_dec_ref(v_sr_1341_);
v___x_1348_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_u_1346_, v_type_1345_, v_semiringInst_1347_);
v___x_1349_ = lean_apply_4(v_toBind_1339_, lean_box(0), lean_box(0), v___x_1348_, v___f_1340_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_){
_start:
{
lean_object* v_toApplicative_1355_; lean_object* v_toBind_1356_; lean_object* v_getSemiring_1357_; lean_object* v_modifySemiring_1358_; lean_object* v_toPure_1359_; lean_object* v___f_1360_; lean_object* v___f_1361_; lean_object* v___x_1362_; 
v_toApplicative_1355_ = lean_ctor_get(v_inst_1352_, 0);
v_toBind_1356_ = lean_ctor_get(v_inst_1352_, 1);
lean_inc_n(v_toBind_1356_, 3);
v_getSemiring_1357_ = lean_ctor_get(v_inst_1354_, 0);
lean_inc(v_getSemiring_1357_);
v_modifySemiring_1358_ = lean_ctor_get(v_inst_1354_, 1);
lean_inc(v_modifySemiring_1358_);
lean_dec_ref(v_inst_1354_);
v_toPure_1359_ = lean_ctor_get(v_toApplicative_1355_, 1);
lean_inc_n(v_toPure_1359_, 2);
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1360_, 0, v_toPure_1359_);
lean_closure_set(v___f_1360_, 1, v_modifySemiring_1358_);
lean_closure_set(v___f_1360_, 2, v_toBind_1356_);
v___f_1361_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1361_, 0, v_toPure_1359_);
lean_closure_set(v___f_1361_, 1, v_inst_1350_);
lean_closure_set(v___f_1361_, 2, v_inst_1351_);
lean_closure_set(v___f_1361_, 3, v_inst_1352_);
lean_closure_set(v___f_1361_, 4, v_inst_1353_);
lean_closure_set(v___f_1361_, 5, v_toBind_1356_);
lean_closure_set(v___f_1361_, 6, v___f_1360_);
v___x_1362_ = lean_apply_4(v_toBind_1356_, lean_box(0), lean_box(0), v_getSemiring_1357_, v___f_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1364_, v_inst_1365_, v_inst_1366_, v_inst_1367_, v_inst_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1370_, lean_object* v_s_1371_){
_start:
{
lean_object* v_id_1372_; lean_object* v_type_1373_; lean_object* v_u_1374_; lean_object* v_semiringInst_1375_; lean_object* v_addFn_x3f_1376_; lean_object* v_mulFn_x3f_1377_; lean_object* v_powFn_x3f_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1386_; 
v_id_1372_ = lean_ctor_get(v_s_1371_, 0);
v_type_1373_ = lean_ctor_get(v_s_1371_, 1);
v_u_1374_ = lean_ctor_get(v_s_1371_, 2);
v_semiringInst_1375_ = lean_ctor_get(v_s_1371_, 3);
v_addFn_x3f_1376_ = lean_ctor_get(v_s_1371_, 4);
v_mulFn_x3f_1377_ = lean_ctor_get(v_s_1371_, 5);
v_powFn_x3f_1378_ = lean_ctor_get(v_s_1371_, 6);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_s_1371_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v_s_1371_, 7);
lean_dec(v_unused_1387_);
v___x_1380_ = v_s_1371_;
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_powFn_x3f_1378_);
lean_inc(v_mulFn_x3f_1377_);
lean_inc(v_addFn_x3f_1376_);
lean_inc(v_semiringInst_1375_);
lean_inc(v_u_1374_);
lean_inc(v_type_1373_);
lean_inc(v_id_1372_);
lean_dec(v_s_1371_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_natCastFn_1370_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 7, v___x_1382_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_id_1372_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_type_1373_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_u_1374_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_semiringInst_1375_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_addFn_x3f_1376_);
lean_ctor_set(v_reuseFailAlloc_1385_, 5, v_mulFn_x3f_1377_);
lean_ctor_set(v_reuseFailAlloc_1385_, 6, v_powFn_x3f_1378_);
lean_ctor_set(v_reuseFailAlloc_1385_, 7, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1388_, lean_object* v_modifySemiring_1389_, lean_object* v_toBind_1390_, lean_object* v_natCastFn_1391_){
_start:
{
lean_object* v___f_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_inc_ref(v_natCastFn_1391_);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1392_, 0, v_natCastFn_1391_);
v___f_1393_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1393_, 0, v_toPure_1388_);
lean_closure_set(v___f_1393_, 1, v_natCastFn_1391_);
v___x_1394_ = lean_apply_1(v_modifySemiring_1389_, v___f_1392_);
v___x_1395_ = lean_apply_4(v_toBind_1390_, lean_box(0), lean_box(0), v___x_1394_, v___f_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_toBind_1400_, lean_object* v___f_1401_, lean_object* v_sr_1402_){
_start:
{
lean_object* v_natCastFn_x3f_1403_; 
v_natCastFn_x3f_1403_ = lean_ctor_get(v_sr_1402_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1403_) == 1)
{
lean_object* v_val_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v_natCastFn_x3f_1403_);
lean_dec_ref(v_sr_1402_);
lean_dec(v___f_1401_);
lean_dec(v_toBind_1400_);
lean_dec_ref(v_inst_1399_);
lean_dec_ref(v_inst_1398_);
lean_dec(v_inst_1397_);
v_val_1404_ = lean_ctor_get(v_natCastFn_x3f_1403_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v_natCastFn_x3f_1403_, 1);
v___x_1405_ = lean_apply_2(v_toPure_1396_, lean_box(0), v_val_1404_);
return v___x_1405_;
}
else
{
lean_object* v_type_1406_; lean_object* v_u_1407_; lean_object* v_semiringInst_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_dec(v_toPure_1396_);
v_type_1406_ = lean_ctor_get(v_sr_1402_, 1);
lean_inc_ref(v_type_1406_);
v_u_1407_ = lean_ctor_get(v_sr_1402_, 2);
lean_inc(v_u_1407_);
v_semiringInst_1408_ = lean_ctor_get(v_sr_1402_, 3);
lean_inc_ref(v_semiringInst_1408_);
lean_dec_ref(v_sr_1402_);
v___x_1409_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1397_, v_inst_1398_, v_inst_1399_, v_u_1407_, v_type_1406_, v_semiringInst_1408_);
v___x_1410_ = lean_apply_4(v_toBind_1400_, lean_box(0), lean_box(0), v___x_1409_, v___f_1401_);
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_){
_start:
{
lean_object* v_toApplicative_1415_; lean_object* v_toBind_1416_; lean_object* v_getSemiring_1417_; lean_object* v_modifySemiring_1418_; lean_object* v_toPure_1419_; lean_object* v___f_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; 
v_toApplicative_1415_ = lean_ctor_get(v_inst_1412_, 0);
v_toBind_1416_ = lean_ctor_get(v_inst_1412_, 1);
lean_inc_n(v_toBind_1416_, 3);
v_getSemiring_1417_ = lean_ctor_get(v_inst_1414_, 0);
lean_inc(v_getSemiring_1417_);
v_modifySemiring_1418_ = lean_ctor_get(v_inst_1414_, 1);
lean_inc(v_modifySemiring_1418_);
lean_dec_ref(v_inst_1414_);
v_toPure_1419_ = lean_ctor_get(v_toApplicative_1415_, 1);
lean_inc_n(v_toPure_1419_, 2);
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1420_, 0, v_toPure_1419_);
lean_closure_set(v___f_1420_, 1, v_modifySemiring_1418_);
lean_closure_set(v___f_1420_, 2, v_toBind_1416_);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1421_, 0, v_toPure_1419_);
lean_closure_set(v___f_1421_, 1, v_inst_1411_);
lean_closure_set(v___f_1421_, 2, v_inst_1412_);
lean_closure_set(v___f_1421_, 3, v_inst_1413_);
lean_closure_set(v___f_1421_, 4, v_toBind_1416_);
lean_closure_set(v___f_1421_, 5, v___f_1420_);
v___x_1422_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v_getSemiring_1417_, v___f_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1424_, v_inst_1425_, v_inst_1426_, v_inst_1427_);
return v___x_1428_;
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
