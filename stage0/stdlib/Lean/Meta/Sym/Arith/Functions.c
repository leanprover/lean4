// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Functions
// Imports: public import Lean.Meta.Sym.Arith.MonadRing public import Lean.Meta.Sym.Arith.MonadSemiring import Init.Grind.Ring
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instHSMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 168, 246, 170, 1, 89, 173, 16)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "nsmul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 91, 174, 144, 107, 56, 221, 203)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zsmul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(150, 37, 191, 247, 137, 26, 61, 190)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value;
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
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toDiv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 88, 233, 125, 69, 12, 189, 21)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(232, 146, 236, 221, 122, 127, 105, 70)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0(lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_scalar_412_, lean_object* v_type_413_, lean_object* v_canonExpr_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0));
v___x_417_ = l_Lean_Name_mkStr2(v___x_410_, v___x_416_);
v___x_418_ = l_Lean_mkConst(v___x_417_, v___x_411_);
lean_inc_ref(v_type_413_);
v___x_419_ = l_Lean_mkApp4(v___x_418_, v_scalar_412_, v_type_413_, v_type_413_, v_inst_415_);
v___x_420_ = lean_apply_1(v_canonExpr_414_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4(lean_object* v_toPure_421_, lean_object* v_inst_x27_422_, lean_object* v_toBind_423_, lean_object* v___f_424_, lean_object* v___f_425_, lean_object* v___x_426_, lean_object* v_inst_427_, lean_object* v_____do__lift_428_){
_start:
{
if (lean_obj_tag(v_____do__lift_428_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_inst_427_);
lean_dec_ref(v___x_426_);
lean_dec(v___f_425_);
v___x_429_ = lean_apply_2(v_toPure_421_, lean_box(0), v_inst_x27_422_);
v___x_430_ = lean_apply_4(v_toBind_423_, lean_box(0), lean_box(0), v___x_429_, v___f_424_);
return v___x_430_;
}
else
{
lean_object* v_val_431_; lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec(v___f_424_);
v_val_431_ = lean_ctor_get(v_____do__lift_428_, 0);
lean_inc_n(v_val_431_, 2);
lean_dec_ref_known(v_____do__lift_428_, 1);
lean_inc(v_toBind_423_);
v___f_432_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_432_, 0, v_toPure_421_);
lean_closure_set(v___f_432_, 1, v_val_431_);
lean_closure_set(v___f_432_, 2, v_toBind_423_);
lean_closure_set(v___f_432_, 3, v___f_425_);
v___x_433_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0));
v___x_434_ = l_Lean_Name_mkStr2(v___x_426_, v___x_433_);
v___x_435_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_435_, 0, v___x_434_);
lean_closure_set(v___x_435_, 1, v_val_431_);
lean_closure_set(v___x_435_, 2, v_inst_x27_422_);
v___x_436_ = lean_apply_2(v_inst_427_, lean_box(0), v___x_435_);
v___x_437_ = lean_apply_4(v_toBind_423_, lean_box(0), lean_box(0), v___x_436_, v___f_432_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_u_447_, lean_object* v_type_448_, lean_object* v_scalar_449_, lean_object* v_expectedSMulInst_450_){
_start:
{
lean_object* v_toApplicative_451_; lean_object* v_toBind_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_485_; 
v_toApplicative_451_ = lean_ctor_get(v_inst_445_, 0);
v_toBind_452_ = lean_ctor_get(v_inst_445_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_inst_445_);
if (v_isSharedCheck_485_ == 0)
{
v___x_454_ = v_inst_445_;
v_isShared_455_ = v_isSharedCheck_485_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_toBind_452_);
lean_inc(v_toApplicative_451_);
lean_dec(v_inst_445_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_485_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_canonExpr_456_; lean_object* v_synthInstance_x3f_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_484_; 
v_canonExpr_456_ = lean_ctor_get(v_inst_446_, 0);
v_synthInstance_x3f_457_ = lean_ctor_get(v_inst_446_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_inst_446_);
if (v_isSharedCheck_484_ == 0)
{
v___x_459_ = v_inst_446_;
v_isShared_460_ = v_isSharedCheck_484_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_synthInstance_x3f_457_);
lean_inc(v_canonExpr_456_);
lean_dec(v_inst_446_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_484_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1));
v___x_462_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_463_ = lean_box(0);
lean_inc(v_u_447_);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
lean_ctor_set(v___x_459_, 1, v___x_463_);
lean_ctor_set(v___x_459_, 0, v_u_447_);
v___x_465_ = v___x_459_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_u_447_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_483_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
lean_inc_ref(v___x_465_);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 1);
lean_ctor_set(v___x_454_, 1, v___x_465_);
lean_ctor_set(v___x_454_, 0, v___x_462_);
v___x_467_ = v___x_454_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_482_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v_inst_x27_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_toPure_476_; lean_object* v___f_477_; lean_object* v___f_478_; lean_object* v___x_479_; lean_object* v___f_480_; lean_object* v___x_481_; 
v___x_468_ = l_Lean_mkConst(v___x_461_, v___x_467_);
lean_inc_ref_n(v_type_448_, 3);
lean_inc_ref_n(v_scalar_449_, 2);
v_inst_x27_469_ = l_Lean_mkApp3(v___x_468_, v_scalar_449_, v_type_448_, v_expectedSMulInst_450_);
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2));
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3));
v___x_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_472_, 0, v_u_447_);
lean_ctor_set(v___x_472_, 1, v___x_465_);
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_462_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_inc_ref(v___x_473_);
v___x_474_ = l_Lean_mkConst(v___x_471_, v___x_473_);
v___x_475_ = l_Lean_mkApp3(v___x_474_, v_scalar_449_, v_type_448_, v_type_448_);
v_toPure_476_ = lean_ctor_get(v_toApplicative_451_, 1);
lean_inc(v_toPure_476_);
lean_dec_ref(v_toApplicative_451_);
v___f_477_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_477_, 0, v___x_470_);
lean_closure_set(v___f_477_, 1, v___x_473_);
lean_closure_set(v___f_477_, 2, v_scalar_449_);
lean_closure_set(v___f_477_, 3, v_type_448_);
lean_closure_set(v___f_477_, 4, v_canonExpr_456_);
v___f_478_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_478_, 0, v___f_477_);
v___x_479_ = lean_apply_1(v_synthInstance_x3f_457_, v___x_475_);
lean_inc_ref(v___f_478_);
lean_inc(v_toBind_452_);
v___f_480_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4), 8, 7);
lean_closure_set(v___f_480_, 0, v_toPure_476_);
lean_closure_set(v___f_480_, 1, v_inst_x27_469_);
lean_closure_set(v___f_480_, 2, v_toBind_452_);
lean_closure_set(v___f_480_, 3, v___f_478_);
lean_closure_set(v___f_480_, 4, v___f_478_);
lean_closure_set(v___f_480_, 5, v___x_470_);
lean_closure_set(v___f_480_, 6, v_inst_444_);
v___x_481_ = lean_apply_4(v_toBind_452_, lean_box(0), lean_box(0), v___x_479_, v___f_480_);
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn(lean_object* v_m_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_u_490_, lean_object* v_type_491_, lean_object* v_scalar_492_, lean_object* v_expectedSMulInst_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_487_, v_inst_488_, v_inst_489_, v_u_490_, v_type_491_, v_scalar_492_, v_expectedSMulInst_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0(lean_object* v_fn_495_, lean_object* v_s_496_){
_start:
{
lean_object* v_id_497_; lean_object* v_type_498_; lean_object* v_u_499_; lean_object* v_ringInst_500_; lean_object* v_semiringInst_501_; lean_object* v_charInst_x3f_502_; lean_object* v_addFn_x3f_503_; lean_object* v_mulFn_x3f_504_; lean_object* v_subFn_x3f_505_; lean_object* v_negFn_x3f_506_; lean_object* v_powFn_x3f_507_; lean_object* v_intCastFn_x3f_508_; lean_object* v_natCastFn_x3f_509_; lean_object* v_intSMulFn_x3f_510_; lean_object* v_one_x3f_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_519_; 
v_id_497_ = lean_ctor_get(v_s_496_, 0);
v_type_498_ = lean_ctor_get(v_s_496_, 1);
v_u_499_ = lean_ctor_get(v_s_496_, 2);
v_ringInst_500_ = lean_ctor_get(v_s_496_, 3);
v_semiringInst_501_ = lean_ctor_get(v_s_496_, 4);
v_charInst_x3f_502_ = lean_ctor_get(v_s_496_, 5);
v_addFn_x3f_503_ = lean_ctor_get(v_s_496_, 6);
v_mulFn_x3f_504_ = lean_ctor_get(v_s_496_, 7);
v_subFn_x3f_505_ = lean_ctor_get(v_s_496_, 8);
v_negFn_x3f_506_ = lean_ctor_get(v_s_496_, 9);
v_powFn_x3f_507_ = lean_ctor_get(v_s_496_, 10);
v_intCastFn_x3f_508_ = lean_ctor_get(v_s_496_, 11);
v_natCastFn_x3f_509_ = lean_ctor_get(v_s_496_, 12);
v_intSMulFn_x3f_510_ = lean_ctor_get(v_s_496_, 14);
v_one_x3f_511_ = lean_ctor_get(v_s_496_, 15);
v_isSharedCheck_519_ = !lean_is_exclusive(v_s_496_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_s_496_, 13);
lean_dec(v_unused_520_);
v___x_513_ = v_s_496_;
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_one_x3f_511_);
lean_inc(v_intSMulFn_x3f_510_);
lean_inc(v_natCastFn_x3f_509_);
lean_inc(v_intCastFn_x3f_508_);
lean_inc(v_powFn_x3f_507_);
lean_inc(v_negFn_x3f_506_);
lean_inc(v_subFn_x3f_505_);
lean_inc(v_mulFn_x3f_504_);
lean_inc(v_addFn_x3f_503_);
lean_inc(v_charInst_x3f_502_);
lean_inc(v_semiringInst_501_);
lean_inc(v_ringInst_500_);
lean_inc(v_u_499_);
lean_inc(v_type_498_);
lean_inc(v_id_497_);
lean_dec(v_s_496_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v_fn_495_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 13, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_id_497_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_type_498_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_u_499_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_ringInst_500_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_semiringInst_501_);
lean_ctor_set(v_reuseFailAlloc_518_, 5, v_charInst_x3f_502_);
lean_ctor_set(v_reuseFailAlloc_518_, 6, v_addFn_x3f_503_);
lean_ctor_set(v_reuseFailAlloc_518_, 7, v_mulFn_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_518_, 8, v_subFn_x3f_505_);
lean_ctor_set(v_reuseFailAlloc_518_, 9, v_negFn_x3f_506_);
lean_ctor_set(v_reuseFailAlloc_518_, 10, v_powFn_x3f_507_);
lean_ctor_set(v_reuseFailAlloc_518_, 11, v_intCastFn_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 12, v_natCastFn_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_518_, 13, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 14, v_intSMulFn_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_518_, 15, v_one_x3f_511_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1(lean_object* v_toPure_521_, lean_object* v_fn_522_, lean_object* v_____r_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_apply_2(v_toPure_521_, lean_box(0), v_fn_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2(lean_object* v_toPure_525_, lean_object* v_modifyRing_526_, lean_object* v_toBind_527_, lean_object* v_fn_528_){
_start:
{
lean_object* v___f_529_; lean_object* v___f_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_inc_ref(v_fn_528_);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_529_, 0, v_fn_528_);
v___f_530_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_530_, 0, v_toPure_525_);
lean_closure_set(v___f_530_, 1, v_fn_528_);
v___x_531_ = lean_apply_1(v_modifyRing_526_, v___f_529_);
v___x_532_ = lean_apply_4(v_toBind_527_, lean_box(0), lean_box(0), v___x_531_, v___f_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3(lean_object* v_toPure_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_toBind_543_, lean_object* v___f_544_, lean_object* v_ring_545_){
_start:
{
lean_object* v_natSMulFn_x3f_546_; 
v_natSMulFn_x3f_546_ = lean_ctor_get(v_ring_545_, 13);
if (lean_obj_tag(v_natSMulFn_x3f_546_) == 1)
{
lean_object* v_val_547_; lean_object* v___x_548_; 
lean_inc_ref(v_natSMulFn_x3f_546_);
lean_dec_ref(v_ring_545_);
lean_dec(v___f_544_);
lean_dec(v_toBind_543_);
lean_dec_ref(v_inst_542_);
lean_dec_ref(v_inst_541_);
lean_dec(v_inst_540_);
v_val_547_ = lean_ctor_get(v_natSMulFn_x3f_546_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v_natSMulFn_x3f_546_, 1);
v___x_548_ = lean_apply_2(v_toPure_539_, lean_box(0), v_val_547_);
return v___x_548_;
}
else
{
lean_object* v_type_549_; lean_object* v_u_550_; lean_object* v_semiringInst_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_toPure_539_);
v_type_549_ = lean_ctor_get(v_ring_545_, 1);
lean_inc_ref_n(v_type_549_, 2);
v_u_550_ = lean_ctor_get(v_ring_545_, 2);
lean_inc_n(v_u_550_, 2);
v_semiringInst_551_ = lean_ctor_get(v_ring_545_, 4);
lean_inc_ref(v_semiringInst_551_);
lean_dec_ref(v_ring_545_);
v___x_552_ = l_Lean_Nat_mkType;
v___x_553_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_554_ = lean_box(0);
v___x_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_555_, 0, v_u_550_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l_Lean_mkConst(v___x_553_, v___x_555_);
v___x_557_ = l_Lean_mkAppB(v___x_556_, v_type_549_, v_semiringInst_551_);
v___x_558_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_540_, v_inst_541_, v_inst_542_, v_u_550_, v_type_549_, v___x_552_, v___x_557_);
v___x_559_ = lean_apply_4(v_toBind_543_, lean_box(0), lean_box(0), v___x_558_, v___f_544_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_){
_start:
{
lean_object* v_toApplicative_564_; lean_object* v_toBind_565_; lean_object* v_getRing_566_; lean_object* v_modifyRing_567_; lean_object* v_toPure_568_; lean_object* v___f_569_; lean_object* v___f_570_; lean_object* v___x_571_; 
v_toApplicative_564_ = lean_ctor_get(v_inst_561_, 0);
v_toBind_565_ = lean_ctor_get(v_inst_561_, 1);
lean_inc_n(v_toBind_565_, 3);
v_getRing_566_ = lean_ctor_get(v_inst_563_, 0);
lean_inc(v_getRing_566_);
v_modifyRing_567_ = lean_ctor_get(v_inst_563_, 1);
lean_inc(v_modifyRing_567_);
lean_dec_ref(v_inst_563_);
v_toPure_568_ = lean_ctor_get(v_toApplicative_564_, 1);
lean_inc_n(v_toPure_568_, 2);
v___f_569_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_569_, 0, v_toPure_568_);
lean_closure_set(v___f_569_, 1, v_modifyRing_567_);
lean_closure_set(v___f_569_, 2, v_toBind_565_);
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_570_, 0, v_toPure_568_);
lean_closure_set(v___f_570_, 1, v_inst_560_);
lean_closure_set(v___f_570_, 2, v_inst_561_);
lean_closure_set(v___f_570_, 3, v_inst_562_);
lean_closure_set(v___f_570_, 4, v_toBind_565_);
lean_closure_set(v___f_570_, 5, v___f_569_);
v___x_571_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v_getRing_566_, v___f_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn(lean_object* v_m_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(v_inst_573_, v_inst_574_, v_inst_575_, v_inst_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0(lean_object* v_fn_578_, lean_object* v_s_579_){
_start:
{
lean_object* v_id_580_; lean_object* v_type_581_; lean_object* v_u_582_; lean_object* v_ringInst_583_; lean_object* v_semiringInst_584_; lean_object* v_charInst_x3f_585_; lean_object* v_addFn_x3f_586_; lean_object* v_mulFn_x3f_587_; lean_object* v_subFn_x3f_588_; lean_object* v_negFn_x3f_589_; lean_object* v_powFn_x3f_590_; lean_object* v_intCastFn_x3f_591_; lean_object* v_natCastFn_x3f_592_; lean_object* v_natSMulFn_x3f_593_; lean_object* v_one_x3f_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v_id_580_ = lean_ctor_get(v_s_579_, 0);
v_type_581_ = lean_ctor_get(v_s_579_, 1);
v_u_582_ = lean_ctor_get(v_s_579_, 2);
v_ringInst_583_ = lean_ctor_get(v_s_579_, 3);
v_semiringInst_584_ = lean_ctor_get(v_s_579_, 4);
v_charInst_x3f_585_ = lean_ctor_get(v_s_579_, 5);
v_addFn_x3f_586_ = lean_ctor_get(v_s_579_, 6);
v_mulFn_x3f_587_ = lean_ctor_get(v_s_579_, 7);
v_subFn_x3f_588_ = lean_ctor_get(v_s_579_, 8);
v_negFn_x3f_589_ = lean_ctor_get(v_s_579_, 9);
v_powFn_x3f_590_ = lean_ctor_get(v_s_579_, 10);
v_intCastFn_x3f_591_ = lean_ctor_get(v_s_579_, 11);
v_natCastFn_x3f_592_ = lean_ctor_get(v_s_579_, 12);
v_natSMulFn_x3f_593_ = lean_ctor_get(v_s_579_, 13);
v_one_x3f_594_ = lean_ctor_get(v_s_579_, 15);
v_isSharedCheck_602_ = !lean_is_exclusive(v_s_579_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_s_579_, 14);
lean_dec(v_unused_603_);
v___x_596_ = v_s_579_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_one_x3f_594_);
lean_inc(v_natSMulFn_x3f_593_);
lean_inc(v_natCastFn_x3f_592_);
lean_inc(v_intCastFn_x3f_591_);
lean_inc(v_powFn_x3f_590_);
lean_inc(v_negFn_x3f_589_);
lean_inc(v_subFn_x3f_588_);
lean_inc(v_mulFn_x3f_587_);
lean_inc(v_addFn_x3f_586_);
lean_inc(v_charInst_x3f_585_);
lean_inc(v_semiringInst_584_);
lean_inc(v_ringInst_583_);
lean_inc(v_u_582_);
lean_inc(v_type_581_);
lean_inc(v_id_580_);
lean_dec(v_s_579_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_fn_578_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 14, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_id_580_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_type_581_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_u_582_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_ringInst_583_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_semiringInst_584_);
lean_ctor_set(v_reuseFailAlloc_601_, 5, v_charInst_x3f_585_);
lean_ctor_set(v_reuseFailAlloc_601_, 6, v_addFn_x3f_586_);
lean_ctor_set(v_reuseFailAlloc_601_, 7, v_mulFn_x3f_587_);
lean_ctor_set(v_reuseFailAlloc_601_, 8, v_subFn_x3f_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 9, v_negFn_x3f_589_);
lean_ctor_set(v_reuseFailAlloc_601_, 10, v_powFn_x3f_590_);
lean_ctor_set(v_reuseFailAlloc_601_, 11, v_intCastFn_x3f_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 12, v_natCastFn_x3f_592_);
lean_ctor_set(v_reuseFailAlloc_601_, 13, v_natSMulFn_x3f_593_);
lean_ctor_set(v_reuseFailAlloc_601_, 14, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_601_, 15, v_one_x3f_594_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2(lean_object* v_toPure_604_, lean_object* v_modifyRing_605_, lean_object* v_toBind_606_, lean_object* v_fn_607_){
_start:
{
lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_inc_ref(v_fn_607_);
v___f_608_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_608_, 0, v_fn_607_);
v___f_609_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_609_, 0, v_toPure_604_);
lean_closure_set(v___f_609_, 1, v_fn_607_);
v___x_610_ = lean_apply_1(v_modifyRing_605_, v___f_608_);
v___x_611_ = lean_apply_4(v_toBind_606_, lean_box(0), lean_box(0), v___x_610_, v___f_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1(lean_object* v_toPure_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_toBind_623_, lean_object* v___f_624_, lean_object* v_ring_625_){
_start:
{
lean_object* v_intSMulFn_x3f_626_; 
v_intSMulFn_x3f_626_ = lean_ctor_get(v_ring_625_, 14);
if (lean_obj_tag(v_intSMulFn_x3f_626_) == 1)
{
lean_object* v_val_627_; lean_object* v___x_628_; 
lean_inc_ref(v_intSMulFn_x3f_626_);
lean_dec_ref(v_ring_625_);
lean_dec(v___f_624_);
lean_dec(v_toBind_623_);
lean_dec_ref(v_inst_622_);
lean_dec_ref(v_inst_621_);
lean_dec(v_inst_620_);
v_val_627_ = lean_ctor_get(v_intSMulFn_x3f_626_, 0);
lean_inc(v_val_627_);
lean_dec_ref_known(v_intSMulFn_x3f_626_, 1);
v___x_628_ = lean_apply_2(v_toPure_619_, lean_box(0), v_val_627_);
return v___x_628_;
}
else
{
lean_object* v_type_629_; lean_object* v_u_630_; lean_object* v_ringInst_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_toPure_619_);
v_type_629_ = lean_ctor_get(v_ring_625_, 1);
lean_inc_ref_n(v_type_629_, 2);
v_u_630_ = lean_ctor_get(v_ring_625_, 2);
lean_inc_n(v_u_630_, 2);
v_ringInst_631_ = lean_ctor_get(v_ring_625_, 3);
lean_inc_ref(v_ringInst_631_);
lean_dec_ref(v_ring_625_);
v___x_632_ = l_Lean_Int_mkType;
v___x_633_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2));
v___x_634_ = lean_box(0);
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v_u_630_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_mkConst(v___x_633_, v___x_635_);
v___x_637_ = l_Lean_mkAppB(v___x_636_, v_type_629_, v_ringInst_631_);
v___x_638_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_620_, v_inst_621_, v_inst_622_, v_u_630_, v_type_629_, v___x_632_, v___x_637_);
v___x_639_ = lean_apply_4(v_toBind_623_, lean_box(0), lean_box(0), v___x_638_, v___f_624_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_inst_643_){
_start:
{
lean_object* v_toApplicative_644_; lean_object* v_toBind_645_; lean_object* v_getRing_646_; lean_object* v_modifyRing_647_; lean_object* v_toPure_648_; lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___x_651_; 
v_toApplicative_644_ = lean_ctor_get(v_inst_641_, 0);
v_toBind_645_ = lean_ctor_get(v_inst_641_, 1);
lean_inc_n(v_toBind_645_, 3);
v_getRing_646_ = lean_ctor_get(v_inst_643_, 0);
lean_inc(v_getRing_646_);
v_modifyRing_647_ = lean_ctor_get(v_inst_643_, 1);
lean_inc(v_modifyRing_647_);
lean_dec_ref(v_inst_643_);
v_toPure_648_ = lean_ctor_get(v_toApplicative_644_, 1);
lean_inc_n(v_toPure_648_, 2);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_649_, 0, v_toPure_648_);
lean_closure_set(v___f_649_, 1, v_modifyRing_647_);
lean_closure_set(v___f_649_, 2, v_toBind_645_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1), 7, 6);
lean_closure_set(v___f_650_, 0, v_toPure_648_);
lean_closure_set(v___f_650_, 1, v_inst_640_);
lean_closure_set(v___f_650_, 2, v_inst_641_);
lean_closure_set(v___f_650_, 3, v_inst_642_);
lean_closure_set(v___f_650_, 4, v_toBind_645_);
lean_closure_set(v___f_650_, 5, v___f_649_);
v___x_651_ = lean_apply_4(v_toBind_645_, lean_box(0), lean_box(0), v_getRing_646_, v___f_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn(lean_object* v_m_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(v_inst_653_, v_inst_654_, v_inst_655_, v_inst_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_658_, lean_object* v_s_659_){
_start:
{
lean_object* v_id_660_; lean_object* v_type_661_; lean_object* v_u_662_; lean_object* v_ringInst_663_; lean_object* v_semiringInst_664_; lean_object* v_charInst_x3f_665_; lean_object* v_mulFn_x3f_666_; lean_object* v_subFn_x3f_667_; lean_object* v_negFn_x3f_668_; lean_object* v_powFn_x3f_669_; lean_object* v_intCastFn_x3f_670_; lean_object* v_natCastFn_x3f_671_; lean_object* v_natSMulFn_x3f_672_; lean_object* v_intSMulFn_x3f_673_; lean_object* v_one_x3f_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
v_id_660_ = lean_ctor_get(v_s_659_, 0);
v_type_661_ = lean_ctor_get(v_s_659_, 1);
v_u_662_ = lean_ctor_get(v_s_659_, 2);
v_ringInst_663_ = lean_ctor_get(v_s_659_, 3);
v_semiringInst_664_ = lean_ctor_get(v_s_659_, 4);
v_charInst_x3f_665_ = lean_ctor_get(v_s_659_, 5);
v_mulFn_x3f_666_ = lean_ctor_get(v_s_659_, 7);
v_subFn_x3f_667_ = lean_ctor_get(v_s_659_, 8);
v_negFn_x3f_668_ = lean_ctor_get(v_s_659_, 9);
v_powFn_x3f_669_ = lean_ctor_get(v_s_659_, 10);
v_intCastFn_x3f_670_ = lean_ctor_get(v_s_659_, 11);
v_natCastFn_x3f_671_ = lean_ctor_get(v_s_659_, 12);
v_natSMulFn_x3f_672_ = lean_ctor_get(v_s_659_, 13);
v_intSMulFn_x3f_673_ = lean_ctor_get(v_s_659_, 14);
v_one_x3f_674_ = lean_ctor_get(v_s_659_, 15);
v_isSharedCheck_682_ = !lean_is_exclusive(v_s_659_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v_s_659_, 6);
lean_dec(v_unused_683_);
v___x_676_ = v_s_659_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_one_x3f_674_);
lean_inc(v_intSMulFn_x3f_673_);
lean_inc(v_natSMulFn_x3f_672_);
lean_inc(v_natCastFn_x3f_671_);
lean_inc(v_intCastFn_x3f_670_);
lean_inc(v_powFn_x3f_669_);
lean_inc(v_negFn_x3f_668_);
lean_inc(v_subFn_x3f_667_);
lean_inc(v_mulFn_x3f_666_);
lean_inc(v_charInst_x3f_665_);
lean_inc(v_semiringInst_664_);
lean_inc(v_ringInst_663_);
lean_inc(v_u_662_);
lean_inc(v_type_661_);
lean_inc(v_id_660_);
lean_dec(v_s_659_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v_addFn_658_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 6, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_id_660_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_type_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_u_662_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_ringInst_663_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_semiringInst_664_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v_charInst_x3f_665_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 7, v_mulFn_x3f_666_);
lean_ctor_set(v_reuseFailAlloc_681_, 8, v_subFn_x3f_667_);
lean_ctor_set(v_reuseFailAlloc_681_, 9, v_negFn_x3f_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 10, v_powFn_x3f_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 11, v_intCastFn_x3f_670_);
lean_ctor_set(v_reuseFailAlloc_681_, 12, v_natCastFn_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 13, v_natSMulFn_x3f_672_);
lean_ctor_set(v_reuseFailAlloc_681_, 14, v_intSMulFn_x3f_673_);
lean_ctor_set(v_reuseFailAlloc_681_, 15, v_one_x3f_674_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_684_, lean_object* v_addFn_685_, lean_object* v_____r_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_apply_2(v_toPure_684_, lean_box(0), v_addFn_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_688_, lean_object* v_modifyRing_689_, lean_object* v_toBind_690_, lean_object* v_addFn_691_){
_start:
{
lean_object* v___f_692_; lean_object* v___f_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
lean_inc_ref(v_addFn_691_);
v___f_692_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_692_, 0, v_addFn_691_);
v___f_693_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_693_, 0, v_toPure_688_);
lean_closure_set(v___f_693_, 1, v_addFn_691_);
v___x_694_ = lean_apply_1(v_modifyRing_689_, v___f_692_);
v___x_695_ = lean_apply_4(v_toBind_690_, lean_box(0), lean_box(0), v___x_694_, v___f_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_toBind_717_, lean_object* v___f_718_, lean_object* v_ring_719_){
_start:
{
lean_object* v_addFn_x3f_720_; 
v_addFn_x3f_720_ = lean_ctor_get(v_ring_719_, 6);
if (lean_obj_tag(v_addFn_x3f_720_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; 
lean_inc_ref(v_addFn_x3f_720_);
lean_dec_ref(v_ring_719_);
lean_dec(v___f_718_);
lean_dec(v_toBind_717_);
lean_dec_ref(v_inst_716_);
lean_dec_ref(v_inst_715_);
lean_dec_ref(v_inst_714_);
lean_dec(v_inst_713_);
v_val_721_ = lean_ctor_get(v_addFn_x3f_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v_addFn_x3f_720_, 1);
v___x_722_ = lean_apply_2(v_toPure_712_, lean_box(0), v_val_721_);
return v___x_722_;
}
else
{
lean_object* v_type_723_; lean_object* v_u_724_; lean_object* v_semiringInst_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_expectedInst_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v_toPure_712_);
v_type_723_ = lean_ctor_get(v_ring_719_, 1);
lean_inc_ref_n(v_type_723_, 3);
v_u_724_ = lean_ctor_get(v_ring_719_, 2);
lean_inc_n(v_u_724_, 2);
v_semiringInst_725_ = lean_ctor_get(v_ring_719_, 4);
lean_inc_ref(v_semiringInst_725_);
lean_dec_ref(v_ring_719_);
v___x_726_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_727_ = lean_box(0);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v_u_724_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
lean_inc_ref(v___x_728_);
v___x_729_ = l_Lean_mkConst(v___x_726_, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_731_ = l_Lean_mkConst(v___x_730_, v___x_728_);
v___x_732_ = l_Lean_mkAppB(v___x_731_, v_type_723_, v_semiringInst_725_);
v_expectedInst_733_ = l_Lean_mkAppB(v___x_729_, v_type_723_, v___x_732_);
v___x_734_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_735_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_736_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_713_, v_inst_714_, v_inst_715_, v_inst_716_, v_type_723_, v_u_724_, v___x_734_, v___x_735_, v_expectedInst_733_);
v___x_737_ = lean_apply_4(v_toBind_717_, lean_box(0), lean_box(0), v___x_736_, v___f_718_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_){
_start:
{
lean_object* v_toApplicative_743_; lean_object* v_toBind_744_; lean_object* v_getRing_745_; lean_object* v_modifyRing_746_; lean_object* v_toPure_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___x_750_; 
v_toApplicative_743_ = lean_ctor_get(v_inst_740_, 0);
v_toBind_744_ = lean_ctor_get(v_inst_740_, 1);
lean_inc_n(v_toBind_744_, 3);
v_getRing_745_ = lean_ctor_get(v_inst_742_, 0);
lean_inc(v_getRing_745_);
v_modifyRing_746_ = lean_ctor_get(v_inst_742_, 1);
lean_inc(v_modifyRing_746_);
lean_dec_ref(v_inst_742_);
v_toPure_747_ = lean_ctor_get(v_toApplicative_743_, 1);
lean_inc_n(v_toPure_747_, 2);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_748_, 0, v_toPure_747_);
lean_closure_set(v___f_748_, 1, v_modifyRing_746_);
lean_closure_set(v___f_748_, 2, v_toBind_744_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_749_, 0, v_toPure_747_);
lean_closure_set(v___f_749_, 1, v_inst_738_);
lean_closure_set(v___f_749_, 2, v_inst_739_);
lean_closure_set(v___f_749_, 3, v_inst_740_);
lean_closure_set(v___f_749_, 4, v_inst_741_);
lean_closure_set(v___f_749_, 5, v_toBind_744_);
lean_closure_set(v___f_749_, 6, v___f_748_);
v___x_750_ = lean_apply_4(v_toBind_744_, lean_box(0), lean_box(0), v_getRing_745_, v___f_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_752_, v_inst_753_, v_inst_754_, v_inst_755_, v_inst_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_758_, lean_object* v_s_759_){
_start:
{
lean_object* v_id_760_; lean_object* v_type_761_; lean_object* v_u_762_; lean_object* v_ringInst_763_; lean_object* v_semiringInst_764_; lean_object* v_charInst_x3f_765_; lean_object* v_addFn_x3f_766_; lean_object* v_subFn_x3f_767_; lean_object* v_negFn_x3f_768_; lean_object* v_powFn_x3f_769_; lean_object* v_intCastFn_x3f_770_; lean_object* v_natCastFn_x3f_771_; lean_object* v_natSMulFn_x3f_772_; lean_object* v_intSMulFn_x3f_773_; lean_object* v_one_x3f_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_id_760_ = lean_ctor_get(v_s_759_, 0);
v_type_761_ = lean_ctor_get(v_s_759_, 1);
v_u_762_ = lean_ctor_get(v_s_759_, 2);
v_ringInst_763_ = lean_ctor_get(v_s_759_, 3);
v_semiringInst_764_ = lean_ctor_get(v_s_759_, 4);
v_charInst_x3f_765_ = lean_ctor_get(v_s_759_, 5);
v_addFn_x3f_766_ = lean_ctor_get(v_s_759_, 6);
v_subFn_x3f_767_ = lean_ctor_get(v_s_759_, 8);
v_negFn_x3f_768_ = lean_ctor_get(v_s_759_, 9);
v_powFn_x3f_769_ = lean_ctor_get(v_s_759_, 10);
v_intCastFn_x3f_770_ = lean_ctor_get(v_s_759_, 11);
v_natCastFn_x3f_771_ = lean_ctor_get(v_s_759_, 12);
v_natSMulFn_x3f_772_ = lean_ctor_get(v_s_759_, 13);
v_intSMulFn_x3f_773_ = lean_ctor_get(v_s_759_, 14);
v_one_x3f_774_ = lean_ctor_get(v_s_759_, 15);
v_isSharedCheck_782_ = !lean_is_exclusive(v_s_759_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v_s_759_, 7);
lean_dec(v_unused_783_);
v___x_776_ = v_s_759_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_one_x3f_774_);
lean_inc(v_intSMulFn_x3f_773_);
lean_inc(v_natSMulFn_x3f_772_);
lean_inc(v_natCastFn_x3f_771_);
lean_inc(v_intCastFn_x3f_770_);
lean_inc(v_powFn_x3f_769_);
lean_inc(v_negFn_x3f_768_);
lean_inc(v_subFn_x3f_767_);
lean_inc(v_addFn_x3f_766_);
lean_inc(v_charInst_x3f_765_);
lean_inc(v_semiringInst_764_);
lean_inc(v_ringInst_763_);
lean_inc(v_u_762_);
lean_inc(v_type_761_);
lean_inc(v_id_760_);
lean_dec(v_s_759_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_mulFn_758_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 7, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_id_760_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_type_761_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_u_762_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_ringInst_763_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_semiringInst_764_);
lean_ctor_set(v_reuseFailAlloc_781_, 5, v_charInst_x3f_765_);
lean_ctor_set(v_reuseFailAlloc_781_, 6, v_addFn_x3f_766_);
lean_ctor_set(v_reuseFailAlloc_781_, 7, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_781_, 8, v_subFn_x3f_767_);
lean_ctor_set(v_reuseFailAlloc_781_, 9, v_negFn_x3f_768_);
lean_ctor_set(v_reuseFailAlloc_781_, 10, v_powFn_x3f_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 11, v_intCastFn_x3f_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 12, v_natCastFn_x3f_771_);
lean_ctor_set(v_reuseFailAlloc_781_, 13, v_natSMulFn_x3f_772_);
lean_ctor_set(v_reuseFailAlloc_781_, 14, v_intSMulFn_x3f_773_);
lean_ctor_set(v_reuseFailAlloc_781_, 15, v_one_x3f_774_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object* v_toPure_784_, lean_object* v_mulFn_785_, lean_object* v_____r_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = lean_apply_2(v_toPure_784_, lean_box(0), v_mulFn_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object* v_toPure_788_, lean_object* v_modifyRing_789_, lean_object* v_toBind_790_, lean_object* v_mulFn_791_){
_start:
{
lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc_ref(v_mulFn_791_);
v___f_792_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_792_, 0, v_mulFn_791_);
v___f_793_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_793_, 0, v_toPure_788_);
lean_closure_set(v___f_793_, 1, v_mulFn_791_);
v___x_794_ = lean_apply_1(v_modifyRing_789_, v___f_792_);
v___x_795_ = lean_apply_4(v_toBind_790_, lean_box(0), lean_box(0), v___x_794_, v___f_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object* v_toPure_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_toBind_817_, lean_object* v___f_818_, lean_object* v_ring_819_){
_start:
{
lean_object* v_mulFn_x3f_820_; 
v_mulFn_x3f_820_ = lean_ctor_get(v_ring_819_, 7);
if (lean_obj_tag(v_mulFn_x3f_820_) == 1)
{
lean_object* v_val_821_; lean_object* v___x_822_; 
lean_inc_ref(v_mulFn_x3f_820_);
lean_dec_ref(v_ring_819_);
lean_dec(v___f_818_);
lean_dec(v_toBind_817_);
lean_dec_ref(v_inst_816_);
lean_dec_ref(v_inst_815_);
lean_dec_ref(v_inst_814_);
lean_dec(v_inst_813_);
v_val_821_ = lean_ctor_get(v_mulFn_x3f_820_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v_mulFn_x3f_820_, 1);
v___x_822_ = lean_apply_2(v_toPure_812_, lean_box(0), v_val_821_);
return v___x_822_;
}
else
{
lean_object* v_type_823_; lean_object* v_u_824_; lean_object* v_semiringInst_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v_expectedInst_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_toPure_812_);
v_type_823_ = lean_ctor_get(v_ring_819_, 1);
lean_inc_ref_n(v_type_823_, 3);
v_u_824_ = lean_ctor_get(v_ring_819_, 2);
lean_inc_n(v_u_824_, 2);
v_semiringInst_825_ = lean_ctor_get(v_ring_819_, 4);
lean_inc_ref(v_semiringInst_825_);
lean_dec_ref(v_ring_819_);
v___x_826_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v_u_824_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
lean_inc_ref(v___x_828_);
v___x_829_ = l_Lean_mkConst(v___x_826_, v___x_828_);
v___x_830_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_831_ = l_Lean_mkConst(v___x_830_, v___x_828_);
v___x_832_ = l_Lean_mkAppB(v___x_831_, v_type_823_, v_semiringInst_825_);
v_expectedInst_833_ = l_Lean_mkAppB(v___x_829_, v_type_823_, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_835_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_836_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_813_, v_inst_814_, v_inst_815_, v_inst_816_, v_type_823_, v_u_824_, v___x_834_, v___x_835_, v_expectedInst_833_);
v___x_837_ = lean_apply_4(v_toBind_817_, lean_box(0), lean_box(0), v___x_836_, v___f_818_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_){
_start:
{
lean_object* v_toApplicative_843_; lean_object* v_toBind_844_; lean_object* v_getRing_845_; lean_object* v_modifyRing_846_; lean_object* v_toPure_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___x_850_; 
v_toApplicative_843_ = lean_ctor_get(v_inst_840_, 0);
v_toBind_844_ = lean_ctor_get(v_inst_840_, 1);
lean_inc_n(v_toBind_844_, 3);
v_getRing_845_ = lean_ctor_get(v_inst_842_, 0);
lean_inc(v_getRing_845_);
v_modifyRing_846_ = lean_ctor_get(v_inst_842_, 1);
lean_inc(v_modifyRing_846_);
lean_dec_ref(v_inst_842_);
v_toPure_847_ = lean_ctor_get(v_toApplicative_843_, 1);
lean_inc_n(v_toPure_847_, 2);
v___f_848_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_848_, 0, v_toPure_847_);
lean_closure_set(v___f_848_, 1, v_modifyRing_846_);
lean_closure_set(v___f_848_, 2, v_toBind_844_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_849_, 0, v_toPure_847_);
lean_closure_set(v___f_849_, 1, v_inst_838_);
lean_closure_set(v___f_849_, 2, v_inst_839_);
lean_closure_set(v___f_849_, 3, v_inst_840_);
lean_closure_set(v___f_849_, 4, v_inst_841_);
lean_closure_set(v___f_849_, 5, v_toBind_844_);
lean_closure_set(v___f_849_, 6, v___f_848_);
v___x_850_ = lean_apply_4(v_toBind_844_, lean_box(0), lean_box(0), v_getRing_845_, v___f_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object* v_m_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_inst_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_852_, v_inst_853_, v_inst_854_, v_inst_855_, v_inst_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object* v_subFn_858_, lean_object* v_s_859_){
_start:
{
lean_object* v_id_860_; lean_object* v_type_861_; lean_object* v_u_862_; lean_object* v_ringInst_863_; lean_object* v_semiringInst_864_; lean_object* v_charInst_x3f_865_; lean_object* v_addFn_x3f_866_; lean_object* v_mulFn_x3f_867_; lean_object* v_negFn_x3f_868_; lean_object* v_powFn_x3f_869_; lean_object* v_intCastFn_x3f_870_; lean_object* v_natCastFn_x3f_871_; lean_object* v_natSMulFn_x3f_872_; lean_object* v_intSMulFn_x3f_873_; lean_object* v_one_x3f_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_882_; 
v_id_860_ = lean_ctor_get(v_s_859_, 0);
v_type_861_ = lean_ctor_get(v_s_859_, 1);
v_u_862_ = lean_ctor_get(v_s_859_, 2);
v_ringInst_863_ = lean_ctor_get(v_s_859_, 3);
v_semiringInst_864_ = lean_ctor_get(v_s_859_, 4);
v_charInst_x3f_865_ = lean_ctor_get(v_s_859_, 5);
v_addFn_x3f_866_ = lean_ctor_get(v_s_859_, 6);
v_mulFn_x3f_867_ = lean_ctor_get(v_s_859_, 7);
v_negFn_x3f_868_ = lean_ctor_get(v_s_859_, 9);
v_powFn_x3f_869_ = lean_ctor_get(v_s_859_, 10);
v_intCastFn_x3f_870_ = lean_ctor_get(v_s_859_, 11);
v_natCastFn_x3f_871_ = lean_ctor_get(v_s_859_, 12);
v_natSMulFn_x3f_872_ = lean_ctor_get(v_s_859_, 13);
v_intSMulFn_x3f_873_ = lean_ctor_get(v_s_859_, 14);
v_one_x3f_874_ = lean_ctor_get(v_s_859_, 15);
v_isSharedCheck_882_ = !lean_is_exclusive(v_s_859_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v_s_859_, 8);
lean_dec(v_unused_883_);
v___x_876_ = v_s_859_;
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_one_x3f_874_);
lean_inc(v_intSMulFn_x3f_873_);
lean_inc(v_natSMulFn_x3f_872_);
lean_inc(v_natCastFn_x3f_871_);
lean_inc(v_intCastFn_x3f_870_);
lean_inc(v_powFn_x3f_869_);
lean_inc(v_negFn_x3f_868_);
lean_inc(v_mulFn_x3f_867_);
lean_inc(v_addFn_x3f_866_);
lean_inc(v_charInst_x3f_865_);
lean_inc(v_semiringInst_864_);
lean_inc(v_ringInst_863_);
lean_inc(v_u_862_);
lean_inc(v_type_861_);
lean_inc(v_id_860_);
lean_dec(v_s_859_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_subFn_858_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 8, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_id_860_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_type_861_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_u_862_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_ringInst_863_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_semiringInst_864_);
lean_ctor_set(v_reuseFailAlloc_881_, 5, v_charInst_x3f_865_);
lean_ctor_set(v_reuseFailAlloc_881_, 6, v_addFn_x3f_866_);
lean_ctor_set(v_reuseFailAlloc_881_, 7, v_mulFn_x3f_867_);
lean_ctor_set(v_reuseFailAlloc_881_, 8, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_881_, 9, v_negFn_x3f_868_);
lean_ctor_set(v_reuseFailAlloc_881_, 10, v_powFn_x3f_869_);
lean_ctor_set(v_reuseFailAlloc_881_, 11, v_intCastFn_x3f_870_);
lean_ctor_set(v_reuseFailAlloc_881_, 12, v_natCastFn_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_881_, 13, v_natSMulFn_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_881_, 14, v_intSMulFn_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_881_, 15, v_one_x3f_874_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_884_, lean_object* v_subFn_885_, lean_object* v_____r_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_apply_2(v_toPure_884_, lean_box(0), v_subFn_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_888_, lean_object* v_modifyRing_889_, lean_object* v_toBind_890_, lean_object* v_subFn_891_){
_start:
{
lean_object* v___f_892_; lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc_ref(v_subFn_891_);
v___f_892_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_892_, 0, v_subFn_891_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_893_, 0, v_toPure_888_);
lean_closure_set(v___f_893_, 1, v_subFn_891_);
v___x_894_ = lean_apply_1(v_modifyRing_889_, v___f_892_);
v___x_895_ = lean_apply_4(v_toBind_890_, lean_box(0), lean_box(0), v___x_894_, v___f_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_toBind_917_, lean_object* v___f_918_, lean_object* v_ring_919_){
_start:
{
lean_object* v_subFn_x3f_920_; 
v_subFn_x3f_920_ = lean_ctor_get(v_ring_919_, 8);
if (lean_obj_tag(v_subFn_x3f_920_) == 1)
{
lean_object* v_val_921_; lean_object* v___x_922_; 
lean_inc_ref(v_subFn_x3f_920_);
lean_dec_ref(v_ring_919_);
lean_dec(v___f_918_);
lean_dec(v_toBind_917_);
lean_dec_ref(v_inst_916_);
lean_dec_ref(v_inst_915_);
lean_dec_ref(v_inst_914_);
lean_dec(v_inst_913_);
v_val_921_ = lean_ctor_get(v_subFn_x3f_920_, 0);
lean_inc(v_val_921_);
lean_dec_ref_known(v_subFn_x3f_920_, 1);
v___x_922_ = lean_apply_2(v_toPure_912_, lean_box(0), v_val_921_);
return v___x_922_;
}
else
{
lean_object* v_type_923_; lean_object* v_u_924_; lean_object* v_ringInst_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_expectedInst_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v_toPure_912_);
v_type_923_ = lean_ctor_get(v_ring_919_, 1);
lean_inc_ref_n(v_type_923_, 3);
v_u_924_ = lean_ctor_get(v_ring_919_, 2);
lean_inc_n(v_u_924_, 2);
v_ringInst_925_ = lean_ctor_get(v_ring_919_, 3);
lean_inc_ref(v_ringInst_925_);
lean_dec_ref(v_ring_919_);
v___x_926_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_927_ = lean_box(0);
v___x_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_928_, 0, v_u_924_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
lean_inc_ref(v___x_928_);
v___x_929_ = l_Lean_mkConst(v___x_926_, v___x_928_);
v___x_930_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3));
v___x_931_ = l_Lean_mkConst(v___x_930_, v___x_928_);
v___x_932_ = l_Lean_mkAppB(v___x_931_, v_type_923_, v_ringInst_925_);
v_expectedInst_933_ = l_Lean_mkAppB(v___x_929_, v_type_923_, v___x_932_);
v___x_934_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5));
v___x_935_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7));
v___x_936_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_913_, v_inst_914_, v_inst_915_, v_inst_916_, v_type_923_, v_u_924_, v___x_934_, v___x_935_, v_expectedInst_933_);
v___x_937_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v___x_936_, v___f_918_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_inst_942_){
_start:
{
lean_object* v_toApplicative_943_; lean_object* v_toBind_944_; lean_object* v_getRing_945_; lean_object* v_modifyRing_946_; lean_object* v_toPure_947_; lean_object* v___f_948_; lean_object* v___f_949_; lean_object* v___x_950_; 
v_toApplicative_943_ = lean_ctor_get(v_inst_940_, 0);
v_toBind_944_ = lean_ctor_get(v_inst_940_, 1);
lean_inc_n(v_toBind_944_, 3);
v_getRing_945_ = lean_ctor_get(v_inst_942_, 0);
lean_inc(v_getRing_945_);
v_modifyRing_946_ = lean_ctor_get(v_inst_942_, 1);
lean_inc(v_modifyRing_946_);
lean_dec_ref(v_inst_942_);
v_toPure_947_ = lean_ctor_get(v_toApplicative_943_, 1);
lean_inc_n(v_toPure_947_, 2);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_948_, 0, v_toPure_947_);
lean_closure_set(v___f_948_, 1, v_modifyRing_946_);
lean_closure_set(v___f_948_, 2, v_toBind_944_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_949_, 0, v_toPure_947_);
lean_closure_set(v___f_949_, 1, v_inst_938_);
lean_closure_set(v___f_949_, 2, v_inst_939_);
lean_closure_set(v___f_949_, 3, v_inst_940_);
lean_closure_set(v___f_949_, 4, v_inst_941_);
lean_closure_set(v___f_949_, 5, v_toBind_944_);
lean_closure_set(v___f_949_, 6, v___f_948_);
v___x_950_ = lean_apply_4(v_toBind_944_, lean_box(0), lean_box(0), v_getRing_945_, v___f_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_inst_955_, lean_object* v_inst_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_952_, v_inst_953_, v_inst_954_, v_inst_955_, v_inst_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_958_, lean_object* v_s_959_){
_start:
{
lean_object* v_id_960_; lean_object* v_type_961_; lean_object* v_u_962_; lean_object* v_ringInst_963_; lean_object* v_semiringInst_964_; lean_object* v_charInst_x3f_965_; lean_object* v_addFn_x3f_966_; lean_object* v_mulFn_x3f_967_; lean_object* v_subFn_x3f_968_; lean_object* v_powFn_x3f_969_; lean_object* v_intCastFn_x3f_970_; lean_object* v_natCastFn_x3f_971_; lean_object* v_natSMulFn_x3f_972_; lean_object* v_intSMulFn_x3f_973_; lean_object* v_one_x3f_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v_id_960_ = lean_ctor_get(v_s_959_, 0);
v_type_961_ = lean_ctor_get(v_s_959_, 1);
v_u_962_ = lean_ctor_get(v_s_959_, 2);
v_ringInst_963_ = lean_ctor_get(v_s_959_, 3);
v_semiringInst_964_ = lean_ctor_get(v_s_959_, 4);
v_charInst_x3f_965_ = lean_ctor_get(v_s_959_, 5);
v_addFn_x3f_966_ = lean_ctor_get(v_s_959_, 6);
v_mulFn_x3f_967_ = lean_ctor_get(v_s_959_, 7);
v_subFn_x3f_968_ = lean_ctor_get(v_s_959_, 8);
v_powFn_x3f_969_ = lean_ctor_get(v_s_959_, 10);
v_intCastFn_x3f_970_ = lean_ctor_get(v_s_959_, 11);
v_natCastFn_x3f_971_ = lean_ctor_get(v_s_959_, 12);
v_natSMulFn_x3f_972_ = lean_ctor_get(v_s_959_, 13);
v_intSMulFn_x3f_973_ = lean_ctor_get(v_s_959_, 14);
v_one_x3f_974_ = lean_ctor_get(v_s_959_, 15);
v_isSharedCheck_982_ = !lean_is_exclusive(v_s_959_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_s_959_, 9);
lean_dec(v_unused_983_);
v___x_976_ = v_s_959_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_one_x3f_974_);
lean_inc(v_intSMulFn_x3f_973_);
lean_inc(v_natSMulFn_x3f_972_);
lean_inc(v_natCastFn_x3f_971_);
lean_inc(v_intCastFn_x3f_970_);
lean_inc(v_powFn_x3f_969_);
lean_inc(v_subFn_x3f_968_);
lean_inc(v_mulFn_x3f_967_);
lean_inc(v_addFn_x3f_966_);
lean_inc(v_charInst_x3f_965_);
lean_inc(v_semiringInst_964_);
lean_inc(v_ringInst_963_);
lean_inc(v_u_962_);
lean_inc(v_type_961_);
lean_inc(v_id_960_);
lean_dec(v_s_959_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_negFn_958_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 9, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_id_960_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_type_961_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_u_962_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_ringInst_963_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_semiringInst_964_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_charInst_x3f_965_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_addFn_x3f_966_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v_mulFn_x3f_967_);
lean_ctor_set(v_reuseFailAlloc_981_, 8, v_subFn_x3f_968_);
lean_ctor_set(v_reuseFailAlloc_981_, 9, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_981_, 10, v_powFn_x3f_969_);
lean_ctor_set(v_reuseFailAlloc_981_, 11, v_intCastFn_x3f_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 12, v_natCastFn_x3f_971_);
lean_ctor_set(v_reuseFailAlloc_981_, 13, v_natSMulFn_x3f_972_);
lean_ctor_set(v_reuseFailAlloc_981_, 14, v_intSMulFn_x3f_973_);
lean_ctor_set(v_reuseFailAlloc_981_, 15, v_one_x3f_974_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_984_, lean_object* v_negFn_985_, lean_object* v_____r_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_apply_2(v_toPure_984_, lean_box(0), v_negFn_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_988_, lean_object* v_modifyRing_989_, lean_object* v_toBind_990_, lean_object* v_negFn_991_){
_start:
{
lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_inc_ref(v_negFn_991_);
v___f_992_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_992_, 0, v_negFn_991_);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_993_, 0, v_toPure_988_);
lean_closure_set(v___f_993_, 1, v_negFn_991_);
v___x_994_ = lean_apply_1(v_modifyRing_989_, v___f_992_);
v___x_995_ = lean_apply_4(v_toBind_990_, lean_box(0), lean_box(0), v___x_994_, v___f_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_toBind_1014_, lean_object* v___f_1015_, lean_object* v_ring_1016_){
_start:
{
lean_object* v_negFn_x3f_1017_; 
v_negFn_x3f_1017_ = lean_ctor_get(v_ring_1016_, 9);
if (lean_obj_tag(v_negFn_x3f_1017_) == 1)
{
lean_object* v_val_1018_; lean_object* v___x_1019_; 
lean_inc_ref(v_negFn_x3f_1017_);
lean_dec_ref(v_ring_1016_);
lean_dec(v___f_1015_);
lean_dec(v_toBind_1014_);
lean_dec_ref(v_inst_1013_);
lean_dec_ref(v_inst_1012_);
lean_dec_ref(v_inst_1011_);
lean_dec(v_inst_1010_);
v_val_1018_ = lean_ctor_get(v_negFn_x3f_1017_, 0);
lean_inc(v_val_1018_);
lean_dec_ref_known(v_negFn_x3f_1017_, 1);
v___x_1019_ = lean_apply_2(v_toPure_1009_, lean_box(0), v_val_1018_);
return v___x_1019_;
}
else
{
lean_object* v_type_1020_; lean_object* v_u_1021_; lean_object* v_ringInst_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_expectedInst_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec(v_toPure_1009_);
v_type_1020_ = lean_ctor_get(v_ring_1016_, 1);
lean_inc_ref_n(v_type_1020_, 2);
v_u_1021_ = lean_ctor_get(v_ring_1016_, 2);
lean_inc_n(v_u_1021_, 2);
v_ringInst_1022_ = lean_ctor_get(v_ring_1016_, 3);
lean_inc_ref(v_ringInst_1022_);
lean_dec_ref(v_ring_1016_);
v___x_1023_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1025_, 0, v_u_1021_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Lean_mkConst(v___x_1023_, v___x_1025_);
v_expectedInst_1027_ = l_Lean_mkAppB(v___x_1026_, v_type_1020_, v_ringInst_1022_);
v___x_1028_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_1029_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_1030_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1010_, v_inst_1011_, v_inst_1012_, v_inst_1013_, v_type_1020_, v_u_1021_, v___x_1028_, v___x_1029_, v_expectedInst_1027_);
v___x_1031_ = lean_apply_4(v_toBind_1014_, lean_box(0), lean_box(0), v___x_1030_, v___f_1015_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_){
_start:
{
lean_object* v_toApplicative_1037_; lean_object* v_toBind_1038_; lean_object* v_getRing_1039_; lean_object* v_modifyRing_1040_; lean_object* v_toPure_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; 
v_toApplicative_1037_ = lean_ctor_get(v_inst_1034_, 0);
v_toBind_1038_ = lean_ctor_get(v_inst_1034_, 1);
lean_inc_n(v_toBind_1038_, 3);
v_getRing_1039_ = lean_ctor_get(v_inst_1036_, 0);
lean_inc(v_getRing_1039_);
v_modifyRing_1040_ = lean_ctor_get(v_inst_1036_, 1);
lean_inc(v_modifyRing_1040_);
lean_dec_ref(v_inst_1036_);
v_toPure_1041_ = lean_ctor_get(v_toApplicative_1037_, 1);
lean_inc_n(v_toPure_1041_, 2);
v___f_1042_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1042_, 0, v_toPure_1041_);
lean_closure_set(v___f_1042_, 1, v_modifyRing_1040_);
lean_closure_set(v___f_1042_, 2, v_toBind_1038_);
v___f_1043_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1043_, 0, v_toPure_1041_);
lean_closure_set(v___f_1043_, 1, v_inst_1032_);
lean_closure_set(v___f_1043_, 2, v_inst_1033_);
lean_closure_set(v___f_1043_, 3, v_inst_1034_);
lean_closure_set(v___f_1043_, 4, v_inst_1035_);
lean_closure_set(v___f_1043_, 5, v_toBind_1038_);
lean_closure_set(v___f_1043_, 6, v___f_1042_);
v___x_1044_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v_getRing_1039_, v___f_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_1046_, v_inst_1047_, v_inst_1048_, v_inst_1049_, v_inst_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_1052_, lean_object* v_s_1053_){
_start:
{
lean_object* v_id_1054_; lean_object* v_type_1055_; lean_object* v_u_1056_; lean_object* v_ringInst_1057_; lean_object* v_semiringInst_1058_; lean_object* v_charInst_x3f_1059_; lean_object* v_addFn_x3f_1060_; lean_object* v_mulFn_x3f_1061_; lean_object* v_subFn_x3f_1062_; lean_object* v_negFn_x3f_1063_; lean_object* v_intCastFn_x3f_1064_; lean_object* v_natCastFn_x3f_1065_; lean_object* v_natSMulFn_x3f_1066_; lean_object* v_intSMulFn_x3f_1067_; lean_object* v_one_x3f_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1076_; 
v_id_1054_ = lean_ctor_get(v_s_1053_, 0);
v_type_1055_ = lean_ctor_get(v_s_1053_, 1);
v_u_1056_ = lean_ctor_get(v_s_1053_, 2);
v_ringInst_1057_ = lean_ctor_get(v_s_1053_, 3);
v_semiringInst_1058_ = lean_ctor_get(v_s_1053_, 4);
v_charInst_x3f_1059_ = lean_ctor_get(v_s_1053_, 5);
v_addFn_x3f_1060_ = lean_ctor_get(v_s_1053_, 6);
v_mulFn_x3f_1061_ = lean_ctor_get(v_s_1053_, 7);
v_subFn_x3f_1062_ = lean_ctor_get(v_s_1053_, 8);
v_negFn_x3f_1063_ = lean_ctor_get(v_s_1053_, 9);
v_intCastFn_x3f_1064_ = lean_ctor_get(v_s_1053_, 11);
v_natCastFn_x3f_1065_ = lean_ctor_get(v_s_1053_, 12);
v_natSMulFn_x3f_1066_ = lean_ctor_get(v_s_1053_, 13);
v_intSMulFn_x3f_1067_ = lean_ctor_get(v_s_1053_, 14);
v_one_x3f_1068_ = lean_ctor_get(v_s_1053_, 15);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_s_1053_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_s_1053_, 10);
lean_dec(v_unused_1077_);
v___x_1070_ = v_s_1053_;
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_one_x3f_1068_);
lean_inc(v_intSMulFn_x3f_1067_);
lean_inc(v_natSMulFn_x3f_1066_);
lean_inc(v_natCastFn_x3f_1065_);
lean_inc(v_intCastFn_x3f_1064_);
lean_inc(v_negFn_x3f_1063_);
lean_inc(v_subFn_x3f_1062_);
lean_inc(v_mulFn_x3f_1061_);
lean_inc(v_addFn_x3f_1060_);
lean_inc(v_charInst_x3f_1059_);
lean_inc(v_semiringInst_1058_);
lean_inc(v_ringInst_1057_);
lean_inc(v_u_1056_);
lean_inc(v_type_1055_);
lean_inc(v_id_1054_);
lean_dec(v_s_1053_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_powFn_1052_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 10, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_id_1054_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_type_1055_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_u_1056_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_ringInst_1057_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_semiringInst_1058_);
lean_ctor_set(v_reuseFailAlloc_1075_, 5, v_charInst_x3f_1059_);
lean_ctor_set(v_reuseFailAlloc_1075_, 6, v_addFn_x3f_1060_);
lean_ctor_set(v_reuseFailAlloc_1075_, 7, v_mulFn_x3f_1061_);
lean_ctor_set(v_reuseFailAlloc_1075_, 8, v_subFn_x3f_1062_);
lean_ctor_set(v_reuseFailAlloc_1075_, 9, v_negFn_x3f_1063_);
lean_ctor_set(v_reuseFailAlloc_1075_, 10, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1075_, 11, v_intCastFn_x3f_1064_);
lean_ctor_set(v_reuseFailAlloc_1075_, 12, v_natCastFn_x3f_1065_);
lean_ctor_set(v_reuseFailAlloc_1075_, 13, v_natSMulFn_x3f_1066_);
lean_ctor_set(v_reuseFailAlloc_1075_, 14, v_intSMulFn_x3f_1067_);
lean_ctor_set(v_reuseFailAlloc_1075_, 15, v_one_x3f_1068_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_1078_, lean_object* v_powFn_1079_, lean_object* v_____r_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_apply_2(v_toPure_1078_, lean_box(0), v_powFn_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_1082_, lean_object* v_modifyRing_1083_, lean_object* v_toBind_1084_, lean_object* v_powFn_1085_){
_start:
{
lean_object* v___f_1086_; lean_object* v___f_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_inc_ref(v_powFn_1085_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1086_, 0, v_powFn_1085_);
v___f_1087_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1087_, 0, v_toPure_1082_);
lean_closure_set(v___f_1087_, 1, v_powFn_1085_);
v___x_1088_ = lean_apply_1(v_modifyRing_1083_, v___f_1086_);
v___x_1089_ = lean_apply_4(v_toBind_1084_, lean_box(0), lean_box(0), v___x_1088_, v___f_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_toBind_1095_, lean_object* v___f_1096_, lean_object* v_ring_1097_){
_start:
{
lean_object* v_powFn_x3f_1098_; 
v_powFn_x3f_1098_ = lean_ctor_get(v_ring_1097_, 10);
if (lean_obj_tag(v_powFn_x3f_1098_) == 1)
{
lean_object* v_val_1099_; lean_object* v___x_1100_; 
lean_inc_ref(v_powFn_x3f_1098_);
lean_dec_ref(v_ring_1097_);
lean_dec(v___f_1096_);
lean_dec(v_toBind_1095_);
lean_dec_ref(v_inst_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_inst_1092_);
lean_dec(v_inst_1091_);
v_val_1099_ = lean_ctor_get(v_powFn_x3f_1098_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v_powFn_x3f_1098_, 1);
v___x_1100_ = lean_apply_2(v_toPure_1090_, lean_box(0), v_val_1099_);
return v___x_1100_;
}
else
{
lean_object* v_type_1101_; lean_object* v_u_1102_; lean_object* v_semiringInst_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v_toPure_1090_);
v_type_1101_ = lean_ctor_get(v_ring_1097_, 1);
lean_inc_ref(v_type_1101_);
v_u_1102_ = lean_ctor_get(v_ring_1097_, 2);
lean_inc(v_u_1102_);
v_semiringInst_1103_ = lean_ctor_get(v_ring_1097_, 4);
lean_inc_ref(v_semiringInst_1103_);
lean_dec_ref(v_ring_1097_);
v___x_1104_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1091_, v_inst_1092_, v_inst_1093_, v_inst_1094_, v_u_1102_, v_type_1101_, v_semiringInst_1103_);
v___x_1105_ = lean_apply_4(v_toBind_1095_, lean_box(0), lean_box(0), v___x_1104_, v___f_1096_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_){
_start:
{
lean_object* v_toApplicative_1111_; lean_object* v_toBind_1112_; lean_object* v_getRing_1113_; lean_object* v_modifyRing_1114_; lean_object* v_toPure_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; 
v_toApplicative_1111_ = lean_ctor_get(v_inst_1108_, 0);
v_toBind_1112_ = lean_ctor_get(v_inst_1108_, 1);
lean_inc_n(v_toBind_1112_, 3);
v_getRing_1113_ = lean_ctor_get(v_inst_1110_, 0);
lean_inc(v_getRing_1113_);
v_modifyRing_1114_ = lean_ctor_get(v_inst_1110_, 1);
lean_inc(v_modifyRing_1114_);
lean_dec_ref(v_inst_1110_);
v_toPure_1115_ = lean_ctor_get(v_toApplicative_1111_, 1);
lean_inc_n(v_toPure_1115_, 2);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1116_, 0, v_toPure_1115_);
lean_closure_set(v___f_1116_, 1, v_modifyRing_1114_);
lean_closure_set(v___f_1116_, 2, v_toBind_1112_);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1117_, 0, v_toPure_1115_);
lean_closure_set(v___f_1117_, 1, v_inst_1106_);
lean_closure_set(v___f_1117_, 2, v_inst_1107_);
lean_closure_set(v___f_1117_, 3, v_inst_1108_);
lean_closure_set(v___f_1117_, 4, v_inst_1109_);
lean_closure_set(v___f_1117_, 5, v_toBind_1112_);
lean_closure_set(v___f_1117_, 6, v___f_1116_);
v___x_1118_ = lean_apply_4(v_toBind_1112_, lean_box(0), lean_box(0), v_getRing_1113_, v___f_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_1120_, v_inst_1121_, v_inst_1122_, v_inst_1123_, v_inst_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_1126_, lean_object* v_s_1127_){
_start:
{
lean_object* v_id_1128_; lean_object* v_type_1129_; lean_object* v_u_1130_; lean_object* v_ringInst_1131_; lean_object* v_semiringInst_1132_; lean_object* v_charInst_x3f_1133_; lean_object* v_addFn_x3f_1134_; lean_object* v_mulFn_x3f_1135_; lean_object* v_subFn_x3f_1136_; lean_object* v_negFn_x3f_1137_; lean_object* v_powFn_x3f_1138_; lean_object* v_natCastFn_x3f_1139_; lean_object* v_natSMulFn_x3f_1140_; lean_object* v_intSMulFn_x3f_1141_; lean_object* v_one_x3f_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_id_1128_ = lean_ctor_get(v_s_1127_, 0);
v_type_1129_ = lean_ctor_get(v_s_1127_, 1);
v_u_1130_ = lean_ctor_get(v_s_1127_, 2);
v_ringInst_1131_ = lean_ctor_get(v_s_1127_, 3);
v_semiringInst_1132_ = lean_ctor_get(v_s_1127_, 4);
v_charInst_x3f_1133_ = lean_ctor_get(v_s_1127_, 5);
v_addFn_x3f_1134_ = lean_ctor_get(v_s_1127_, 6);
v_mulFn_x3f_1135_ = lean_ctor_get(v_s_1127_, 7);
v_subFn_x3f_1136_ = lean_ctor_get(v_s_1127_, 8);
v_negFn_x3f_1137_ = lean_ctor_get(v_s_1127_, 9);
v_powFn_x3f_1138_ = lean_ctor_get(v_s_1127_, 10);
v_natCastFn_x3f_1139_ = lean_ctor_get(v_s_1127_, 12);
v_natSMulFn_x3f_1140_ = lean_ctor_get(v_s_1127_, 13);
v_intSMulFn_x3f_1141_ = lean_ctor_get(v_s_1127_, 14);
v_one_x3f_1142_ = lean_ctor_get(v_s_1127_, 15);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_s_1127_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_s_1127_, 11);
lean_dec(v_unused_1151_);
v___x_1144_ = v_s_1127_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_one_x3f_1142_);
lean_inc(v_intSMulFn_x3f_1141_);
lean_inc(v_natSMulFn_x3f_1140_);
lean_inc(v_natCastFn_x3f_1139_);
lean_inc(v_powFn_x3f_1138_);
lean_inc(v_negFn_x3f_1137_);
lean_inc(v_subFn_x3f_1136_);
lean_inc(v_mulFn_x3f_1135_);
lean_inc(v_addFn_x3f_1134_);
lean_inc(v_charInst_x3f_1133_);
lean_inc(v_semiringInst_1132_);
lean_inc(v_ringInst_1131_);
lean_inc(v_u_1130_);
lean_inc(v_type_1129_);
lean_inc(v_id_1128_);
lean_dec(v_s_1127_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_intCastFn_1126_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 11, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_id_1128_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_type_1129_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_u_1130_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_ringInst_1131_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_semiringInst_1132_);
lean_ctor_set(v_reuseFailAlloc_1149_, 5, v_charInst_x3f_1133_);
lean_ctor_set(v_reuseFailAlloc_1149_, 6, v_addFn_x3f_1134_);
lean_ctor_set(v_reuseFailAlloc_1149_, 7, v_mulFn_x3f_1135_);
lean_ctor_set(v_reuseFailAlloc_1149_, 8, v_subFn_x3f_1136_);
lean_ctor_set(v_reuseFailAlloc_1149_, 9, v_negFn_x3f_1137_);
lean_ctor_set(v_reuseFailAlloc_1149_, 10, v_powFn_x3f_1138_);
lean_ctor_set(v_reuseFailAlloc_1149_, 11, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 12, v_natCastFn_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 13, v_natSMulFn_x3f_1140_);
lean_ctor_set(v_reuseFailAlloc_1149_, 14, v_intSMulFn_x3f_1141_);
lean_ctor_set(v_reuseFailAlloc_1149_, 15, v_one_x3f_1142_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_1152_, lean_object* v_intCastFn_1153_, lean_object* v_____r_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_apply_2(v_toPure_1152_, lean_box(0), v_intCastFn_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_1156_, lean_object* v_modifyRing_1157_, lean_object* v_toBind_1158_, lean_object* v_intCastFn_1159_){
_start:
{
lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_inc_ref(v_intCastFn_1159_);
v___f_1160_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1160_, 0, v_intCastFn_1159_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1161_, 0, v_toPure_1156_);
lean_closure_set(v___f_1161_, 1, v_intCastFn_1159_);
v___x_1162_ = lean_apply_1(v_modifyRing_1157_, v___f_1160_);
v___x_1163_ = lean_apply_4(v_toBind_1158_, lean_box(0), lean_box(0), v___x_1162_, v___f_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v_type_1167_, lean_object* v_canonExpr_1168_, lean_object* v_toBind_1169_, lean_object* v___f_1170_, lean_object* v_inst_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1172_ = l_Lean_Name_mkStr2(v___x_1164_, v___x_1165_);
v___x_1173_ = l_Lean_mkConst(v___x_1172_, v___x_1166_);
v___x_1174_ = l_Lean_mkAppB(v___x_1173_, v_type_1167_, v_inst_1171_);
v___x_1175_ = lean_apply_1(v_canonExpr_1168_, v___x_1174_);
v___x_1176_ = lean_apply_4(v_toBind_1169_, lean_box(0), lean_box(0), v___x_1175_, v___f_1170_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_1182_, lean_object* v_inst_x27_1183_, lean_object* v_toBind_1184_, lean_object* v___f_1185_, lean_object* v___f_1186_, lean_object* v_inst_1187_, lean_object* v_____do__lift_1188_){
_start:
{
if (lean_obj_tag(v_____do__lift_1188_) == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_inst_1187_);
lean_dec(v___f_1186_);
v___x_1189_ = lean_apply_2(v_toPure_1182_, lean_box(0), v_inst_x27_1183_);
v___x_1190_ = lean_apply_4(v_toBind_1184_, lean_box(0), lean_box(0), v___x_1189_, v___f_1185_);
return v___x_1190_;
}
else
{
lean_object* v_val_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v___f_1185_);
v_val_1191_ = lean_ctor_get(v_____do__lift_1188_, 0);
lean_inc_n(v_val_1191_, 2);
lean_dec_ref_known(v_____do__lift_1188_, 1);
lean_inc(v_toBind_1184_);
v___f_1192_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1192_, 0, v_toPure_1182_);
lean_closure_set(v___f_1192_, 1, v_val_1191_);
lean_closure_set(v___f_1192_, 2, v_toBind_1184_);
lean_closure_set(v___f_1192_, 3, v___f_1186_);
v___x_1193_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_1194_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_1194_, 0, v___x_1193_);
lean_closure_set(v___x_1194_, 1, v_val_1191_);
lean_closure_set(v___x_1194_, 2, v_inst_x27_1183_);
v___x_1195_ = lean_apply_2(v_inst_1187_, lean_box(0), v___x_1194_);
v___x_1196_ = lean_apply_4(v_toBind_1184_, lean_box(0), lean_box(0), v___x_1195_, v___f_1192_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_1206_, lean_object* v_inst_1207_, lean_object* v_toBind_1208_, lean_object* v___f_1209_, lean_object* v_inst_1210_, lean_object* v_ring_1211_){
_start:
{
lean_object* v_intCastFn_x3f_1212_; 
v_intCastFn_x3f_1212_ = lean_ctor_get(v_ring_1211_, 11);
if (lean_obj_tag(v_intCastFn_x3f_1212_) == 1)
{
lean_object* v_val_1213_; lean_object* v___x_1214_; 
lean_inc_ref(v_intCastFn_x3f_1212_);
lean_dec_ref(v_ring_1211_);
lean_dec(v_inst_1210_);
lean_dec(v___f_1209_);
lean_dec(v_toBind_1208_);
lean_dec_ref(v_inst_1207_);
v_val_1213_ = lean_ctor_get(v_intCastFn_x3f_1212_, 0);
lean_inc(v_val_1213_);
lean_dec_ref_known(v_intCastFn_x3f_1212_, 1);
v___x_1214_ = lean_apply_2(v_toPure_1206_, lean_box(0), v_val_1213_);
return v___x_1214_;
}
else
{
lean_object* v_type_1215_; lean_object* v_u_1216_; lean_object* v_ringInst_1217_; lean_object* v_canonExpr_1218_; lean_object* v_synthInstance_x3f_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1240_; 
v_type_1215_ = lean_ctor_get(v_ring_1211_, 1);
lean_inc_ref(v_type_1215_);
v_u_1216_ = lean_ctor_get(v_ring_1211_, 2);
lean_inc(v_u_1216_);
v_ringInst_1217_ = lean_ctor_get(v_ring_1211_, 3);
lean_inc_ref(v_ringInst_1217_);
lean_dec_ref(v_ring_1211_);
v_canonExpr_1218_ = lean_ctor_get(v_inst_1207_, 0);
v_synthInstance_x3f_1219_ = lean_ctor_get(v_inst_1207_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_inst_1207_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1221_ = v_inst_1207_;
v_isShared_1222_ = v_isSharedCheck_1240_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_synthInstance_x3f_1219_);
lean_inc(v_canonExpr_1218_);
lean_dec(v_inst_1207_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1240_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_1224_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_1225_ = lean_box(0);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
lean_ctor_set(v___x_1221_, 1, v___x_1225_);
lean_ctor_set(v___x_1221_, 0, v_u_1216_);
v___x_1227_ = v___x_1221_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_u_1216_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v_inst_x27_1229_; lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_instType_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_inc_ref_n(v___x_1227_, 2);
v___x_1228_ = l_Lean_mkConst(v___x_1224_, v___x_1227_);
lean_inc_ref_n(v_type_1215_, 2);
v_inst_x27_1229_ = l_Lean_mkAppB(v___x_1228_, v_type_1215_, v_ringInst_1217_);
v___x_1230_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_1208_, 2);
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1231_, 0, v___x_1230_);
lean_closure_set(v___f_1231_, 1, v___x_1223_);
lean_closure_set(v___f_1231_, 2, v___x_1227_);
lean_closure_set(v___f_1231_, 3, v_type_1215_);
lean_closure_set(v___f_1231_, 4, v_canonExpr_1218_);
lean_closure_set(v___f_1231_, 5, v_toBind_1208_);
lean_closure_set(v___f_1231_, 6, v___f_1209_);
v___f_1232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1232_, 0, v___f_1231_);
lean_inc_ref(v___f_1232_);
v___f_1233_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_1233_, 0, v_toPure_1206_);
lean_closure_set(v___f_1233_, 1, v_inst_x27_1229_);
lean_closure_set(v___f_1233_, 2, v_toBind_1208_);
lean_closure_set(v___f_1233_, 3, v___f_1232_);
lean_closure_set(v___f_1233_, 4, v___f_1232_);
lean_closure_set(v___f_1233_, 5, v_inst_1210_);
v___x_1234_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_1235_ = l_Lean_mkConst(v___x_1234_, v___x_1227_);
v_instType_1236_ = l_Lean_Expr_app___override(v___x_1235_, v_type_1215_);
v___x_1237_ = lean_apply_1(v_synthInstance_x3f_1219_, v_instType_1236_);
v___x_1238_ = lean_apply_4(v_toBind_1208_, lean_box(0), lean_box(0), v___x_1237_, v___f_1233_);
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_){
_start:
{
lean_object* v_toApplicative_1245_; lean_object* v_toBind_1246_; lean_object* v_getRing_1247_; lean_object* v_modifyRing_1248_; lean_object* v_toPure_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; 
v_toApplicative_1245_ = lean_ctor_get(v_inst_1242_, 0);
lean_inc_ref(v_toApplicative_1245_);
v_toBind_1246_ = lean_ctor_get(v_inst_1242_, 1);
lean_inc_n(v_toBind_1246_, 3);
lean_dec_ref(v_inst_1242_);
v_getRing_1247_ = lean_ctor_get(v_inst_1244_, 0);
lean_inc(v_getRing_1247_);
v_modifyRing_1248_ = lean_ctor_get(v_inst_1244_, 1);
lean_inc(v_modifyRing_1248_);
lean_dec_ref(v_inst_1244_);
v_toPure_1249_ = lean_ctor_get(v_toApplicative_1245_, 1);
lean_inc_n(v_toPure_1249_, 2);
lean_dec_ref(v_toApplicative_1245_);
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1250_, 0, v_toPure_1249_);
lean_closure_set(v___f_1250_, 1, v_modifyRing_1248_);
lean_closure_set(v___f_1250_, 2, v_toBind_1246_);
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_1251_, 0, v_toPure_1249_);
lean_closure_set(v___f_1251_, 1, v_inst_1243_);
lean_closure_set(v___f_1251_, 2, v_toBind_1246_);
lean_closure_set(v___f_1251_, 3, v___f_1250_);
lean_closure_set(v___f_1251_, 4, v_inst_1241_);
v___x_1252_ = lean_apply_4(v_toBind_1246_, lean_box(0), lean_box(0), v_getRing_1247_, v___f_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_1254_, v_inst_1255_, v_inst_1256_, v_inst_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_1259_, lean_object* v_s_1260_){
_start:
{
lean_object* v_id_1261_; lean_object* v_type_1262_; lean_object* v_u_1263_; lean_object* v_ringInst_1264_; lean_object* v_semiringInst_1265_; lean_object* v_charInst_x3f_1266_; lean_object* v_addFn_x3f_1267_; lean_object* v_mulFn_x3f_1268_; lean_object* v_subFn_x3f_1269_; lean_object* v_negFn_x3f_1270_; lean_object* v_powFn_x3f_1271_; lean_object* v_intCastFn_x3f_1272_; lean_object* v_natSMulFn_x3f_1273_; lean_object* v_intSMulFn_x3f_1274_; lean_object* v_one_x3f_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1283_; 
v_id_1261_ = lean_ctor_get(v_s_1260_, 0);
v_type_1262_ = lean_ctor_get(v_s_1260_, 1);
v_u_1263_ = lean_ctor_get(v_s_1260_, 2);
v_ringInst_1264_ = lean_ctor_get(v_s_1260_, 3);
v_semiringInst_1265_ = lean_ctor_get(v_s_1260_, 4);
v_charInst_x3f_1266_ = lean_ctor_get(v_s_1260_, 5);
v_addFn_x3f_1267_ = lean_ctor_get(v_s_1260_, 6);
v_mulFn_x3f_1268_ = lean_ctor_get(v_s_1260_, 7);
v_subFn_x3f_1269_ = lean_ctor_get(v_s_1260_, 8);
v_negFn_x3f_1270_ = lean_ctor_get(v_s_1260_, 9);
v_powFn_x3f_1271_ = lean_ctor_get(v_s_1260_, 10);
v_intCastFn_x3f_1272_ = lean_ctor_get(v_s_1260_, 11);
v_natSMulFn_x3f_1273_ = lean_ctor_get(v_s_1260_, 13);
v_intSMulFn_x3f_1274_ = lean_ctor_get(v_s_1260_, 14);
v_one_x3f_1275_ = lean_ctor_get(v_s_1260_, 15);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_s_1260_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v_s_1260_, 12);
lean_dec(v_unused_1284_);
v___x_1277_ = v_s_1260_;
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_one_x3f_1275_);
lean_inc(v_intSMulFn_x3f_1274_);
lean_inc(v_natSMulFn_x3f_1273_);
lean_inc(v_intCastFn_x3f_1272_);
lean_inc(v_powFn_x3f_1271_);
lean_inc(v_negFn_x3f_1270_);
lean_inc(v_subFn_x3f_1269_);
lean_inc(v_mulFn_x3f_1268_);
lean_inc(v_addFn_x3f_1267_);
lean_inc(v_charInst_x3f_1266_);
lean_inc(v_semiringInst_1265_);
lean_inc(v_ringInst_1264_);
lean_inc(v_u_1263_);
lean_inc(v_type_1262_);
lean_inc(v_id_1261_);
lean_dec(v_s_1260_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_natCastFn_1259_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 12, v___x_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_id_1261_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_type_1262_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_u_1263_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_ringInst_1264_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_semiringInst_1265_);
lean_ctor_set(v_reuseFailAlloc_1282_, 5, v_charInst_x3f_1266_);
lean_ctor_set(v_reuseFailAlloc_1282_, 6, v_addFn_x3f_1267_);
lean_ctor_set(v_reuseFailAlloc_1282_, 7, v_mulFn_x3f_1268_);
lean_ctor_set(v_reuseFailAlloc_1282_, 8, v_subFn_x3f_1269_);
lean_ctor_set(v_reuseFailAlloc_1282_, 9, v_negFn_x3f_1270_);
lean_ctor_set(v_reuseFailAlloc_1282_, 10, v_powFn_x3f_1271_);
lean_ctor_set(v_reuseFailAlloc_1282_, 11, v_intCastFn_x3f_1272_);
lean_ctor_set(v_reuseFailAlloc_1282_, 12, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1282_, 13, v_natSMulFn_x3f_1273_);
lean_ctor_set(v_reuseFailAlloc_1282_, 14, v_intSMulFn_x3f_1274_);
lean_ctor_set(v_reuseFailAlloc_1282_, 15, v_one_x3f_1275_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1285_, lean_object* v_natCastFn_1286_, lean_object* v_____r_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_apply_2(v_toPure_1285_, lean_box(0), v_natCastFn_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1289_, lean_object* v_modifyRing_1290_, lean_object* v_toBind_1291_, lean_object* v_natCastFn_1292_){
_start:
{
lean_object* v___f_1293_; lean_object* v___f_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_inc_ref(v_natCastFn_1292_);
v___f_1293_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1293_, 0, v_natCastFn_1292_);
v___f_1294_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1294_, 0, v_toPure_1289_);
lean_closure_set(v___f_1294_, 1, v_natCastFn_1292_);
v___x_1295_ = lean_apply_1(v_modifyRing_1290_, v___f_1293_);
v___x_1296_ = lean_apply_4(v_toBind_1291_, lean_box(0), lean_box(0), v___x_1295_, v___f_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_toBind_1301_, lean_object* v___f_1302_, lean_object* v_ring_1303_){
_start:
{
lean_object* v_natCastFn_x3f_1304_; 
v_natCastFn_x3f_1304_ = lean_ctor_get(v_ring_1303_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1304_) == 1)
{
lean_object* v_val_1305_; lean_object* v___x_1306_; 
lean_inc_ref(v_natCastFn_x3f_1304_);
lean_dec_ref(v_ring_1303_);
lean_dec(v___f_1302_);
lean_dec(v_toBind_1301_);
lean_dec_ref(v_inst_1300_);
lean_dec_ref(v_inst_1299_);
lean_dec(v_inst_1298_);
v_val_1305_ = lean_ctor_get(v_natCastFn_x3f_1304_, 0);
lean_inc(v_val_1305_);
lean_dec_ref_known(v_natCastFn_x3f_1304_, 1);
v___x_1306_ = lean_apply_2(v_toPure_1297_, lean_box(0), v_val_1305_);
return v___x_1306_;
}
else
{
lean_object* v_type_1307_; lean_object* v_u_1308_; lean_object* v_semiringInst_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_toPure_1297_);
v_type_1307_ = lean_ctor_get(v_ring_1303_, 1);
lean_inc_ref(v_type_1307_);
v_u_1308_ = lean_ctor_get(v_ring_1303_, 2);
lean_inc(v_u_1308_);
v_semiringInst_1309_ = lean_ctor_get(v_ring_1303_, 4);
lean_inc_ref(v_semiringInst_1309_);
lean_dec_ref(v_ring_1303_);
v___x_1310_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1298_, v_inst_1299_, v_inst_1300_, v_u_1308_, v_type_1307_, v_semiringInst_1309_);
v___x_1311_ = lean_apply_4(v_toBind_1301_, lean_box(0), lean_box(0), v___x_1310_, v___f_1302_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_){
_start:
{
lean_object* v_toApplicative_1316_; lean_object* v_toBind_1317_; lean_object* v_getRing_1318_; lean_object* v_modifyRing_1319_; lean_object* v_toPure_1320_; lean_object* v___f_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; 
v_toApplicative_1316_ = lean_ctor_get(v_inst_1313_, 0);
v_toBind_1317_ = lean_ctor_get(v_inst_1313_, 1);
lean_inc_n(v_toBind_1317_, 3);
v_getRing_1318_ = lean_ctor_get(v_inst_1315_, 0);
lean_inc(v_getRing_1318_);
v_modifyRing_1319_ = lean_ctor_get(v_inst_1315_, 1);
lean_inc(v_modifyRing_1319_);
lean_dec_ref(v_inst_1315_);
v_toPure_1320_ = lean_ctor_get(v_toApplicative_1316_, 1);
lean_inc_n(v_toPure_1320_, 2);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1321_, 0, v_toPure_1320_);
lean_closure_set(v___f_1321_, 1, v_modifyRing_1319_);
lean_closure_set(v___f_1321_, 2, v_toBind_1317_);
v___f_1322_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1322_, 0, v_toPure_1320_);
lean_closure_set(v___f_1322_, 1, v_inst_1312_);
lean_closure_set(v___f_1322_, 2, v_inst_1313_);
lean_closure_set(v___f_1322_, 3, v_inst_1314_);
lean_closure_set(v___f_1322_, 4, v_toBind_1317_);
lean_closure_set(v___f_1322_, 5, v___f_1321_);
v___x_1323_ = lean_apply_4(v_toBind_1317_, lean_box(0), lean_box(0), v_getRing_1318_, v___f_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1325_, v_inst_1326_, v_inst_1327_, v_inst_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1330_, lean_object* v_s_1331_){
_start:
{
lean_object* v_toRing_1332_; lean_object* v_divFn_x3f_1333_; lean_object* v_semiringId_x3f_1334_; lean_object* v_commSemiringInst_1335_; lean_object* v_commRingInst_1336_; lean_object* v_noZeroDivInst_x3f_1337_; lean_object* v_fieldInst_x3f_1338_; lean_object* v_powIdentityInst_x3f_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_toRing_1332_ = lean_ctor_get(v_s_1331_, 0);
v_divFn_x3f_1333_ = lean_ctor_get(v_s_1331_, 2);
v_semiringId_x3f_1334_ = lean_ctor_get(v_s_1331_, 3);
v_commSemiringInst_1335_ = lean_ctor_get(v_s_1331_, 4);
v_commRingInst_1336_ = lean_ctor_get(v_s_1331_, 5);
v_noZeroDivInst_x3f_1337_ = lean_ctor_get(v_s_1331_, 6);
v_fieldInst_x3f_1338_ = lean_ctor_get(v_s_1331_, 7);
v_powIdentityInst_x3f_1339_ = lean_ctor_get(v_s_1331_, 8);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_s_1331_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v_s_1331_, 1);
lean_dec(v_unused_1348_);
v___x_1341_ = v_s_1331_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1339_);
lean_inc(v_fieldInst_x3f_1338_);
lean_inc(v_noZeroDivInst_x3f_1337_);
lean_inc(v_commRingInst_1336_);
lean_inc(v_commSemiringInst_1335_);
lean_inc(v_semiringId_x3f_1334_);
lean_inc(v_divFn_x3f_1333_);
lean_inc(v_toRing_1332_);
lean_dec(v_s_1331_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_invFn_1330_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_toRing_1332_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_divFn_x3f_1333_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_semiringId_x3f_1334_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_commSemiringInst_1335_);
lean_ctor_set(v_reuseFailAlloc_1346_, 5, v_commRingInst_1336_);
lean_ctor_set(v_reuseFailAlloc_1346_, 6, v_noZeroDivInst_x3f_1337_);
lean_ctor_set(v_reuseFailAlloc_1346_, 7, v_fieldInst_x3f_1338_);
lean_ctor_set(v_reuseFailAlloc_1346_, 8, v_powIdentityInst_x3f_1339_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1349_, lean_object* v_invFn_1350_, lean_object* v_____r_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_apply_2(v_toPure_1349_, lean_box(0), v_invFn_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1353_, lean_object* v_modifyCommRing_1354_, lean_object* v_toBind_1355_, lean_object* v_invFn_1356_){
_start:
{
lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_inc_ref(v_invFn_1356_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1357_, 0, v_invFn_1356_);
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1358_, 0, v_toPure_1353_);
lean_closure_set(v___f_1358_, 1, v_invFn_1356_);
v___x_1359_ = lean_apply_1(v_modifyCommRing_1354_, v___f_1357_);
v___x_1360_ = lean_apply_4(v_toBind_1355_, lean_box(0), lean_box(0), v___x_1359_, v___f_1358_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_toBind_1383_, lean_object* v___f_1384_, lean_object* v_ring_1385_){
_start:
{
lean_object* v_fieldInst_x3f_1386_; 
v_fieldInst_x3f_1386_ = lean_ctor_get(v_ring_1385_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1386_) == 1)
{
lean_object* v_invFn_x3f_1387_; 
lean_inc_ref(v_fieldInst_x3f_1386_);
v_invFn_x3f_1387_ = lean_ctor_get(v_ring_1385_, 1);
if (lean_obj_tag(v_invFn_x3f_1387_) == 1)
{
lean_object* v_val_1388_; lean_object* v___x_1389_; 
lean_inc_ref(v_invFn_x3f_1387_);
lean_dec_ref_known(v_fieldInst_x3f_1386_, 1);
lean_dec_ref(v_ring_1385_);
lean_dec(v___f_1384_);
lean_dec(v_toBind_1383_);
lean_dec_ref(v_inst_1382_);
lean_dec_ref(v_inst_1381_);
lean_dec_ref(v_inst_1380_);
lean_dec(v_inst_1379_);
v_val_1388_ = lean_ctor_get(v_invFn_x3f_1387_, 0);
lean_inc(v_val_1388_);
lean_dec_ref_known(v_invFn_x3f_1387_, 1);
v___x_1389_ = lean_apply_2(v_toPure_1378_, lean_box(0), v_val_1388_);
return v___x_1389_;
}
else
{
lean_object* v_toRing_1390_; lean_object* v_val_1391_; lean_object* v_type_1392_; lean_object* v_u_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_expectedInst_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v_toPure_1378_);
v_toRing_1390_ = lean_ctor_get(v_ring_1385_, 0);
lean_inc_ref(v_toRing_1390_);
lean_dec_ref(v_ring_1385_);
v_val_1391_ = lean_ctor_get(v_fieldInst_x3f_1386_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v_fieldInst_x3f_1386_, 1);
v_type_1392_ = lean_ctor_get(v_toRing_1390_, 1);
lean_inc_ref_n(v_type_1392_, 2);
v_u_1393_ = lean_ctor_get(v_toRing_1390_, 2);
lean_inc_n(v_u_1393_, 2);
lean_dec_ref(v_toRing_1390_);
v___x_1394_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_u_1393_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_mkConst(v___x_1394_, v___x_1396_);
v_expectedInst_1398_ = l_Lean_mkAppB(v___x_1397_, v_type_1392_, v_val_1391_);
v___x_1399_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1400_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1401_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1379_, v_inst_1380_, v_inst_1381_, v_inst_1382_, v_type_1392_, v_u_1393_, v___x_1399_, v___x_1400_, v_expectedInst_1398_);
v___x_1402_ = lean_apply_4(v_toBind_1383_, lean_box(0), lean_box(0), v___x_1401_, v___f_1384_);
return v___x_1402_;
}
}
else
{
lean_object* v_toRing_1403_; lean_object* v_type_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec(v___f_1384_);
lean_dec(v_toBind_1383_);
lean_dec_ref(v_inst_1382_);
lean_dec(v_inst_1379_);
lean_dec(v_toPure_1378_);
v_toRing_1403_ = lean_ctor_get(v_ring_1385_, 0);
lean_inc_ref(v_toRing_1403_);
lean_dec_ref(v_ring_1385_);
v_type_1404_ = lean_ctor_get(v_toRing_1403_, 1);
lean_inc_ref(v_type_1404_);
lean_dec_ref(v_toRing_1403_);
v___x_1405_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1406_ = l_Lean_indentExpr(v_type_1404_);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Lean_throwError___redArg(v_inst_1381_, v_inst_1380_, v___x_1407_);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_){
_start:
{
lean_object* v_toApplicative_1414_; lean_object* v_toBind_1415_; lean_object* v_getCommRing_1416_; lean_object* v_modifyCommRing_1417_; lean_object* v_toPure_1418_; lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; 
v_toApplicative_1414_ = lean_ctor_get(v_inst_1411_, 0);
v_toBind_1415_ = lean_ctor_get(v_inst_1411_, 1);
lean_inc_n(v_toBind_1415_, 3);
v_getCommRing_1416_ = lean_ctor_get(v_inst_1413_, 0);
lean_inc(v_getCommRing_1416_);
v_modifyCommRing_1417_ = lean_ctor_get(v_inst_1413_, 1);
lean_inc(v_modifyCommRing_1417_);
lean_dec_ref(v_inst_1413_);
v_toPure_1418_ = lean_ctor_get(v_toApplicative_1414_, 1);
lean_inc_n(v_toPure_1418_, 2);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1419_, 0, v_toPure_1418_);
lean_closure_set(v___f_1419_, 1, v_modifyCommRing_1417_);
lean_closure_set(v___f_1419_, 2, v_toBind_1415_);
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1420_, 0, v_toPure_1418_);
lean_closure_set(v___f_1420_, 1, v_inst_1409_);
lean_closure_set(v___f_1420_, 2, v_inst_1410_);
lean_closure_set(v___f_1420_, 3, v_inst_1411_);
lean_closure_set(v___f_1420_, 4, v_inst_1412_);
lean_closure_set(v___f_1420_, 5, v_toBind_1415_);
lean_closure_set(v___f_1420_, 6, v___f_1419_);
v___x_1421_ = lean_apply_4(v_toBind_1415_, lean_box(0), lean_box(0), v_getCommRing_1416_, v___f_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1423_, v_inst_1424_, v_inst_1425_, v_inst_1426_, v_inst_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0(lean_object* v_divFn_1429_, lean_object* v_s_1430_){
_start:
{
lean_object* v_toRing_1431_; lean_object* v_invFn_x3f_1432_; lean_object* v_semiringId_x3f_1433_; lean_object* v_commSemiringInst_1434_; lean_object* v_commRingInst_1435_; lean_object* v_noZeroDivInst_x3f_1436_; lean_object* v_fieldInst_x3f_1437_; lean_object* v_powIdentityInst_x3f_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
v_toRing_1431_ = lean_ctor_get(v_s_1430_, 0);
v_invFn_x3f_1432_ = lean_ctor_get(v_s_1430_, 1);
v_semiringId_x3f_1433_ = lean_ctor_get(v_s_1430_, 3);
v_commSemiringInst_1434_ = lean_ctor_get(v_s_1430_, 4);
v_commRingInst_1435_ = lean_ctor_get(v_s_1430_, 5);
v_noZeroDivInst_x3f_1436_ = lean_ctor_get(v_s_1430_, 6);
v_fieldInst_x3f_1437_ = lean_ctor_get(v_s_1430_, 7);
v_powIdentityInst_x3f_1438_ = lean_ctor_get(v_s_1430_, 8);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_s_1430_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_s_1430_, 2);
lean_dec(v_unused_1447_);
v___x_1440_ = v_s_1430_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1438_);
lean_inc(v_fieldInst_x3f_1437_);
lean_inc(v_noZeroDivInst_x3f_1436_);
lean_inc(v_commRingInst_1435_);
lean_inc(v_commSemiringInst_1434_);
lean_inc(v_semiringId_x3f_1433_);
lean_inc(v_invFn_x3f_1432_);
lean_inc(v_toRing_1431_);
lean_dec(v_s_1430_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_divFn_1429_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 2, v___x_1442_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_toRing_1431_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_invFn_x3f_1432_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_semiringId_x3f_1433_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_commSemiringInst_1434_);
lean_ctor_set(v_reuseFailAlloc_1445_, 5, v_commRingInst_1435_);
lean_ctor_set(v_reuseFailAlloc_1445_, 6, v_noZeroDivInst_x3f_1436_);
lean_ctor_set(v_reuseFailAlloc_1445_, 7, v_fieldInst_x3f_1437_);
lean_ctor_set(v_reuseFailAlloc_1445_, 8, v_powIdentityInst_x3f_1438_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1(lean_object* v_toPure_1448_, lean_object* v_divFn_1449_, lean_object* v_____r_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_apply_2(v_toPure_1448_, lean_box(0), v_divFn_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2(lean_object* v_toPure_1452_, lean_object* v_modifyCommRing_1453_, lean_object* v_toBind_1454_, lean_object* v_divFn_1455_){
_start:
{
lean_object* v___f_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_inc_ref(v_divFn_1455_);
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1456_, 0, v_divFn_1455_);
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1457_, 0, v_toPure_1452_);
lean_closure_set(v___f_1457_, 1, v_divFn_1455_);
v___x_1458_ = lean_apply_1(v_modifyCommRing_1453_, v___f_1456_);
v___x_1459_ = lean_apply_4(v_toBind_1454_, lean_box(0), lean_box(0), v___x_1458_, v___f_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3(lean_object* v_toPure_1476_, lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_toBind_1481_, lean_object* v___f_1482_, lean_object* v_ring_1483_){
_start:
{
lean_object* v_fieldInst_x3f_1484_; 
v_fieldInst_x3f_1484_ = lean_ctor_get(v_ring_1483_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1484_) == 1)
{
lean_object* v_divFn_x3f_1485_; 
lean_inc_ref(v_fieldInst_x3f_1484_);
v_divFn_x3f_1485_ = lean_ctor_get(v_ring_1483_, 2);
if (lean_obj_tag(v_divFn_x3f_1485_) == 1)
{
lean_object* v_val_1486_; lean_object* v___x_1487_; 
lean_inc_ref(v_divFn_x3f_1485_);
lean_dec_ref_known(v_fieldInst_x3f_1484_, 1);
lean_dec_ref(v_ring_1483_);
lean_dec(v___f_1482_);
lean_dec(v_toBind_1481_);
lean_dec_ref(v_inst_1480_);
lean_dec_ref(v_inst_1479_);
lean_dec_ref(v_inst_1478_);
lean_dec(v_inst_1477_);
v_val_1486_ = lean_ctor_get(v_divFn_x3f_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v_divFn_x3f_1485_, 1);
v___x_1487_ = lean_apply_2(v_toPure_1476_, lean_box(0), v_val_1486_);
return v___x_1487_;
}
else
{
lean_object* v_toRing_1488_; lean_object* v_val_1489_; lean_object* v_type_1490_; lean_object* v_u_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_expectedInst_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v_toPure_1476_);
v_toRing_1488_ = lean_ctor_get(v_ring_1483_, 0);
lean_inc_ref(v_toRing_1488_);
lean_dec_ref(v_ring_1483_);
v_val_1489_ = lean_ctor_get(v_fieldInst_x3f_1484_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v_fieldInst_x3f_1484_, 1);
v_type_1490_ = lean_ctor_get(v_toRing_1488_, 1);
lean_inc_ref_n(v_type_1490_, 3);
v_u_1491_ = lean_ctor_get(v_toRing_1488_, 2);
lean_inc_n(v_u_1491_, 2);
lean_dec_ref(v_toRing_1488_);
v___x_1492_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1));
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_u_1491_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
lean_inc_ref(v___x_1494_);
v___x_1495_ = l_Lean_mkConst(v___x_1492_, v___x_1494_);
v___x_1496_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3));
v___x_1497_ = l_Lean_mkConst(v___x_1496_, v___x_1494_);
v___x_1498_ = l_Lean_mkAppB(v___x_1497_, v_type_1490_, v_val_1489_);
v_expectedInst_1499_ = l_Lean_mkAppB(v___x_1495_, v_type_1490_, v___x_1498_);
v___x_1500_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5));
v___x_1501_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7));
v___x_1502_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1477_, v_inst_1478_, v_inst_1479_, v_inst_1480_, v_type_1490_, v_u_1491_, v___x_1500_, v___x_1501_, v_expectedInst_1499_);
v___x_1503_ = lean_apply_4(v_toBind_1481_, lean_box(0), lean_box(0), v___x_1502_, v___f_1482_);
return v___x_1503_;
}
}
else
{
lean_object* v_toRing_1504_; lean_object* v_type_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v___f_1482_);
lean_dec(v_toBind_1481_);
lean_dec_ref(v_inst_1480_);
lean_dec(v_inst_1477_);
lean_dec(v_toPure_1476_);
v_toRing_1504_ = lean_ctor_get(v_ring_1483_, 0);
lean_inc_ref(v_toRing_1504_);
lean_dec_ref(v_ring_1483_);
v_type_1505_ = lean_ctor_get(v_toRing_1504_, 1);
lean_inc_ref(v_type_1505_);
lean_dec_ref(v_toRing_1504_);
v___x_1506_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1507_ = l_Lean_indentExpr(v_type_1505_);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Lean_throwError___redArg(v_inst_1479_, v_inst_1478_, v___x_1508_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg(lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_){
_start:
{
lean_object* v_toApplicative_1515_; lean_object* v_toBind_1516_; lean_object* v_getCommRing_1517_; lean_object* v_modifyCommRing_1518_; lean_object* v_toPure_1519_; lean_object* v___f_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; 
v_toApplicative_1515_ = lean_ctor_get(v_inst_1512_, 0);
v_toBind_1516_ = lean_ctor_get(v_inst_1512_, 1);
lean_inc_n(v_toBind_1516_, 3);
v_getCommRing_1517_ = lean_ctor_get(v_inst_1514_, 0);
lean_inc(v_getCommRing_1517_);
v_modifyCommRing_1518_ = lean_ctor_get(v_inst_1514_, 1);
lean_inc(v_modifyCommRing_1518_);
lean_dec_ref(v_inst_1514_);
v_toPure_1519_ = lean_ctor_get(v_toApplicative_1515_, 1);
lean_inc_n(v_toPure_1519_, 2);
v___f_1520_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1520_, 0, v_toPure_1519_);
lean_closure_set(v___f_1520_, 1, v_modifyCommRing_1518_);
lean_closure_set(v___f_1520_, 2, v_toBind_1516_);
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1521_, 0, v_toPure_1519_);
lean_closure_set(v___f_1521_, 1, v_inst_1510_);
lean_closure_set(v___f_1521_, 2, v_inst_1511_);
lean_closure_set(v___f_1521_, 3, v_inst_1512_);
lean_closure_set(v___f_1521_, 4, v_inst_1513_);
lean_closure_set(v___f_1521_, 5, v_toBind_1516_);
lean_closure_set(v___f_1521_, 6, v___f_1520_);
v___x_1522_ = lean_apply_4(v_toBind_1516_, lean_box(0), lean_box(0), v_getCommRing_1517_, v___f_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn(lean_object* v_m_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Meta_Sym_Arith_getDivFn___redArg(v_inst_1524_, v_inst_1525_, v_inst_1526_, v_inst_1527_, v_inst_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0(lean_object* v_fn_1530_, lean_object* v_s_1531_){
_start:
{
lean_object* v_id_1532_; lean_object* v_type_1533_; lean_object* v_u_1534_; lean_object* v_semiringInst_1535_; lean_object* v_addFn_x3f_1536_; lean_object* v_mulFn_x3f_1537_; lean_object* v_powFn_x3f_1538_; lean_object* v_natCastFn_x3f_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1547_; 
v_id_1532_ = lean_ctor_get(v_s_1531_, 0);
v_type_1533_ = lean_ctor_get(v_s_1531_, 1);
v_u_1534_ = lean_ctor_get(v_s_1531_, 2);
v_semiringInst_1535_ = lean_ctor_get(v_s_1531_, 3);
v_addFn_x3f_1536_ = lean_ctor_get(v_s_1531_, 4);
v_mulFn_x3f_1537_ = lean_ctor_get(v_s_1531_, 5);
v_powFn_x3f_1538_ = lean_ctor_get(v_s_1531_, 6);
v_natCastFn_x3f_1539_ = lean_ctor_get(v_s_1531_, 7);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_s_1531_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_s_1531_, 8);
lean_dec(v_unused_1548_);
v___x_1541_ = v_s_1531_;
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_natCastFn_x3f_1539_);
lean_inc(v_powFn_x3f_1538_);
lean_inc(v_mulFn_x3f_1537_);
lean_inc(v_addFn_x3f_1536_);
lean_inc(v_semiringInst_1535_);
lean_inc(v_u_1534_);
lean_inc(v_type_1533_);
lean_inc(v_id_1532_);
lean_dec(v_s_1531_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_fn_1530_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 8, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_id_1532_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_type_1533_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_u_1534_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_semiringInst_1535_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_addFn_x3f_1536_);
lean_ctor_set(v_reuseFailAlloc_1546_, 5, v_mulFn_x3f_1537_);
lean_ctor_set(v_reuseFailAlloc_1546_, 6, v_powFn_x3f_1538_);
lean_ctor_set(v_reuseFailAlloc_1546_, 7, v_natCastFn_x3f_1539_);
lean_ctor_set(v_reuseFailAlloc_1546_, 8, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2(lean_object* v_toPure_1549_, lean_object* v_modifySemiring_1550_, lean_object* v_toBind_1551_, lean_object* v_fn_1552_){
_start:
{
lean_object* v___f_1553_; lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_inc_ref(v_fn_1552_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1553_, 0, v_fn_1552_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1554_, 0, v_toPure_1549_);
lean_closure_set(v___f_1554_, 1, v_fn_1552_);
v___x_1555_ = lean_apply_1(v_modifySemiring_1550_, v___f_1553_);
v___x_1556_ = lean_apply_4(v_toBind_1551_, lean_box(0), lean_box(0), v___x_1555_, v___f_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1(lean_object* v_toPure_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_toBind_1561_, lean_object* v___f_1562_, lean_object* v_sr_1563_){
_start:
{
lean_object* v_natSMulFn_x3f_1564_; 
v_natSMulFn_x3f_1564_ = lean_ctor_get(v_sr_1563_, 8);
if (lean_obj_tag(v_natSMulFn_x3f_1564_) == 1)
{
lean_object* v_val_1565_; lean_object* v___x_1566_; 
lean_inc_ref(v_natSMulFn_x3f_1564_);
lean_dec_ref(v_sr_1563_);
lean_dec(v___f_1562_);
lean_dec(v_toBind_1561_);
lean_dec_ref(v_inst_1560_);
lean_dec_ref(v_inst_1559_);
lean_dec(v_inst_1558_);
v_val_1565_ = lean_ctor_get(v_natSMulFn_x3f_1564_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v_natSMulFn_x3f_1564_, 1);
v___x_1566_ = lean_apply_2(v_toPure_1557_, lean_box(0), v_val_1565_);
return v___x_1566_;
}
else
{
lean_object* v_type_1567_; lean_object* v_u_1568_; lean_object* v_semiringInst_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec(v_toPure_1557_);
v_type_1567_ = lean_ctor_get(v_sr_1563_, 1);
lean_inc_ref_n(v_type_1567_, 2);
v_u_1568_ = lean_ctor_get(v_sr_1563_, 2);
lean_inc_n(v_u_1568_, 2);
v_semiringInst_1569_ = lean_ctor_get(v_sr_1563_, 3);
lean_inc_ref(v_semiringInst_1569_);
lean_dec_ref(v_sr_1563_);
v___x_1570_ = l_Lean_Nat_mkType;
v___x_1571_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_u_1568_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_mkConst(v___x_1571_, v___x_1573_);
v___x_1575_ = l_Lean_mkAppB(v___x_1574_, v_type_1567_, v_semiringInst_1569_);
v___x_1576_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_1558_, v_inst_1559_, v_inst_1560_, v_u_1568_, v_type_1567_, v___x_1570_, v___x_1575_);
v___x_1577_ = lean_apply_4(v_toBind_1561_, lean_box(0), lean_box(0), v___x_1576_, v___f_1562_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(lean_object* v_inst_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_inst_1581_){
_start:
{
lean_object* v_toApplicative_1582_; lean_object* v_toBind_1583_; lean_object* v_getSemiring_1584_; lean_object* v_modifySemiring_1585_; lean_object* v_toPure_1586_; lean_object* v___f_1587_; lean_object* v___f_1588_; lean_object* v___x_1589_; 
v_toApplicative_1582_ = lean_ctor_get(v_inst_1579_, 0);
v_toBind_1583_ = lean_ctor_get(v_inst_1579_, 1);
lean_inc_n(v_toBind_1583_, 3);
v_getSemiring_1584_ = lean_ctor_get(v_inst_1581_, 0);
lean_inc(v_getSemiring_1584_);
v_modifySemiring_1585_ = lean_ctor_get(v_inst_1581_, 1);
lean_inc(v_modifySemiring_1585_);
lean_dec_ref(v_inst_1581_);
v_toPure_1586_ = lean_ctor_get(v_toApplicative_1582_, 1);
lean_inc_n(v_toPure_1586_, 2);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1587_, 0, v_toPure_1586_);
lean_closure_set(v___f_1587_, 1, v_modifySemiring_1585_);
lean_closure_set(v___f_1587_, 2, v_toBind_1583_);
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1588_, 0, v_toPure_1586_);
lean_closure_set(v___f_1588_, 1, v_inst_1578_);
lean_closure_set(v___f_1588_, 2, v_inst_1579_);
lean_closure_set(v___f_1588_, 3, v_inst_1580_);
lean_closure_set(v___f_1588_, 4, v_toBind_1583_);
lean_closure_set(v___f_1588_, 5, v___f_1587_);
v___x_1589_ = lean_apply_4(v_toBind_1583_, lean_box(0), lean_box(0), v_getSemiring_1584_, v___f_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27(lean_object* v_m_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(v_inst_1591_, v_inst_1592_, v_inst_1593_, v_inst_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_1596_, lean_object* v_s_1597_){
_start:
{
lean_object* v_id_1598_; lean_object* v_type_1599_; lean_object* v_u_1600_; lean_object* v_semiringInst_1601_; lean_object* v_mulFn_x3f_1602_; lean_object* v_powFn_x3f_1603_; lean_object* v_natCastFn_x3f_1604_; lean_object* v_natSMulFn_x3f_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
v_id_1598_ = lean_ctor_get(v_s_1597_, 0);
v_type_1599_ = lean_ctor_get(v_s_1597_, 1);
v_u_1600_ = lean_ctor_get(v_s_1597_, 2);
v_semiringInst_1601_ = lean_ctor_get(v_s_1597_, 3);
v_mulFn_x3f_1602_ = lean_ctor_get(v_s_1597_, 5);
v_powFn_x3f_1603_ = lean_ctor_get(v_s_1597_, 6);
v_natCastFn_x3f_1604_ = lean_ctor_get(v_s_1597_, 7);
v_natSMulFn_x3f_1605_ = lean_ctor_get(v_s_1597_, 8);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_s_1597_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_s_1597_, 4);
lean_dec(v_unused_1614_);
v___x_1607_ = v_s_1597_;
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_natSMulFn_x3f_1605_);
lean_inc(v_natCastFn_x3f_1604_);
lean_inc(v_powFn_x3f_1603_);
lean_inc(v_mulFn_x3f_1602_);
lean_inc(v_semiringInst_1601_);
lean_inc(v_u_1600_);
lean_inc(v_type_1599_);
lean_inc(v_id_1598_);
lean_dec(v_s_1597_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_addFn_1596_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 4, v___x_1609_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_id_1598_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_type_1599_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_u_1600_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_semiringInst_1601_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1612_, 5, v_mulFn_x3f_1602_);
lean_ctor_set(v_reuseFailAlloc_1612_, 6, v_powFn_x3f_1603_);
lean_ctor_set(v_reuseFailAlloc_1612_, 7, v_natCastFn_x3f_1604_);
lean_ctor_set(v_reuseFailAlloc_1612_, 8, v_natSMulFn_x3f_1605_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_1615_, lean_object* v_modifySemiring_1616_, lean_object* v_toBind_1617_, lean_object* v_addFn_1618_){
_start:
{
lean_object* v___f_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_inc_ref(v_addFn_1618_);
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1619_, 0, v_addFn_1618_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1620_, 0, v_toPure_1615_);
lean_closure_set(v___f_1620_, 1, v_addFn_1618_);
v___x_1621_ = lean_apply_1(v_modifySemiring_1616_, v___f_1619_);
v___x_1622_ = lean_apply_4(v_toBind_1617_, lean_box(0), lean_box(0), v___x_1621_, v___f_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_toBind_1628_, lean_object* v___f_1629_, lean_object* v_sr_1630_){
_start:
{
lean_object* v_addFn_x3f_1631_; 
v_addFn_x3f_1631_ = lean_ctor_get(v_sr_1630_, 4);
if (lean_obj_tag(v_addFn_x3f_1631_) == 1)
{
lean_object* v_val_1632_; lean_object* v___x_1633_; 
lean_inc_ref(v_addFn_x3f_1631_);
lean_dec_ref(v_sr_1630_);
lean_dec(v___f_1629_);
lean_dec(v_toBind_1628_);
lean_dec_ref(v_inst_1627_);
lean_dec_ref(v_inst_1626_);
lean_dec_ref(v_inst_1625_);
lean_dec(v_inst_1624_);
v_val_1632_ = lean_ctor_get(v_addFn_x3f_1631_, 0);
lean_inc(v_val_1632_);
lean_dec_ref_known(v_addFn_x3f_1631_, 1);
v___x_1633_ = lean_apply_2(v_toPure_1623_, lean_box(0), v_val_1632_);
return v___x_1633_;
}
else
{
lean_object* v_type_1634_; lean_object* v_u_1635_; lean_object* v_semiringInst_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_expectedInst_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v_toPure_1623_);
v_type_1634_ = lean_ctor_get(v_sr_1630_, 1);
lean_inc_ref_n(v_type_1634_, 3);
v_u_1635_ = lean_ctor_get(v_sr_1630_, 2);
lean_inc_n(v_u_1635_, 2);
v_semiringInst_1636_ = lean_ctor_get(v_sr_1630_, 3);
lean_inc_ref(v_semiringInst_1636_);
lean_dec_ref(v_sr_1630_);
v___x_1637_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_u_1635_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
lean_inc_ref(v___x_1639_);
v___x_1640_ = l_Lean_mkConst(v___x_1637_, v___x_1639_);
v___x_1641_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1642_ = l_Lean_mkConst(v___x_1641_, v___x_1639_);
v___x_1643_ = l_Lean_mkAppB(v___x_1642_, v_type_1634_, v_semiringInst_1636_);
v_expectedInst_1644_ = l_Lean_mkAppB(v___x_1640_, v_type_1634_, v___x_1643_);
v___x_1645_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1646_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1647_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_type_1634_, v_u_1635_, v___x_1645_, v___x_1646_, v_expectedInst_1644_);
v___x_1648_ = lean_apply_4(v_toBind_1628_, lean_box(0), lean_box(0), v___x_1647_, v___f_1629_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_){
_start:
{
lean_object* v_toApplicative_1654_; lean_object* v_toBind_1655_; lean_object* v_getSemiring_1656_; lean_object* v_modifySemiring_1657_; lean_object* v_toPure_1658_; lean_object* v___f_1659_; lean_object* v___f_1660_; lean_object* v___x_1661_; 
v_toApplicative_1654_ = lean_ctor_get(v_inst_1651_, 0);
v_toBind_1655_ = lean_ctor_get(v_inst_1651_, 1);
lean_inc_n(v_toBind_1655_, 3);
v_getSemiring_1656_ = lean_ctor_get(v_inst_1653_, 0);
lean_inc(v_getSemiring_1656_);
v_modifySemiring_1657_ = lean_ctor_get(v_inst_1653_, 1);
lean_inc(v_modifySemiring_1657_);
lean_dec_ref(v_inst_1653_);
v_toPure_1658_ = lean_ctor_get(v_toApplicative_1654_, 1);
lean_inc_n(v_toPure_1658_, 2);
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1659_, 0, v_toPure_1658_);
lean_closure_set(v___f_1659_, 1, v_modifySemiring_1657_);
lean_closure_set(v___f_1659_, 2, v_toBind_1655_);
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1660_, 0, v_toPure_1658_);
lean_closure_set(v___f_1660_, 1, v_inst_1649_);
lean_closure_set(v___f_1660_, 2, v_inst_1650_);
lean_closure_set(v___f_1660_, 3, v_inst_1651_);
lean_closure_set(v___f_1660_, 4, v_inst_1652_);
lean_closure_set(v___f_1660_, 5, v_toBind_1655_);
lean_closure_set(v___f_1660_, 6, v___f_1659_);
v___x_1661_ = lean_apply_4(v_toBind_1655_, lean_box(0), lean_box(0), v_getSemiring_1656_, v___f_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1663_, v_inst_1664_, v_inst_1665_, v_inst_1666_, v_inst_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_1669_, lean_object* v_s_1670_){
_start:
{
lean_object* v_id_1671_; lean_object* v_type_1672_; lean_object* v_u_1673_; lean_object* v_semiringInst_1674_; lean_object* v_addFn_x3f_1675_; lean_object* v_powFn_x3f_1676_; lean_object* v_natCastFn_x3f_1677_; lean_object* v_natSMulFn_x3f_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
v_id_1671_ = lean_ctor_get(v_s_1670_, 0);
v_type_1672_ = lean_ctor_get(v_s_1670_, 1);
v_u_1673_ = lean_ctor_get(v_s_1670_, 2);
v_semiringInst_1674_ = lean_ctor_get(v_s_1670_, 3);
v_addFn_x3f_1675_ = lean_ctor_get(v_s_1670_, 4);
v_powFn_x3f_1676_ = lean_ctor_get(v_s_1670_, 6);
v_natCastFn_x3f_1677_ = lean_ctor_get(v_s_1670_, 7);
v_natSMulFn_x3f_1678_ = lean_ctor_get(v_s_1670_, 8);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_s_1670_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v_s_1670_, 5);
lean_dec(v_unused_1687_);
v___x_1680_ = v_s_1670_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_natSMulFn_x3f_1678_);
lean_inc(v_natCastFn_x3f_1677_);
lean_inc(v_powFn_x3f_1676_);
lean_inc(v_addFn_x3f_1675_);
lean_inc(v_semiringInst_1674_);
lean_inc(v_u_1673_);
lean_inc(v_type_1672_);
lean_inc(v_id_1671_);
lean_dec(v_s_1670_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_mulFn_1669_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 5, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_id_1671_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_type_1672_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_u_1673_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_semiringInst_1674_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_addFn_x3f_1675_);
lean_ctor_set(v_reuseFailAlloc_1685_, 5, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1685_, 6, v_powFn_x3f_1676_);
lean_ctor_set(v_reuseFailAlloc_1685_, 7, v_natCastFn_x3f_1677_);
lean_ctor_set(v_reuseFailAlloc_1685_, 8, v_natSMulFn_x3f_1678_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1688_, lean_object* v_modifySemiring_1689_, lean_object* v_toBind_1690_, lean_object* v_mulFn_1691_){
_start:
{
lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc_ref(v_mulFn_1691_);
v___f_1692_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1692_, 0, v_mulFn_1691_);
v___f_1693_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1693_, 0, v_toPure_1688_);
lean_closure_set(v___f_1693_, 1, v_mulFn_1691_);
v___x_1694_ = lean_apply_1(v_modifySemiring_1689_, v___f_1692_);
v___x_1695_ = lean_apply_4(v_toBind_1690_, lean_box(0), lean_box(0), v___x_1694_, v___f_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_toBind_1701_, lean_object* v___f_1702_, lean_object* v_sr_1703_){
_start:
{
lean_object* v_mulFn_x3f_1704_; 
v_mulFn_x3f_1704_ = lean_ctor_get(v_sr_1703_, 5);
if (lean_obj_tag(v_mulFn_x3f_1704_) == 1)
{
lean_object* v_val_1705_; lean_object* v___x_1706_; 
lean_inc_ref(v_mulFn_x3f_1704_);
lean_dec_ref(v_sr_1703_);
lean_dec(v___f_1702_);
lean_dec(v_toBind_1701_);
lean_dec_ref(v_inst_1700_);
lean_dec_ref(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec(v_inst_1697_);
v_val_1705_ = lean_ctor_get(v_mulFn_x3f_1704_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v_mulFn_x3f_1704_, 1);
v___x_1706_ = lean_apply_2(v_toPure_1696_, lean_box(0), v_val_1705_);
return v___x_1706_;
}
else
{
lean_object* v_type_1707_; lean_object* v_u_1708_; lean_object* v_semiringInst_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v_expectedInst_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec(v_toPure_1696_);
v_type_1707_ = lean_ctor_get(v_sr_1703_, 1);
lean_inc_ref_n(v_type_1707_, 3);
v_u_1708_ = lean_ctor_get(v_sr_1703_, 2);
lean_inc_n(v_u_1708_, 2);
v_semiringInst_1709_ = lean_ctor_get(v_sr_1703_, 3);
lean_inc_ref(v_semiringInst_1709_);
lean_dec_ref(v_sr_1703_);
v___x_1710_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_u_1708_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
lean_inc_ref(v___x_1712_);
v___x_1713_ = l_Lean_mkConst(v___x_1710_, v___x_1712_);
v___x_1714_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1715_ = l_Lean_mkConst(v___x_1714_, v___x_1712_);
v___x_1716_ = l_Lean_mkAppB(v___x_1715_, v_type_1707_, v_semiringInst_1709_);
v_expectedInst_1717_ = l_Lean_mkAppB(v___x_1713_, v_type_1707_, v___x_1716_);
v___x_1718_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1719_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1720_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1697_, v_inst_1698_, v_inst_1699_, v_inst_1700_, v_type_1707_, v_u_1708_, v___x_1718_, v___x_1719_, v_expectedInst_1717_);
v___x_1721_ = lean_apply_4(v_toBind_1701_, lean_box(0), lean_box(0), v___x_1720_, v___f_1702_);
return v___x_1721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_){
_start:
{
lean_object* v_toApplicative_1727_; lean_object* v_toBind_1728_; lean_object* v_getSemiring_1729_; lean_object* v_modifySemiring_1730_; lean_object* v_toPure_1731_; lean_object* v___f_1732_; lean_object* v___f_1733_; lean_object* v___x_1734_; 
v_toApplicative_1727_ = lean_ctor_get(v_inst_1724_, 0);
v_toBind_1728_ = lean_ctor_get(v_inst_1724_, 1);
lean_inc_n(v_toBind_1728_, 3);
v_getSemiring_1729_ = lean_ctor_get(v_inst_1726_, 0);
lean_inc(v_getSemiring_1729_);
v_modifySemiring_1730_ = lean_ctor_get(v_inst_1726_, 1);
lean_inc(v_modifySemiring_1730_);
lean_dec_ref(v_inst_1726_);
v_toPure_1731_ = lean_ctor_get(v_toApplicative_1727_, 1);
lean_inc_n(v_toPure_1731_, 2);
v___f_1732_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1732_, 0, v_toPure_1731_);
lean_closure_set(v___f_1732_, 1, v_modifySemiring_1730_);
lean_closure_set(v___f_1732_, 2, v_toBind_1728_);
v___f_1733_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1733_, 0, v_toPure_1731_);
lean_closure_set(v___f_1733_, 1, v_inst_1722_);
lean_closure_set(v___f_1733_, 2, v_inst_1723_);
lean_closure_set(v___f_1733_, 3, v_inst_1724_);
lean_closure_set(v___f_1733_, 4, v_inst_1725_);
lean_closure_set(v___f_1733_, 5, v_toBind_1728_);
lean_closure_set(v___f_1733_, 6, v___f_1732_);
v___x_1734_ = lean_apply_4(v_toBind_1728_, lean_box(0), lean_box(0), v_getSemiring_1729_, v___f_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_inst_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1736_, v_inst_1737_, v_inst_1738_, v_inst_1739_, v_inst_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1742_, lean_object* v_s_1743_){
_start:
{
lean_object* v_id_1744_; lean_object* v_type_1745_; lean_object* v_u_1746_; lean_object* v_semiringInst_1747_; lean_object* v_addFn_x3f_1748_; lean_object* v_mulFn_x3f_1749_; lean_object* v_natCastFn_x3f_1750_; lean_object* v_natSMulFn_x3f_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1759_; 
v_id_1744_ = lean_ctor_get(v_s_1743_, 0);
v_type_1745_ = lean_ctor_get(v_s_1743_, 1);
v_u_1746_ = lean_ctor_get(v_s_1743_, 2);
v_semiringInst_1747_ = lean_ctor_get(v_s_1743_, 3);
v_addFn_x3f_1748_ = lean_ctor_get(v_s_1743_, 4);
v_mulFn_x3f_1749_ = lean_ctor_get(v_s_1743_, 5);
v_natCastFn_x3f_1750_ = lean_ctor_get(v_s_1743_, 7);
v_natSMulFn_x3f_1751_ = lean_ctor_get(v_s_1743_, 8);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_s_1743_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v_s_1743_, 6);
lean_dec(v_unused_1760_);
v___x_1753_ = v_s_1743_;
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_natSMulFn_x3f_1751_);
lean_inc(v_natCastFn_x3f_1750_);
lean_inc(v_mulFn_x3f_1749_);
lean_inc(v_addFn_x3f_1748_);
lean_inc(v_semiringInst_1747_);
lean_inc(v_u_1746_);
lean_inc(v_type_1745_);
lean_inc(v_id_1744_);
lean_dec(v_s_1743_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_powFn_1742_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 6, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_id_1744_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_type_1745_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_u_1746_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_semiringInst_1747_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_addFn_x3f_1748_);
lean_ctor_set(v_reuseFailAlloc_1758_, 5, v_mulFn_x3f_1749_);
lean_ctor_set(v_reuseFailAlloc_1758_, 6, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1758_, 7, v_natCastFn_x3f_1750_);
lean_ctor_set(v_reuseFailAlloc_1758_, 8, v_natSMulFn_x3f_1751_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1761_, lean_object* v_modifySemiring_1762_, lean_object* v_toBind_1763_, lean_object* v_powFn_1764_){
_start:
{
lean_object* v___f_1765_; lean_object* v___f_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_inc_ref(v_powFn_1764_);
v___f_1765_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1765_, 0, v_powFn_1764_);
v___f_1766_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1766_, 0, v_toPure_1761_);
lean_closure_set(v___f_1766_, 1, v_powFn_1764_);
v___x_1767_ = lean_apply_1(v_modifySemiring_1762_, v___f_1765_);
v___x_1768_ = lean_apply_4(v_toBind_1763_, lean_box(0), lean_box(0), v___x_1767_, v___f_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1769_, lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_toBind_1774_, lean_object* v___f_1775_, lean_object* v_sr_1776_){
_start:
{
lean_object* v_powFn_x3f_1777_; 
v_powFn_x3f_1777_ = lean_ctor_get(v_sr_1776_, 6);
if (lean_obj_tag(v_powFn_x3f_1777_) == 1)
{
lean_object* v_val_1778_; lean_object* v___x_1779_; 
lean_inc_ref(v_powFn_x3f_1777_);
lean_dec_ref(v_sr_1776_);
lean_dec(v___f_1775_);
lean_dec(v_toBind_1774_);
lean_dec_ref(v_inst_1773_);
lean_dec_ref(v_inst_1772_);
lean_dec_ref(v_inst_1771_);
lean_dec(v_inst_1770_);
v_val_1778_ = lean_ctor_get(v_powFn_x3f_1777_, 0);
lean_inc(v_val_1778_);
lean_dec_ref_known(v_powFn_x3f_1777_, 1);
v___x_1779_ = lean_apply_2(v_toPure_1769_, lean_box(0), v_val_1778_);
return v___x_1779_;
}
else
{
lean_object* v_type_1780_; lean_object* v_u_1781_; lean_object* v_semiringInst_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec(v_toPure_1769_);
v_type_1780_ = lean_ctor_get(v_sr_1776_, 1);
lean_inc_ref(v_type_1780_);
v_u_1781_ = lean_ctor_get(v_sr_1776_, 2);
lean_inc(v_u_1781_);
v_semiringInst_1782_ = lean_ctor_get(v_sr_1776_, 3);
lean_inc_ref(v_semiringInst_1782_);
lean_dec_ref(v_sr_1776_);
v___x_1783_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1770_, v_inst_1771_, v_inst_1772_, v_inst_1773_, v_u_1781_, v_type_1780_, v_semiringInst_1782_);
v___x_1784_ = lean_apply_4(v_toBind_1774_, lean_box(0), lean_box(0), v___x_1783_, v___f_1775_);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_){
_start:
{
lean_object* v_toApplicative_1790_; lean_object* v_toBind_1791_; lean_object* v_getSemiring_1792_; lean_object* v_modifySemiring_1793_; lean_object* v_toPure_1794_; lean_object* v___f_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; 
v_toApplicative_1790_ = lean_ctor_get(v_inst_1787_, 0);
v_toBind_1791_ = lean_ctor_get(v_inst_1787_, 1);
lean_inc_n(v_toBind_1791_, 3);
v_getSemiring_1792_ = lean_ctor_get(v_inst_1789_, 0);
lean_inc(v_getSemiring_1792_);
v_modifySemiring_1793_ = lean_ctor_get(v_inst_1789_, 1);
lean_inc(v_modifySemiring_1793_);
lean_dec_ref(v_inst_1789_);
v_toPure_1794_ = lean_ctor_get(v_toApplicative_1790_, 1);
lean_inc_n(v_toPure_1794_, 2);
v___f_1795_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1795_, 0, v_toPure_1794_);
lean_closure_set(v___f_1795_, 1, v_modifySemiring_1793_);
lean_closure_set(v___f_1795_, 2, v_toBind_1791_);
v___f_1796_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1796_, 0, v_toPure_1794_);
lean_closure_set(v___f_1796_, 1, v_inst_1785_);
lean_closure_set(v___f_1796_, 2, v_inst_1786_);
lean_closure_set(v___f_1796_, 3, v_inst_1787_);
lean_closure_set(v___f_1796_, 4, v_inst_1788_);
lean_closure_set(v___f_1796_, 5, v_toBind_1791_);
lean_closure_set(v___f_1796_, 6, v___f_1795_);
v___x_1797_ = lean_apply_4(v_toBind_1791_, lean_box(0), lean_box(0), v_getSemiring_1792_, v___f_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_1798_, lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1799_, v_inst_1800_, v_inst_1801_, v_inst_1802_, v_inst_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1805_, lean_object* v_s_1806_){
_start:
{
lean_object* v_id_1807_; lean_object* v_type_1808_; lean_object* v_u_1809_; lean_object* v_semiringInst_1810_; lean_object* v_addFn_x3f_1811_; lean_object* v_mulFn_x3f_1812_; lean_object* v_powFn_x3f_1813_; lean_object* v_natSMulFn_x3f_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1822_; 
v_id_1807_ = lean_ctor_get(v_s_1806_, 0);
v_type_1808_ = lean_ctor_get(v_s_1806_, 1);
v_u_1809_ = lean_ctor_get(v_s_1806_, 2);
v_semiringInst_1810_ = lean_ctor_get(v_s_1806_, 3);
v_addFn_x3f_1811_ = lean_ctor_get(v_s_1806_, 4);
v_mulFn_x3f_1812_ = lean_ctor_get(v_s_1806_, 5);
v_powFn_x3f_1813_ = lean_ctor_get(v_s_1806_, 6);
v_natSMulFn_x3f_1814_ = lean_ctor_get(v_s_1806_, 8);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_s_1806_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v_s_1806_, 7);
lean_dec(v_unused_1823_);
v___x_1816_ = v_s_1806_;
v_isShared_1817_ = v_isSharedCheck_1822_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_natSMulFn_x3f_1814_);
lean_inc(v_powFn_x3f_1813_);
lean_inc(v_mulFn_x3f_1812_);
lean_inc(v_addFn_x3f_1811_);
lean_inc(v_semiringInst_1810_);
lean_inc(v_u_1809_);
lean_inc(v_type_1808_);
lean_inc(v_id_1807_);
lean_dec(v_s_1806_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1822_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_natCastFn_1805_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 7, v___x_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_id_1807_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_type_1808_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_u_1809_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_semiringInst_1810_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_addFn_x3f_1811_);
lean_ctor_set(v_reuseFailAlloc_1821_, 5, v_mulFn_x3f_1812_);
lean_ctor_set(v_reuseFailAlloc_1821_, 6, v_powFn_x3f_1813_);
lean_ctor_set(v_reuseFailAlloc_1821_, 7, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1821_, 8, v_natSMulFn_x3f_1814_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1824_, lean_object* v_modifySemiring_1825_, lean_object* v_toBind_1826_, lean_object* v_natCastFn_1827_){
_start:
{
lean_object* v___f_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_inc_ref(v_natCastFn_1827_);
v___f_1828_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1828_, 0, v_natCastFn_1827_);
v___f_1829_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1829_, 0, v_toPure_1824_);
lean_closure_set(v___f_1829_, 1, v_natCastFn_1827_);
v___x_1830_ = lean_apply_1(v_modifySemiring_1825_, v___f_1828_);
v___x_1831_ = lean_apply_4(v_toBind_1826_, lean_box(0), lean_box(0), v___x_1830_, v___f_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_toBind_1836_, lean_object* v___f_1837_, lean_object* v_sr_1838_){
_start:
{
lean_object* v_natCastFn_x3f_1839_; 
v_natCastFn_x3f_1839_ = lean_ctor_get(v_sr_1838_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1839_) == 1)
{
lean_object* v_val_1840_; lean_object* v___x_1841_; 
lean_inc_ref(v_natCastFn_x3f_1839_);
lean_dec_ref(v_sr_1838_);
lean_dec(v___f_1837_);
lean_dec(v_toBind_1836_);
lean_dec_ref(v_inst_1835_);
lean_dec_ref(v_inst_1834_);
lean_dec(v_inst_1833_);
v_val_1840_ = lean_ctor_get(v_natCastFn_x3f_1839_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v_natCastFn_x3f_1839_, 1);
v___x_1841_ = lean_apply_2(v_toPure_1832_, lean_box(0), v_val_1840_);
return v___x_1841_;
}
else
{
lean_object* v_type_1842_; lean_object* v_u_1843_; lean_object* v_semiringInst_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_toPure_1832_);
v_type_1842_ = lean_ctor_get(v_sr_1838_, 1);
lean_inc_ref(v_type_1842_);
v_u_1843_ = lean_ctor_get(v_sr_1838_, 2);
lean_inc(v_u_1843_);
v_semiringInst_1844_ = lean_ctor_get(v_sr_1838_, 3);
lean_inc_ref(v_semiringInst_1844_);
lean_dec_ref(v_sr_1838_);
v___x_1845_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1833_, v_inst_1834_, v_inst_1835_, v_u_1843_, v_type_1842_, v_semiringInst_1844_);
v___x_1846_ = lean_apply_4(v_toBind_1836_, lean_box(0), lean_box(0), v___x_1845_, v___f_1837_);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_){
_start:
{
lean_object* v_toApplicative_1851_; lean_object* v_toBind_1852_; lean_object* v_getSemiring_1853_; lean_object* v_modifySemiring_1854_; lean_object* v_toPure_1855_; lean_object* v___f_1856_; lean_object* v___f_1857_; lean_object* v___x_1858_; 
v_toApplicative_1851_ = lean_ctor_get(v_inst_1848_, 0);
v_toBind_1852_ = lean_ctor_get(v_inst_1848_, 1);
lean_inc_n(v_toBind_1852_, 3);
v_getSemiring_1853_ = lean_ctor_get(v_inst_1850_, 0);
lean_inc(v_getSemiring_1853_);
v_modifySemiring_1854_ = lean_ctor_get(v_inst_1850_, 1);
lean_inc(v_modifySemiring_1854_);
lean_dec_ref(v_inst_1850_);
v_toPure_1855_ = lean_ctor_get(v_toApplicative_1851_, 1);
lean_inc_n(v_toPure_1855_, 2);
v___f_1856_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1856_, 0, v_toPure_1855_);
lean_closure_set(v___f_1856_, 1, v_modifySemiring_1854_);
lean_closure_set(v___f_1856_, 2, v_toBind_1852_);
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1857_, 0, v_toPure_1855_);
lean_closure_set(v___f_1857_, 1, v_inst_1847_);
lean_closure_set(v___f_1857_, 2, v_inst_1848_);
lean_closure_set(v___f_1857_, 3, v_inst_1849_);
lean_closure_set(v___f_1857_, 4, v_toBind_1852_);
lean_closure_set(v___f_1857_, 5, v___f_1856_);
v___x_1858_ = lean_apply_4(v_toBind_1852_, lean_box(0), lean_box(0), v_getSemiring_1853_, v___f_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_, lean_object* v_inst_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1860_, v_inst_1861_, v_inst_1862_, v_inst_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0(lean_object* v_toQFn_1865_, lean_object* v_s_1866_){
_start:
{
lean_object* v_toSemiring_1867_; lean_object* v_ringId_1868_; lean_object* v_commSemiringInst_1869_; lean_object* v_addRightCancelInst_x3f_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1878_; 
v_toSemiring_1867_ = lean_ctor_get(v_s_1866_, 0);
v_ringId_1868_ = lean_ctor_get(v_s_1866_, 1);
v_commSemiringInst_1869_ = lean_ctor_get(v_s_1866_, 2);
v_addRightCancelInst_x3f_1870_ = lean_ctor_get(v_s_1866_, 3);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_s_1866_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v_s_1866_, 4);
lean_dec(v_unused_1879_);
v___x_1872_ = v_s_1866_;
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_1870_);
lean_inc(v_commSemiringInst_1869_);
lean_inc(v_ringId_1868_);
lean_inc(v_toSemiring_1867_);
lean_dec(v_s_1866_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_toQFn_1865_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_toSemiring_1867_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_ringId_1868_);
lean_ctor_set(v_reuseFailAlloc_1877_, 2, v_commSemiringInst_1869_);
lean_ctor_set(v_reuseFailAlloc_1877_, 3, v_addRightCancelInst_x3f_1870_);
lean_ctor_set(v_reuseFailAlloc_1877_, 4, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1(lean_object* v_toPure_1880_, lean_object* v_toQFn_1881_, lean_object* v_____r_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_apply_2(v_toPure_1880_, lean_box(0), v_toQFn_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2(lean_object* v_toPure_1884_, lean_object* v_modifyCommSemiring_1885_, lean_object* v_toBind_1886_, lean_object* v_toQFn_1887_){
_start:
{
lean_object* v___f_1888_; lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_inc_ref(v_toQFn_1887_);
v___f_1888_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1888_, 0, v_toQFn_1887_);
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1889_, 0, v_toPure_1884_);
lean_closure_set(v___f_1889_, 1, v_toQFn_1887_);
v___x_1890_ = lean_apply_1(v_modifyCommSemiring_1885_, v___f_1888_);
v___x_1891_ = lean_apply_4(v_toBind_1886_, lean_box(0), lean_box(0), v___x_1890_, v___f_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3(lean_object* v_toPure_1900_, lean_object* v_inst_1901_, lean_object* v_toBind_1902_, lean_object* v___f_1903_, lean_object* v_s_1904_){
_start:
{
lean_object* v_toQFn_x3f_1905_; 
v_toQFn_x3f_1905_ = lean_ctor_get(v_s_1904_, 4);
if (lean_obj_tag(v_toQFn_x3f_1905_) == 1)
{
lean_object* v_val_1906_; lean_object* v___x_1907_; 
lean_inc_ref(v_toQFn_x3f_1905_);
lean_dec_ref(v_s_1904_);
lean_dec(v___f_1903_);
lean_dec(v_toBind_1902_);
lean_dec_ref(v_inst_1901_);
v_val_1906_ = lean_ctor_get(v_toQFn_x3f_1905_, 0);
lean_inc(v_val_1906_);
lean_dec_ref_known(v_toQFn_x3f_1905_, 1);
v___x_1907_ = lean_apply_2(v_toPure_1900_, lean_box(0), v_val_1906_);
return v___x_1907_;
}
else
{
lean_object* v_toSemiring_1908_; lean_object* v_canonExpr_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_toPure_1900_);
v_toSemiring_1908_ = lean_ctor_get(v_s_1904_, 0);
lean_inc_ref(v_toSemiring_1908_);
lean_dec_ref(v_s_1904_);
v_canonExpr_1909_ = lean_ctor_get(v_inst_1901_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_inst_1901_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v_inst_1901_, 1);
lean_dec(v_unused_1926_);
v___x_1911_ = v_inst_1901_;
v_isShared_1912_ = v_isSharedCheck_1925_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_canonExpr_1909_);
lean_dec(v_inst_1901_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1925_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_type_1913_; lean_object* v_u_1914_; lean_object* v_semiringInst_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v_type_1913_ = lean_ctor_get(v_toSemiring_1908_, 1);
lean_inc_ref(v_type_1913_);
v_u_1914_ = lean_ctor_get(v_toSemiring_1908_, 2);
lean_inc(v_u_1914_);
v_semiringInst_1915_ = lean_ctor_get(v_toSemiring_1908_, 3);
lean_inc_ref(v_semiringInst_1915_);
lean_dec_ref(v_toSemiring_1908_);
v___x_1916_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2));
v___x_1917_ = lean_box(0);
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 1);
lean_ctor_set(v___x_1911_, 1, v___x_1917_);
lean_ctor_set(v___x_1911_, 0, v_u_1914_);
v___x_1919_ = v___x_1911_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_u_1914_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1920_ = l_Lean_mkConst(v___x_1916_, v___x_1919_);
v___x_1921_ = l_Lean_mkAppB(v___x_1920_, v_type_1913_, v_semiringInst_1915_);
v___x_1922_ = lean_apply_1(v_canonExpr_1909_, v___x_1921_);
v___x_1923_ = lean_apply_4(v_toBind_1902_, lean_box(0), lean_box(0), v___x_1922_, v___f_1903_);
return v___x_1923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg(lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_inst_1929_){
_start:
{
lean_object* v_toApplicative_1930_; lean_object* v_toBind_1931_; lean_object* v_getCommSemiring_1932_; lean_object* v_modifyCommSemiring_1933_; lean_object* v_toPure_1934_; lean_object* v___f_1935_; lean_object* v___f_1936_; lean_object* v___x_1937_; 
v_toApplicative_1930_ = lean_ctor_get(v_inst_1927_, 0);
lean_inc_ref(v_toApplicative_1930_);
v_toBind_1931_ = lean_ctor_get(v_inst_1927_, 1);
lean_inc_n(v_toBind_1931_, 3);
lean_dec_ref(v_inst_1927_);
v_getCommSemiring_1932_ = lean_ctor_get(v_inst_1929_, 0);
lean_inc(v_getCommSemiring_1932_);
v_modifyCommSemiring_1933_ = lean_ctor_get(v_inst_1929_, 1);
lean_inc(v_modifyCommSemiring_1933_);
lean_dec_ref(v_inst_1929_);
v_toPure_1934_ = lean_ctor_get(v_toApplicative_1930_, 1);
lean_inc_n(v_toPure_1934_, 2);
lean_dec_ref(v_toApplicative_1930_);
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1935_, 0, v_toPure_1934_);
lean_closure_set(v___f_1935_, 1, v_modifyCommSemiring_1933_);
lean_closure_set(v___f_1935_, 2, v_toBind_1931_);
v___f_1936_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1936_, 0, v_toPure_1934_);
lean_closure_set(v___f_1936_, 1, v_inst_1928_);
lean_closure_set(v___f_1936_, 2, v_toBind_1931_);
lean_closure_set(v___f_1936_, 3, v___f_1935_);
v___x_1937_ = lean_apply_4(v_toBind_1931_, lean_box(0), lean_box(0), v_getCommSemiring_1932_, v___f_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn(lean_object* v_m_1938_, lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_Meta_Sym_Arith_getToQFn___redArg(v_inst_1939_, v_inst_1940_, v_inst_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0(lean_object* v_addRightCancelInst_x3f_1943_, lean_object* v_s_1944_){
_start:
{
lean_object* v_toSemiring_1945_; lean_object* v_ringId_1946_; lean_object* v_commSemiringInst_1947_; lean_object* v_toQFn_x3f_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
v_toSemiring_1945_ = lean_ctor_get(v_s_1944_, 0);
v_ringId_1946_ = lean_ctor_get(v_s_1944_, 1);
v_commSemiringInst_1947_ = lean_ctor_get(v_s_1944_, 2);
v_toQFn_x3f_1948_ = lean_ctor_get(v_s_1944_, 4);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_s_1944_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v_s_1944_, 3);
lean_dec(v_unused_1957_);
v___x_1950_ = v_s_1944_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_toQFn_x3f_1948_);
lean_inc(v_commSemiringInst_1947_);
lean_inc(v_ringId_1946_);
lean_inc(v_toSemiring_1945_);
lean_dec(v_s_1944_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v_addRightCancelInst_x3f_1943_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 3, v___x_1952_);
v___x_1954_ = v___x_1950_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_toSemiring_1945_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_ringId_1946_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_commSemiringInst_1947_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_toQFn_x3f_1948_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1(lean_object* v_toPure_1958_, lean_object* v_addRightCancelInst_x3f_1959_, lean_object* v_____r_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_apply_2(v_toPure_1958_, lean_box(0), v_addRightCancelInst_x3f_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2(lean_object* v_toPure_1962_, lean_object* v_modifyCommSemiring_1963_, lean_object* v_toBind_1964_, lean_object* v_addRightCancelInst_x3f_1965_){
_start:
{
lean_object* v___f_1966_; lean_object* v___f_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_inc(v_addRightCancelInst_x3f_1965_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1966_, 0, v_addRightCancelInst_x3f_1965_);
v___f_1967_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1967_, 0, v_toPure_1962_);
lean_closure_set(v___f_1967_, 1, v_addRightCancelInst_x3f_1965_);
v___x_1968_ = lean_apply_1(v_modifyCommSemiring_1963_, v___f_1966_);
v___x_1969_ = lean_apply_4(v_toBind_1964_, lean_box(0), lean_box(0), v___x_1968_, v___f_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3(lean_object* v___f_1970_, lean_object* v_addRightCancelInst_x3f_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_apply_1(v___f_1970_, v_addRightCancelInst_x3f_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5(lean_object* v___x_1978_, lean_object* v_type_1979_, lean_object* v_synthInstance_x3f_1980_, lean_object* v_toBind_1981_, lean_object* v___f_1982_, lean_object* v_toPure_1983_, lean_object* v___f_1984_, lean_object* v_____x_1985_){
_start:
{
if (lean_obj_tag(v_____x_1985_) == 1)
{
lean_object* v_val_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v___f_1984_);
lean_dec(v_toPure_1983_);
v_val_1986_ = lean_ctor_get(v_____x_1985_, 0);
lean_inc(v_val_1986_);
lean_dec_ref_known(v_____x_1985_, 1);
v___x_1987_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1));
v___x_1988_ = l_Lean_mkConst(v___x_1987_, v___x_1978_);
v___x_1989_ = l_Lean_mkAppB(v___x_1988_, v_type_1979_, v_val_1986_);
v___x_1990_ = lean_apply_1(v_synthInstance_x3f_1980_, v___x_1989_);
v___x_1991_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v___x_1990_, v___f_1982_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec(v_____x_1985_);
lean_dec(v___f_1982_);
lean_dec(v_synthInstance_x3f_1980_);
lean_dec_ref(v_type_1979_);
lean_dec(v___x_1978_);
v___x_1992_ = lean_box(0);
v___x_1993_ = lean_apply_2(v_toPure_1983_, lean_box(0), v___x_1992_);
v___x_1994_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v___x_1993_, v___f_1984_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4(lean_object* v_toPure_1998_, lean_object* v_inst_1999_, lean_object* v_toBind_2000_, lean_object* v___f_2001_, lean_object* v___f_2002_, lean_object* v_s_2003_){
_start:
{
lean_object* v_addRightCancelInst_x3f_2004_; 
v_addRightCancelInst_x3f_2004_ = lean_ctor_get(v_s_2003_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_2004_) == 1)
{
lean_object* v_val_2005_; lean_object* v___x_2006_; 
lean_inc_ref(v_addRightCancelInst_x3f_2004_);
lean_dec_ref(v_s_2003_);
lean_dec(v___f_2002_);
lean_dec(v___f_2001_);
lean_dec(v_toBind_2000_);
lean_dec_ref(v_inst_1999_);
v_val_2005_ = lean_ctor_get(v_addRightCancelInst_x3f_2004_, 0);
lean_inc(v_val_2005_);
lean_dec_ref_known(v_addRightCancelInst_x3f_2004_, 1);
v___x_2006_ = lean_apply_2(v_toPure_1998_, lean_box(0), v_val_2005_);
return v___x_2006_;
}
else
{
lean_object* v_toSemiring_2007_; lean_object* v_synthInstance_x3f_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2024_; 
v_toSemiring_2007_ = lean_ctor_get(v_s_2003_, 0);
lean_inc_ref(v_toSemiring_2007_);
lean_dec_ref(v_s_2003_);
v_synthInstance_x3f_2008_ = lean_ctor_get(v_inst_1999_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_inst_1999_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_inst_1999_, 0);
lean_dec(v_unused_2025_);
v___x_2010_ = v_inst_1999_;
v_isShared_2011_ = v_isSharedCheck_2024_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_synthInstance_x3f_2008_);
lean_dec(v_inst_1999_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2024_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_type_2012_; lean_object* v_u_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v_type_2012_ = lean_ctor_get(v_toSemiring_2007_, 1);
lean_inc_ref(v_type_2012_);
v_u_2013_ = lean_ctor_get(v_toSemiring_2007_, 2);
lean_inc(v_u_2013_);
lean_dec_ref(v_toSemiring_2007_);
v___x_2014_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1));
v___x_2015_ = lean_box(0);
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 1);
lean_ctor_set(v___x_2010_, 1, v___x_2015_);
lean_ctor_set(v___x_2010_, 0, v_u_2013_);
v___x_2017_ = v___x_2010_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_u_2013_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_inc(v_toBind_2000_);
lean_inc(v_synthInstance_x3f_2008_);
lean_inc_ref(v_type_2012_);
lean_inc_ref(v___x_2017_);
v___f_2018_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_2018_, 0, v___x_2017_);
lean_closure_set(v___f_2018_, 1, v_type_2012_);
lean_closure_set(v___f_2018_, 2, v_synthInstance_x3f_2008_);
lean_closure_set(v___f_2018_, 3, v_toBind_2000_);
lean_closure_set(v___f_2018_, 4, v___f_2001_);
lean_closure_set(v___f_2018_, 5, v_toPure_1998_);
lean_closure_set(v___f_2018_, 6, v___f_2002_);
v___x_2019_ = l_Lean_mkConst(v___x_2014_, v___x_2017_);
v___x_2020_ = l_Lean_Expr_app___override(v___x_2019_, v_type_2012_);
v___x_2021_ = lean_apply_1(v_synthInstance_x3f_2008_, v___x_2020_);
v___x_2022_ = lean_apply_4(v_toBind_2000_, lean_box(0), lean_box(0), v___x_2021_, v___f_2018_);
return v___x_2022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_){
_start:
{
lean_object* v_toApplicative_2029_; lean_object* v_toBind_2030_; lean_object* v_getCommSemiring_2031_; lean_object* v_modifyCommSemiring_2032_; lean_object* v_toPure_2033_; lean_object* v___f_2034_; lean_object* v___f_2035_; lean_object* v___f_2036_; lean_object* v___x_2037_; 
v_toApplicative_2029_ = lean_ctor_get(v_inst_2026_, 0);
lean_inc_ref(v_toApplicative_2029_);
v_toBind_2030_ = lean_ctor_get(v_inst_2026_, 1);
lean_inc_n(v_toBind_2030_, 3);
lean_dec_ref(v_inst_2026_);
v_getCommSemiring_2031_ = lean_ctor_get(v_inst_2028_, 0);
lean_inc(v_getCommSemiring_2031_);
v_modifyCommSemiring_2032_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc(v_modifyCommSemiring_2032_);
lean_dec_ref(v_inst_2028_);
v_toPure_2033_ = lean_ctor_get(v_toApplicative_2029_, 1);
lean_inc_n(v_toPure_2033_, 2);
lean_dec_ref(v_toApplicative_2029_);
v___f_2034_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2034_, 0, v_toPure_2033_);
lean_closure_set(v___f_2034_, 1, v_modifyCommSemiring_2032_);
lean_closure_set(v___f_2034_, 2, v_toBind_2030_);
v___f_2035_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2035_, 0, v___f_2034_);
lean_inc_ref(v___f_2035_);
v___f_2036_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4), 6, 5);
lean_closure_set(v___f_2036_, 0, v_toPure_2033_);
lean_closure_set(v___f_2036_, 1, v_inst_2027_);
lean_closure_set(v___f_2036_, 2, v_toBind_2030_);
lean_closure_set(v___f_2036_, 3, v___f_2035_);
lean_closure_set(v___f_2036_, 4, v___f_2035_);
v___x_2037_ = lean_apply_4(v_toBind_2030_, lean_box(0), lean_box(0), v_getCommSemiring_2031_, v___f_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f(lean_object* v_m_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(v_inst_2039_, v_inst_2040_, v_inst_2041_);
return v___x_2042_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
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
res = runtime_initialize_Init_Grind_Ring(builtin);
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
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
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
res = initialize_Init_Grind_Ring(builtin);
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
