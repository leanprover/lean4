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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6));
v___x_61_ = l_Lean_stringToMessageData(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object* v_declName_62_, lean_object* v_inst_63_, lean_object* v_inst_x27_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___y_71_; lean_object* v___x_104_; uint8_t v_transparency_105_; uint8_t v___x_106_; uint8_t v___x_107_; 
v___x_104_ = l_Lean_Meta_Context_config(v_a_65_);
v_transparency_105_ = lean_ctor_get_uint8(v___x_104_, 9);
lean_dec_ref(v___x_104_);
v___x_106_ = 3;
v___x_107_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v_keyedConfig_108_; uint8_t v_trackZetaDelta_109_; lean_object* v_zetaDeltaSet_110_; lean_object* v_lctx_111_; lean_object* v_localInstances_112_; lean_object* v_defEqCtx_x3f_113_; lean_object* v_synthPendingDepth_114_; lean_object* v_customCanUnfoldPredicate_x3f_115_; uint8_t v_univApprox_116_; uint8_t v_inTypeClassResolution_117_; uint8_t v_cacheInferType_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_keyedConfig_108_ = lean_ctor_get(v_a_65_, 0);
v_trackZetaDelta_109_ = lean_ctor_get_uint8(v_a_65_, sizeof(void*)*7);
v_zetaDeltaSet_110_ = lean_ctor_get(v_a_65_, 1);
v_lctx_111_ = lean_ctor_get(v_a_65_, 2);
v_localInstances_112_ = lean_ctor_get(v_a_65_, 3);
v_defEqCtx_x3f_113_ = lean_ctor_get(v_a_65_, 4);
v_synthPendingDepth_114_ = lean_ctor_get(v_a_65_, 5);
v_customCanUnfoldPredicate_x3f_115_ = lean_ctor_get(v_a_65_, 6);
v_univApprox_116_ = lean_ctor_get_uint8(v_a_65_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_117_ = lean_ctor_get_uint8(v_a_65_, sizeof(void*)*7 + 2);
v_cacheInferType_118_ = lean_ctor_get_uint8(v_a_65_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_108_);
v___x_119_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_106_, v_keyedConfig_108_);
lean_inc(v_customCanUnfoldPredicate_x3f_115_);
lean_inc(v_synthPendingDepth_114_);
lean_inc(v_defEqCtx_x3f_113_);
lean_inc_ref(v_localInstances_112_);
lean_inc_ref(v_lctx_111_);
lean_inc(v_zetaDeltaSet_110_);
v___x_120_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_zetaDeltaSet_110_);
lean_ctor_set(v___x_120_, 2, v_lctx_111_);
lean_ctor_set(v___x_120_, 3, v_localInstances_112_);
lean_ctor_set(v___x_120_, 4, v_defEqCtx_x3f_113_);
lean_ctor_set(v___x_120_, 5, v_synthPendingDepth_114_);
lean_ctor_set(v___x_120_, 6, v_customCanUnfoldPredicate_x3f_115_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*7, v_trackZetaDelta_109_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*7 + 1, v_univApprox_116_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*7 + 2, v_inTypeClassResolution_117_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*7 + 3, v_cacheInferType_118_);
lean_inc_ref(v_inst_x27_64_);
lean_inc_ref(v_inst_63_);
v___x_121_ = l_Lean_Meta_isExprDefEq(v_inst_63_, v_inst_x27_64_, v___x_120_, v_a_66_, v_a_67_, v_a_68_);
lean_dec_ref_known(v___x_120_, 7);
v___y_71_ = v___x_121_;
goto v___jp_70_;
}
else
{
lean_object* v___x_122_; 
lean_inc_ref(v_inst_x27_64_);
lean_inc_ref(v_inst_63_);
v___x_122_ = l_Lean_Meta_isExprDefEq(v_inst_63_, v_inst_x27_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
v___y_71_ = v___x_122_;
goto v___jp_70_;
}
v___jp_70_:
{
if (lean_obj_tag(v___y_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_95_; 
v_a_72_ = lean_ctor_get(v___y_71_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___y_71_);
if (v_isSharedCheck_95_ == 0)
{
v___x_74_ = v___y_71_;
v_isShared_75_ = v_isSharedCheck_95_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___y_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_95_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint8_t v___x_76_; 
v___x_76_ = lean_unbox(v_a_72_);
lean_dec(v_a_72_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
lean_del_object(v___x_74_);
v___x_77_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1);
v___x_78_ = l_Lean_MessageData_ofName(v_declName_62_);
v___x_79_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3);
v___x_81_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = l_Lean_indentExpr(v_inst_63_);
v___x_83_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = l_Lean_indentExpr(v_inst_x27_64_);
v___x_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7);
v___x_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_89_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_93_; 
lean_dec_ref(v_inst_x27_64_);
lean_dec_ref(v_inst_63_);
lean_dec(v_declName_62_);
v___x_91_ = lean_box(0);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_91_);
v___x_93_ = v___x_74_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_inst_x27_64_);
lean_dec_ref(v_inst_63_);
lean_dec(v_declName_62_);
v_a_96_ = lean_ctor_get(v___y_71_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___y_71_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___y_71_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___y_71_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object* v_declName_123_, lean_object* v_inst_124_, lean_object* v_inst_x27_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_123_, v_inst_124_, v_inst_x27_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object* v_00_u03b1_132_, lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(lean_object* v_00_u03b1_140_, lean_object* v_msg_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(v_00_u03b1_140_, v_msg_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object* v_inst_148_, lean_object* v_declName_149_, lean_object* v___x_150_, lean_object* v_type_151_, lean_object* v_inst_152_, lean_object* v_____r_153_){
_start:
{
lean_object* v_canonExpr_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_canonExpr_154_ = lean_ctor_get(v_inst_148_, 0);
lean_inc(v_canonExpr_154_);
lean_dec_ref(v_inst_148_);
v___x_155_ = l_Lean_mkConst(v_declName_149_, v___x_150_);
v___x_156_ = l_Lean_mkAppB(v___x_155_, v_type_151_, v_inst_152_);
v___x_157_ = lean_apply_1(v_canonExpr_154_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object* v_inst_158_, lean_object* v_declName_159_, lean_object* v___x_160_, lean_object* v_type_161_, lean_object* v_expectedInst_162_, lean_object* v_inst_163_, lean_object* v_toBind_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_inc_ref(v_inst_165_);
lean_inc(v_declName_159_);
v___f_166_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_166_, 0, v_inst_158_);
lean_closure_set(v___f_166_, 1, v_declName_159_);
lean_closure_set(v___f_166_, 2, v___x_160_);
lean_closure_set(v___f_166_, 3, v_type_161_);
lean_closure_set(v___f_166_, 4, v_inst_165_);
v___x_167_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_167_, 0, v_declName_159_);
lean_closure_set(v___x_167_, 1, v_inst_165_);
lean_closure_set(v___x_167_, 2, v_expectedInst_162_);
v___x_168_ = lean_apply_2(v_inst_163_, lean_box(0), v___x_167_);
v___x_169_ = lean_apply_4(v_toBind_164_, lean_box(0), lean_box(0), v___x_168_, v___f_166_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_type_174_, lean_object* v_u_175_, lean_object* v_instDeclName_176_, lean_object* v_declName_177_, lean_object* v_expectedInst_178_){
_start:
{
lean_object* v_toBind_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_toBind_179_ = lean_ctor_get(v_inst_172_, 1);
lean_inc_n(v_toBind_179_, 2);
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v_u_175_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
lean_inc_ref(v_type_174_);
lean_inc_ref(v___x_181_);
lean_inc_ref(v_inst_173_);
v___f_182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_182_, 0, v_inst_173_);
lean_closure_set(v___f_182_, 1, v_declName_177_);
lean_closure_set(v___f_182_, 2, v___x_181_);
lean_closure_set(v___f_182_, 3, v_type_174_);
lean_closure_set(v___f_182_, 4, v_expectedInst_178_);
lean_closure_set(v___f_182_, 5, v_inst_170_);
lean_closure_set(v___f_182_, 6, v_toBind_179_);
v___x_183_ = l_Lean_mkConst(v_instDeclName_176_, v___x_181_);
v___x_184_ = l_Lean_Expr_app___override(v___x_183_, v_type_174_);
v___x_185_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_172_, v_inst_171_, v_inst_173_, v___x_184_);
v___x_186_ = lean_apply_4(v_toBind_179_, lean_box(0), lean_box(0), v___x_185_, v___f_182_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object* v_m_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_type_192_, lean_object* v_u_193_, lean_object* v_instDeclName_194_, lean_object* v_declName_195_, lean_object* v_expectedInst_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_188_, v_inst_189_, v_inst_190_, v_inst_191_, v_type_192_, v_u_193_, v_instDeclName_194_, v_declName_195_, v_expectedInst_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_198_, lean_object* v_declName_199_, lean_object* v___x_200_, lean_object* v_type_201_, lean_object* v_inst_202_, lean_object* v_____r_203_){
_start:
{
lean_object* v_canonExpr_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_canonExpr_204_ = lean_ctor_get(v_inst_198_, 0);
lean_inc(v_canonExpr_204_);
lean_dec_ref(v_inst_198_);
v___x_205_ = l_Lean_mkConst(v_declName_199_, v___x_200_);
lean_inc_ref_n(v_type_201_, 2);
v___x_206_ = l_Lean_mkApp4(v___x_205_, v_type_201_, v_type_201_, v_type_201_, v_inst_202_);
v___x_207_ = lean_apply_1(v_canonExpr_204_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_208_, lean_object* v_declName_209_, lean_object* v___x_210_, lean_object* v_type_211_, lean_object* v_expectedInst_212_, lean_object* v_inst_213_, lean_object* v_toBind_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_inc_ref(v_inst_215_);
lean_inc(v_declName_209_);
v___f_216_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_216_, 0, v_inst_208_);
lean_closure_set(v___f_216_, 1, v_declName_209_);
lean_closure_set(v___f_216_, 2, v___x_210_);
lean_closure_set(v___f_216_, 3, v_type_211_);
lean_closure_set(v___f_216_, 4, v_inst_215_);
v___x_217_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_217_, 0, v_declName_209_);
lean_closure_set(v___x_217_, 1, v_inst_215_);
lean_closure_set(v___x_217_, 2, v_expectedInst_212_);
v___x_218_ = lean_apply_2(v_inst_213_, lean_box(0), v___x_217_);
v___x_219_ = lean_apply_4(v_toBind_214_, lean_box(0), lean_box(0), v___x_218_, v___f_216_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_type_224_, lean_object* v_u_225_, lean_object* v_instDeclName_226_, lean_object* v_declName_227_, lean_object* v_expectedInst_228_){
_start:
{
lean_object* v_toBind_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_toBind_229_ = lean_ctor_get(v_inst_222_, 1);
lean_inc_n(v_toBind_229_, 2);
v___x_230_ = lean_box(0);
lean_inc_n(v_u_225_, 2);
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v_u_225_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v_u_225_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v_u_225_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
lean_inc_ref_n(v_type_224_, 3);
lean_inc_ref(v___x_233_);
lean_inc_ref(v_inst_223_);
v___f_234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_234_, 0, v_inst_223_);
lean_closure_set(v___f_234_, 1, v_declName_227_);
lean_closure_set(v___f_234_, 2, v___x_233_);
lean_closure_set(v___f_234_, 3, v_type_224_);
lean_closure_set(v___f_234_, 4, v_expectedInst_228_);
lean_closure_set(v___f_234_, 5, v_inst_220_);
lean_closure_set(v___f_234_, 6, v_toBind_229_);
v___x_235_ = l_Lean_mkConst(v_instDeclName_226_, v___x_233_);
v___x_236_ = l_Lean_mkApp3(v___x_235_, v_type_224_, v_type_224_, v_type_224_);
v___x_237_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_222_, v_inst_221_, v_inst_223_, v___x_236_);
v___x_238_ = lean_apply_4(v_toBind_229_, lean_box(0), lean_box(0), v___x_237_, v___f_234_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object* v_m_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_type_244_, lean_object* v_u_245_, lean_object* v_instDeclName_246_, lean_object* v_declName_247_, lean_object* v_expectedInst_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_240_, v_inst_241_, v_inst_242_, v_inst_243_, v_type_244_, v_u_245_, v_instDeclName_246_, v_declName_247_, v_expectedInst_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object* v_inst_250_, lean_object* v___x_251_, lean_object* v___x_252_, lean_object* v_type_253_, lean_object* v___x_254_, lean_object* v_inst_255_, lean_object* v_____r_256_){
_start:
{
lean_object* v_canonExpr_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_canonExpr_257_ = lean_ctor_get(v_inst_250_, 0);
lean_inc(v_canonExpr_257_);
lean_dec_ref(v_inst_250_);
v___x_258_ = l_Lean_mkConst(v___x_251_, v___x_252_);
lean_inc_ref(v_type_253_);
v___x_259_ = l_Lean_mkApp4(v___x_258_, v_type_253_, v___x_254_, v_type_253_, v_inst_255_);
v___x_260_ = lean_apply_1(v_canonExpr_257_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object* v___x_271_, lean_object* v_type_272_, lean_object* v_semiringInst_273_, lean_object* v___x_274_, lean_object* v_inst_275_, lean_object* v___x_276_, lean_object* v___x_277_, lean_object* v_inst_278_, lean_object* v_toBind_279_, lean_object* v_inst_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_inst_x27_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4));
v___x_282_ = l_Lean_mkConst(v___x_281_, v___x_271_);
lean_inc_ref(v_type_272_);
v_inst_x27_283_ = l_Lean_mkAppB(v___x_282_, v_type_272_, v_semiringInst_273_);
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5));
v___x_285_ = l_Lean_Name_mkStr2(v___x_274_, v___x_284_);
lean_inc_ref(v_inst_280_);
lean_inc(v___x_285_);
v___f_286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_286_, 0, v_inst_275_);
lean_closure_set(v___f_286_, 1, v___x_285_);
lean_closure_set(v___f_286_, 2, v___x_276_);
lean_closure_set(v___f_286_, 3, v_type_272_);
lean_closure_set(v___f_286_, 4, v___x_277_);
lean_closure_set(v___f_286_, 5, v_inst_280_);
v___x_287_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_287_, 0, v___x_285_);
lean_closure_set(v___x_287_, 1, v_inst_280_);
lean_closure_set(v___x_287_, 2, v_inst_x27_283_);
v___x_288_ = lean_apply_2(v_inst_278_, lean_box(0), v___x_287_);
v___x_289_ = lean_apply_4(v_toBind_279_, lean_box(0), lean_box(0), v___x_288_, v___f_286_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = l_Lean_Level_ofNat(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_u_299_, lean_object* v_type_300_, lean_object* v_semiringInst_301_){
_start:
{
lean_object* v_toBind_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_toBind_302_ = lean_ctor_get(v_inst_297_, 1);
lean_inc_n(v_toBind_302_, 2);
v___x_303_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0));
v___x_304_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1));
v___x_305_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_306_ = lean_box(0);
lean_inc(v_u_299_);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v_u_299_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
lean_inc_ref(v___x_307_);
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_305_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v_u_299_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_inc_ref(v___x_309_);
v___x_310_ = l_Lean_mkConst(v___x_304_, v___x_309_);
v___x_311_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_298_);
lean_inc_ref_n(v_type_300_, 2);
v___f_312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_312_, 0, v___x_307_);
lean_closure_set(v___f_312_, 1, v_type_300_);
lean_closure_set(v___f_312_, 2, v_semiringInst_301_);
lean_closure_set(v___f_312_, 3, v___x_303_);
lean_closure_set(v___f_312_, 4, v_inst_298_);
lean_closure_set(v___f_312_, 5, v___x_309_);
lean_closure_set(v___f_312_, 6, v___x_311_);
lean_closure_set(v___f_312_, 7, v_inst_295_);
lean_closure_set(v___f_312_, 8, v_toBind_302_);
v___x_313_ = l_Lean_mkApp3(v___x_310_, v_type_300_, v___x_311_, v_type_300_);
v___x_314_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_297_, v_inst_296_, v_inst_298_, v___x_313_);
v___x_315_ = lean_apply_4(v_toBind_302_, lean_box(0), lean_box(0), v___x_314_, v___f_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object* v_m_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_u_321_, lean_object* v_type_322_, lean_object* v_semiringInst_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_317_, v_inst_318_, v_inst_319_, v_inst_320_, v_u_321_, v_type_322_, v_semiringInst_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object* v___x_325_, lean_object* v___x_326_, lean_object* v___x_327_, lean_object* v_type_328_, lean_object* v_canonExpr_329_, lean_object* v_inst_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = l_Lean_Name_mkStr2(v___x_325_, v___x_326_);
v___x_332_ = l_Lean_mkConst(v___x_331_, v___x_327_);
v___x_333_ = l_Lean_mkAppB(v___x_332_, v_type_328_, v_inst_330_);
v___x_334_ = lean_apply_1(v_canonExpr_329_, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object* v___f_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_apply_1(v___f_335_, v_inst_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_338_, lean_object* v_val_339_, lean_object* v_toBind_340_, lean_object* v___f_341_, lean_object* v_____r_342_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_apply_2(v_toPure_338_, lean_box(0), v_val_339_);
v___x_344_ = lean_apply_4(v_toBind_340_, lean_box(0), lean_box(0), v___x_343_, v___f_341_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_345_, lean_object* v_inst_x27_346_, lean_object* v_toBind_347_, lean_object* v___f_348_, lean_object* v___f_349_, lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v_inst_352_, lean_object* v_____do__lift_353_){
_start:
{
if (lean_obj_tag(v_____do__lift_353_) == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_inst_352_);
lean_dec_ref(v___x_351_);
lean_dec_ref(v___x_350_);
lean_dec(v___f_349_);
v___x_354_ = lean_apply_2(v_toPure_345_, lean_box(0), v_inst_x27_346_);
v___x_355_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_354_, v___f_348_);
return v___x_355_;
}
else
{
lean_object* v_val_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___f_348_);
v_val_356_ = lean_ctor_get(v_____do__lift_353_, 0);
lean_inc_n(v_val_356_, 2);
lean_dec_ref_known(v_____do__lift_353_, 1);
lean_inc(v_toBind_347_);
v___f_357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_357_, 0, v_toPure_345_);
lean_closure_set(v___f_357_, 1, v_val_356_);
lean_closure_set(v___f_357_, 2, v_toBind_347_);
lean_closure_set(v___f_357_, 3, v___f_349_);
v___x_358_ = l_Lean_Name_mkStr2(v___x_350_, v___x_351_);
v___x_359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_359_, 0, v___x_358_);
lean_closure_set(v___x_359_, 1, v_val_356_);
lean_closure_set(v___x_359_, 2, v_inst_x27_346_);
v___x_360_ = lean_apply_2(v_inst_352_, lean_box(0), v___x_359_);
v___x_361_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_360_, v___f_357_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_u_374_, lean_object* v_type_375_, lean_object* v_semiringInst_376_){
_start:
{
lean_object* v_toApplicative_377_; lean_object* v_toBind_378_; lean_object* v_canonExpr_379_; lean_object* v_synthInstance_x3f_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_402_; 
v_toApplicative_377_ = lean_ctor_get(v_inst_372_, 0);
lean_inc_ref(v_toApplicative_377_);
v_toBind_378_ = lean_ctor_get(v_inst_372_, 1);
lean_inc(v_toBind_378_);
lean_dec_ref(v_inst_372_);
v_canonExpr_379_ = lean_ctor_get(v_inst_373_, 0);
v_synthInstance_x3f_380_ = lean_ctor_get(v_inst_373_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v_inst_373_);
if (v_isSharedCheck_402_ == 0)
{
v___x_382_ = v_inst_373_;
v_isShared_383_ = v_isSharedCheck_402_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_synthInstance_x3f_380_);
lean_inc(v_canonExpr_379_);
lean_dec(v_inst_373_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_402_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_toPure_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v_toPure_384_ = lean_ctor_get(v_toApplicative_377_, 1);
lean_inc(v_toPure_384_);
lean_dec_ref(v_toApplicative_377_);
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0));
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1));
v___x_387_ = lean_box(0);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 1);
lean_ctor_set(v___x_382_, 1, v___x_387_);
lean_ctor_set(v___x_382_, 0, v_u_374_);
v___x_389_ = v___x_382_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_u_374_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_387_);
v___x_389_ = v_reuseFailAlloc_401_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v_inst_x27_391_; lean_object* v___x_392_; lean_object* v___f_393_; lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_instType_397_; lean_object* v___x_398_; lean_object* v___f_399_; lean_object* v___x_400_; 
lean_inc_ref_n(v___x_389_, 2);
v___x_390_ = l_Lean_mkConst(v___x_386_, v___x_389_);
lean_inc_ref_n(v_type_375_, 2);
v_inst_x27_391_ = l_Lean_mkAppB(v___x_390_, v_type_375_, v_semiringInst_376_);
v___x_392_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2));
v___f_393_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_393_, 0, v___x_392_);
lean_closure_set(v___f_393_, 1, v___x_385_);
lean_closure_set(v___f_393_, 2, v___x_389_);
lean_closure_set(v___f_393_, 3, v_type_375_);
lean_closure_set(v___f_393_, 4, v_canonExpr_379_);
v___f_394_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_394_, 0, v___f_393_);
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3));
v___x_396_ = l_Lean_mkConst(v___x_395_, v___x_389_);
v_instType_397_ = l_Lean_Expr_app___override(v___x_396_, v_type_375_);
v___x_398_ = lean_apply_1(v_synthInstance_x3f_380_, v_instType_397_);
lean_inc_ref(v___f_394_);
lean_inc(v_toBind_378_);
v___f_399_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_399_, 0, v_toPure_384_);
lean_closure_set(v___f_399_, 1, v_inst_x27_391_);
lean_closure_set(v___f_399_, 2, v_toBind_378_);
lean_closure_set(v___f_399_, 3, v___f_394_);
lean_closure_set(v___f_399_, 4, v___f_394_);
lean_closure_set(v___f_399_, 5, v___x_392_);
lean_closure_set(v___f_399_, 6, v___x_385_);
lean_closure_set(v___f_399_, 7, v_inst_371_);
v___x_400_ = lean_apply_4(v_toBind_378_, lean_box(0), lean_box(0), v___x_398_, v___f_399_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object* v_m_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_u_407_, lean_object* v_type_408_, lean_object* v_semiringInst_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_404_, v_inst_405_, v_inst_406_, v_u_407_, v_type_408_, v_semiringInst_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0(lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v_scalar_414_, lean_object* v_type_415_, lean_object* v_canonExpr_416_, lean_object* v_inst_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0));
v___x_419_ = l_Lean_Name_mkStr2(v___x_412_, v___x_418_);
v___x_420_ = l_Lean_mkConst(v___x_419_, v___x_413_);
lean_inc_ref(v_type_415_);
v___x_421_ = l_Lean_mkApp4(v___x_420_, v_scalar_414_, v_type_415_, v_type_415_, v_inst_417_);
v___x_422_ = lean_apply_1(v_canonExpr_416_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4(lean_object* v_toPure_423_, lean_object* v_inst_x27_424_, lean_object* v_toBind_425_, lean_object* v___f_426_, lean_object* v___f_427_, lean_object* v___x_428_, lean_object* v_inst_429_, lean_object* v_____do__lift_430_){
_start:
{
if (lean_obj_tag(v_____do__lift_430_) == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_inst_429_);
lean_dec_ref(v___x_428_);
lean_dec(v___f_427_);
v___x_431_ = lean_apply_2(v_toPure_423_, lean_box(0), v_inst_x27_424_);
v___x_432_ = lean_apply_4(v_toBind_425_, lean_box(0), lean_box(0), v___x_431_, v___f_426_);
return v___x_432_;
}
else
{
lean_object* v_val_433_; lean_object* v___f_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v___f_426_);
v_val_433_ = lean_ctor_get(v_____do__lift_430_, 0);
lean_inc_n(v_val_433_, 2);
lean_dec_ref_known(v_____do__lift_430_, 1);
lean_inc(v_toBind_425_);
v___f_434_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_434_, 0, v_toPure_423_);
lean_closure_set(v___f_434_, 1, v_val_433_);
lean_closure_set(v___f_434_, 2, v_toBind_425_);
lean_closure_set(v___f_434_, 3, v___f_427_);
v___x_435_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0));
v___x_436_ = l_Lean_Name_mkStr2(v___x_428_, v___x_435_);
v___x_437_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_437_, 0, v___x_436_);
lean_closure_set(v___x_437_, 1, v_val_433_);
lean_closure_set(v___x_437_, 2, v_inst_x27_424_);
v___x_438_ = lean_apply_2(v_inst_429_, lean_box(0), v___x_437_);
v___x_439_ = lean_apply_4(v_toBind_425_, lean_box(0), lean_box(0), v___x_438_, v___f_434_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_u_449_, lean_object* v_type_450_, lean_object* v_scalar_451_, lean_object* v_expectedSMulInst_452_){
_start:
{
lean_object* v_toApplicative_453_; lean_object* v_toBind_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_487_; 
v_toApplicative_453_ = lean_ctor_get(v_inst_447_, 0);
v_toBind_454_ = lean_ctor_get(v_inst_447_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_inst_447_);
if (v_isSharedCheck_487_ == 0)
{
v___x_456_ = v_inst_447_;
v_isShared_457_ = v_isSharedCheck_487_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_toBind_454_);
lean_inc(v_toApplicative_453_);
lean_dec(v_inst_447_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_487_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_canonExpr_458_; lean_object* v_synthInstance_x3f_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_486_; 
v_canonExpr_458_ = lean_ctor_get(v_inst_448_, 0);
v_synthInstance_x3f_459_ = lean_ctor_get(v_inst_448_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_inst_448_);
if (v_isSharedCheck_486_ == 0)
{
v___x_461_ = v_inst_448_;
v_isShared_462_ = v_isSharedCheck_486_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_synthInstance_x3f_459_);
lean_inc(v_canonExpr_458_);
lean_dec(v_inst_448_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_486_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1));
v___x_464_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_465_ = lean_box(0);
lean_inc(v_u_449_);
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 1);
lean_ctor_set(v___x_461_, 1, v___x_465_);
lean_ctor_set(v___x_461_, 0, v_u_449_);
v___x_467_ = v___x_461_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_u_449_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_485_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
lean_inc_ref(v___x_467_);
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 1);
lean_ctor_set(v___x_456_, 1, v___x_467_);
lean_ctor_set(v___x_456_, 0, v___x_464_);
v___x_469_ = v___x_456_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_484_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v_inst_x27_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_toPure_478_; lean_object* v___f_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___f_482_; lean_object* v___x_483_; 
v___x_470_ = l_Lean_mkConst(v___x_463_, v___x_469_);
lean_inc_ref_n(v_type_450_, 3);
lean_inc_ref_n(v_scalar_451_, 2);
v_inst_x27_471_ = l_Lean_mkApp3(v___x_470_, v_scalar_451_, v_type_450_, v_expectedSMulInst_452_);
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2));
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3));
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v_u_449_);
lean_ctor_set(v___x_474_, 1, v___x_467_);
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_464_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
lean_inc_ref(v___x_475_);
v___x_476_ = l_Lean_mkConst(v___x_473_, v___x_475_);
v___x_477_ = l_Lean_mkApp3(v___x_476_, v_scalar_451_, v_type_450_, v_type_450_);
v_toPure_478_ = lean_ctor_get(v_toApplicative_453_, 1);
lean_inc(v_toPure_478_);
lean_dec_ref(v_toApplicative_453_);
v___f_479_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_479_, 0, v___x_472_);
lean_closure_set(v___f_479_, 1, v___x_475_);
lean_closure_set(v___f_479_, 2, v_scalar_451_);
lean_closure_set(v___f_479_, 3, v_type_450_);
lean_closure_set(v___f_479_, 4, v_canonExpr_458_);
v___f_480_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_480_, 0, v___f_479_);
v___x_481_ = lean_apply_1(v_synthInstance_x3f_459_, v___x_477_);
lean_inc_ref(v___f_480_);
lean_inc(v_toBind_454_);
v___f_482_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4), 8, 7);
lean_closure_set(v___f_482_, 0, v_toPure_478_);
lean_closure_set(v___f_482_, 1, v_inst_x27_471_);
lean_closure_set(v___f_482_, 2, v_toBind_454_);
lean_closure_set(v___f_482_, 3, v___f_480_);
lean_closure_set(v___f_482_, 4, v___f_480_);
lean_closure_set(v___f_482_, 5, v___x_472_);
lean_closure_set(v___f_482_, 6, v_inst_446_);
v___x_483_ = lean_apply_4(v_toBind_454_, lean_box(0), lean_box(0), v___x_481_, v___f_482_);
return v___x_483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn(lean_object* v_m_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_u_492_, lean_object* v_type_493_, lean_object* v_scalar_494_, lean_object* v_expectedSMulInst_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_489_, v_inst_490_, v_inst_491_, v_u_492_, v_type_493_, v_scalar_494_, v_expectedSMulInst_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0(lean_object* v_fn_497_, lean_object* v_s_498_){
_start:
{
lean_object* v_id_499_; lean_object* v_type_500_; lean_object* v_u_501_; lean_object* v_ringInst_502_; lean_object* v_semiringInst_503_; lean_object* v_charInst_x3f_504_; uint8_t v_symbolicChar_505_; lean_object* v_addFn_x3f_506_; lean_object* v_mulFn_x3f_507_; lean_object* v_subFn_x3f_508_; lean_object* v_negFn_x3f_509_; lean_object* v_powFn_x3f_510_; lean_object* v_intCastFn_x3f_511_; lean_object* v_natCastFn_x3f_512_; lean_object* v_intSMulFn_x3f_513_; lean_object* v_one_x3f_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_id_499_ = lean_ctor_get(v_s_498_, 0);
v_type_500_ = lean_ctor_get(v_s_498_, 1);
v_u_501_ = lean_ctor_get(v_s_498_, 2);
v_ringInst_502_ = lean_ctor_get(v_s_498_, 3);
v_semiringInst_503_ = lean_ctor_get(v_s_498_, 4);
v_charInst_x3f_504_ = lean_ctor_get(v_s_498_, 5);
v_symbolicChar_505_ = lean_ctor_get_uint8(v_s_498_, sizeof(void*)*16);
v_addFn_x3f_506_ = lean_ctor_get(v_s_498_, 6);
v_mulFn_x3f_507_ = lean_ctor_get(v_s_498_, 7);
v_subFn_x3f_508_ = lean_ctor_get(v_s_498_, 8);
v_negFn_x3f_509_ = lean_ctor_get(v_s_498_, 9);
v_powFn_x3f_510_ = lean_ctor_get(v_s_498_, 10);
v_intCastFn_x3f_511_ = lean_ctor_get(v_s_498_, 11);
v_natCastFn_x3f_512_ = lean_ctor_get(v_s_498_, 12);
v_intSMulFn_x3f_513_ = lean_ctor_get(v_s_498_, 14);
v_one_x3f_514_ = lean_ctor_get(v_s_498_, 15);
v_isSharedCheck_522_ = !lean_is_exclusive(v_s_498_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_s_498_, 13);
lean_dec(v_unused_523_);
v___x_516_ = v_s_498_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_one_x3f_514_);
lean_inc(v_intSMulFn_x3f_513_);
lean_inc(v_natCastFn_x3f_512_);
lean_inc(v_intCastFn_x3f_511_);
lean_inc(v_powFn_x3f_510_);
lean_inc(v_negFn_x3f_509_);
lean_inc(v_subFn_x3f_508_);
lean_inc(v_mulFn_x3f_507_);
lean_inc(v_addFn_x3f_506_);
lean_inc(v_charInst_x3f_504_);
lean_inc(v_semiringInst_503_);
lean_inc(v_ringInst_502_);
lean_inc(v_u_501_);
lean_inc(v_type_500_);
lean_inc(v_id_499_);
lean_dec(v_s_498_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v_fn_497_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 13, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_id_499_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_type_500_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_u_501_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_ringInst_502_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v_semiringInst_503_);
lean_ctor_set(v_reuseFailAlloc_521_, 5, v_charInst_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_521_, 6, v_addFn_x3f_506_);
lean_ctor_set(v_reuseFailAlloc_521_, 7, v_mulFn_x3f_507_);
lean_ctor_set(v_reuseFailAlloc_521_, 8, v_subFn_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_521_, 9, v_negFn_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_521_, 10, v_powFn_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_521_, 11, v_intCastFn_x3f_511_);
lean_ctor_set(v_reuseFailAlloc_521_, 12, v_natCastFn_x3f_512_);
lean_ctor_set(v_reuseFailAlloc_521_, 13, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 14, v_intSMulFn_x3f_513_);
lean_ctor_set(v_reuseFailAlloc_521_, 15, v_one_x3f_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_521_, sizeof(void*)*16, v_symbolicChar_505_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1(lean_object* v_toPure_524_, lean_object* v_fn_525_, lean_object* v_____r_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_apply_2(v_toPure_524_, lean_box(0), v_fn_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2(lean_object* v_toPure_528_, lean_object* v_modifyRing_529_, lean_object* v_toBind_530_, lean_object* v_fn_531_){
_start:
{
lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
lean_inc_ref(v_fn_531_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_532_, 0, v_fn_531_);
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_533_, 0, v_toPure_528_);
lean_closure_set(v___f_533_, 1, v_fn_531_);
v___x_534_ = lean_apply_1(v_modifyRing_529_, v___f_532_);
v___x_535_ = lean_apply_4(v_toBind_530_, lean_box(0), lean_box(0), v___x_534_, v___f_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3(lean_object* v_toPure_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_toBind_546_, lean_object* v___f_547_, lean_object* v_ring_548_){
_start:
{
lean_object* v_natSMulFn_x3f_549_; 
v_natSMulFn_x3f_549_ = lean_ctor_get(v_ring_548_, 13);
if (lean_obj_tag(v_natSMulFn_x3f_549_) == 1)
{
lean_object* v_val_550_; lean_object* v___x_551_; 
lean_inc_ref(v_natSMulFn_x3f_549_);
lean_dec_ref(v_ring_548_);
lean_dec(v___f_547_);
lean_dec(v_toBind_546_);
lean_dec_ref(v_inst_545_);
lean_dec_ref(v_inst_544_);
lean_dec(v_inst_543_);
v_val_550_ = lean_ctor_get(v_natSMulFn_x3f_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v_natSMulFn_x3f_549_, 1);
v___x_551_ = lean_apply_2(v_toPure_542_, lean_box(0), v_val_550_);
return v___x_551_;
}
else
{
lean_object* v_type_552_; lean_object* v_u_553_; lean_object* v_semiringInst_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_toPure_542_);
v_type_552_ = lean_ctor_get(v_ring_548_, 1);
lean_inc_ref_n(v_type_552_, 2);
v_u_553_ = lean_ctor_get(v_ring_548_, 2);
lean_inc_n(v_u_553_, 2);
v_semiringInst_554_ = lean_ctor_get(v_ring_548_, 4);
lean_inc_ref(v_semiringInst_554_);
lean_dec_ref(v_ring_548_);
v___x_555_ = l_Lean_Nat_mkType;
v___x_556_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_557_ = lean_box(0);
v___x_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_558_, 0, v_u_553_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l_Lean_mkConst(v___x_556_, v___x_558_);
v___x_560_ = l_Lean_mkAppB(v___x_559_, v_type_552_, v_semiringInst_554_);
v___x_561_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_543_, v_inst_544_, v_inst_545_, v_u_553_, v_type_552_, v___x_555_, v___x_560_);
v___x_562_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_561_, v___f_547_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_){
_start:
{
lean_object* v_toApplicative_567_; lean_object* v_toBind_568_; lean_object* v_getRing_569_; lean_object* v_modifyRing_570_; lean_object* v_toPure_571_; lean_object* v___f_572_; lean_object* v___f_573_; lean_object* v___x_574_; 
v_toApplicative_567_ = lean_ctor_get(v_inst_564_, 0);
v_toBind_568_ = lean_ctor_get(v_inst_564_, 1);
lean_inc_n(v_toBind_568_, 3);
v_getRing_569_ = lean_ctor_get(v_inst_566_, 0);
lean_inc(v_getRing_569_);
v_modifyRing_570_ = lean_ctor_get(v_inst_566_, 1);
lean_inc(v_modifyRing_570_);
lean_dec_ref(v_inst_566_);
v_toPure_571_ = lean_ctor_get(v_toApplicative_567_, 1);
lean_inc_n(v_toPure_571_, 2);
v___f_572_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_572_, 0, v_toPure_571_);
lean_closure_set(v___f_572_, 1, v_modifyRing_570_);
lean_closure_set(v___f_572_, 2, v_toBind_568_);
v___f_573_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_573_, 0, v_toPure_571_);
lean_closure_set(v___f_573_, 1, v_inst_563_);
lean_closure_set(v___f_573_, 2, v_inst_564_);
lean_closure_set(v___f_573_, 3, v_inst_565_);
lean_closure_set(v___f_573_, 4, v_toBind_568_);
lean_closure_set(v___f_573_, 5, v___f_572_);
v___x_574_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v_getRing_569_, v___f_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn(lean_object* v_m_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0(lean_object* v_fn_581_, lean_object* v_s_582_){
_start:
{
lean_object* v_id_583_; lean_object* v_type_584_; lean_object* v_u_585_; lean_object* v_ringInst_586_; lean_object* v_semiringInst_587_; lean_object* v_charInst_x3f_588_; uint8_t v_symbolicChar_589_; lean_object* v_addFn_x3f_590_; lean_object* v_mulFn_x3f_591_; lean_object* v_subFn_x3f_592_; lean_object* v_negFn_x3f_593_; lean_object* v_powFn_x3f_594_; lean_object* v_intCastFn_x3f_595_; lean_object* v_natCastFn_x3f_596_; lean_object* v_natSMulFn_x3f_597_; lean_object* v_one_x3f_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_606_; 
v_id_583_ = lean_ctor_get(v_s_582_, 0);
v_type_584_ = lean_ctor_get(v_s_582_, 1);
v_u_585_ = lean_ctor_get(v_s_582_, 2);
v_ringInst_586_ = lean_ctor_get(v_s_582_, 3);
v_semiringInst_587_ = lean_ctor_get(v_s_582_, 4);
v_charInst_x3f_588_ = lean_ctor_get(v_s_582_, 5);
v_symbolicChar_589_ = lean_ctor_get_uint8(v_s_582_, sizeof(void*)*16);
v_addFn_x3f_590_ = lean_ctor_get(v_s_582_, 6);
v_mulFn_x3f_591_ = lean_ctor_get(v_s_582_, 7);
v_subFn_x3f_592_ = lean_ctor_get(v_s_582_, 8);
v_negFn_x3f_593_ = lean_ctor_get(v_s_582_, 9);
v_powFn_x3f_594_ = lean_ctor_get(v_s_582_, 10);
v_intCastFn_x3f_595_ = lean_ctor_get(v_s_582_, 11);
v_natCastFn_x3f_596_ = lean_ctor_get(v_s_582_, 12);
v_natSMulFn_x3f_597_ = lean_ctor_get(v_s_582_, 13);
v_one_x3f_598_ = lean_ctor_get(v_s_582_, 15);
v_isSharedCheck_606_ = !lean_is_exclusive(v_s_582_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_s_582_, 14);
lean_dec(v_unused_607_);
v___x_600_ = v_s_582_;
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_one_x3f_598_);
lean_inc(v_natSMulFn_x3f_597_);
lean_inc(v_natCastFn_x3f_596_);
lean_inc(v_intCastFn_x3f_595_);
lean_inc(v_powFn_x3f_594_);
lean_inc(v_negFn_x3f_593_);
lean_inc(v_subFn_x3f_592_);
lean_inc(v_mulFn_x3f_591_);
lean_inc(v_addFn_x3f_590_);
lean_inc(v_charInst_x3f_588_);
lean_inc(v_semiringInst_587_);
lean_inc(v_ringInst_586_);
lean_inc(v_u_585_);
lean_inc(v_type_584_);
lean_inc(v_id_583_);
lean_dec(v_s_582_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_fn_581_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 14, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_id_583_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_type_584_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_u_585_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_ringInst_586_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_semiringInst_587_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v_charInst_x3f_588_);
lean_ctor_set(v_reuseFailAlloc_605_, 6, v_addFn_x3f_590_);
lean_ctor_set(v_reuseFailAlloc_605_, 7, v_mulFn_x3f_591_);
lean_ctor_set(v_reuseFailAlloc_605_, 8, v_subFn_x3f_592_);
lean_ctor_set(v_reuseFailAlloc_605_, 9, v_negFn_x3f_593_);
lean_ctor_set(v_reuseFailAlloc_605_, 10, v_powFn_x3f_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 11, v_intCastFn_x3f_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 12, v_natCastFn_x3f_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 13, v_natSMulFn_x3f_597_);
lean_ctor_set(v_reuseFailAlloc_605_, 14, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_605_, 15, v_one_x3f_598_);
lean_ctor_set_uint8(v_reuseFailAlloc_605_, sizeof(void*)*16, v_symbolicChar_589_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2(lean_object* v_toPure_608_, lean_object* v_modifyRing_609_, lean_object* v_toBind_610_, lean_object* v_fn_611_){
_start:
{
lean_object* v___f_612_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc_ref(v_fn_611_);
v___f_612_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_612_, 0, v_fn_611_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_613_, 0, v_toPure_608_);
lean_closure_set(v___f_613_, 1, v_fn_611_);
v___x_614_ = lean_apply_1(v_modifyRing_609_, v___f_612_);
v___x_615_ = lean_apply_4(v_toBind_610_, lean_box(0), lean_box(0), v___x_614_, v___f_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1(lean_object* v_toPure_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_toBind_627_, lean_object* v___f_628_, lean_object* v_ring_629_){
_start:
{
lean_object* v_intSMulFn_x3f_630_; 
v_intSMulFn_x3f_630_ = lean_ctor_get(v_ring_629_, 14);
if (lean_obj_tag(v_intSMulFn_x3f_630_) == 1)
{
lean_object* v_val_631_; lean_object* v___x_632_; 
lean_inc_ref(v_intSMulFn_x3f_630_);
lean_dec_ref(v_ring_629_);
lean_dec(v___f_628_);
lean_dec(v_toBind_627_);
lean_dec_ref(v_inst_626_);
lean_dec_ref(v_inst_625_);
lean_dec(v_inst_624_);
v_val_631_ = lean_ctor_get(v_intSMulFn_x3f_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v_intSMulFn_x3f_630_, 1);
v___x_632_ = lean_apply_2(v_toPure_623_, lean_box(0), v_val_631_);
return v___x_632_;
}
else
{
lean_object* v_type_633_; lean_object* v_u_634_; lean_object* v_ringInst_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v_toPure_623_);
v_type_633_ = lean_ctor_get(v_ring_629_, 1);
lean_inc_ref_n(v_type_633_, 2);
v_u_634_ = lean_ctor_get(v_ring_629_, 2);
lean_inc_n(v_u_634_, 2);
v_ringInst_635_ = lean_ctor_get(v_ring_629_, 3);
lean_inc_ref(v_ringInst_635_);
lean_dec_ref(v_ring_629_);
v___x_636_ = l_Lean_Int_mkType;
v___x_637_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2));
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v_u_634_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_mkConst(v___x_637_, v___x_639_);
v___x_641_ = l_Lean_mkAppB(v___x_640_, v_type_633_, v_ringInst_635_);
v___x_642_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_624_, v_inst_625_, v_inst_626_, v_u_634_, v_type_633_, v___x_636_, v___x_641_);
v___x_643_ = lean_apply_4(v_toBind_627_, lean_box(0), lean_box(0), v___x_642_, v___f_628_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_){
_start:
{
lean_object* v_toApplicative_648_; lean_object* v_toBind_649_; lean_object* v_getRing_650_; lean_object* v_modifyRing_651_; lean_object* v_toPure_652_; lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___x_655_; 
v_toApplicative_648_ = lean_ctor_get(v_inst_645_, 0);
v_toBind_649_ = lean_ctor_get(v_inst_645_, 1);
lean_inc_n(v_toBind_649_, 3);
v_getRing_650_ = lean_ctor_get(v_inst_647_, 0);
lean_inc(v_getRing_650_);
v_modifyRing_651_ = lean_ctor_get(v_inst_647_, 1);
lean_inc(v_modifyRing_651_);
lean_dec_ref(v_inst_647_);
v_toPure_652_ = lean_ctor_get(v_toApplicative_648_, 1);
lean_inc_n(v_toPure_652_, 2);
v___f_653_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_653_, 0, v_toPure_652_);
lean_closure_set(v___f_653_, 1, v_modifyRing_651_);
lean_closure_set(v___f_653_, 2, v_toBind_649_);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1), 7, 6);
lean_closure_set(v___f_654_, 0, v_toPure_652_);
lean_closure_set(v___f_654_, 1, v_inst_644_);
lean_closure_set(v___f_654_, 2, v_inst_645_);
lean_closure_set(v___f_654_, 3, v_inst_646_);
lean_closure_set(v___f_654_, 4, v_toBind_649_);
lean_closure_set(v___f_654_, 5, v___f_653_);
v___x_655_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v_getRing_650_, v___f_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn(lean_object* v_m_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(v_inst_657_, v_inst_658_, v_inst_659_, v_inst_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_662_, lean_object* v_s_663_){
_start:
{
lean_object* v_id_664_; lean_object* v_type_665_; lean_object* v_u_666_; lean_object* v_ringInst_667_; lean_object* v_semiringInst_668_; lean_object* v_charInst_x3f_669_; uint8_t v_symbolicChar_670_; lean_object* v_mulFn_x3f_671_; lean_object* v_subFn_x3f_672_; lean_object* v_negFn_x3f_673_; lean_object* v_powFn_x3f_674_; lean_object* v_intCastFn_x3f_675_; lean_object* v_natCastFn_x3f_676_; lean_object* v_natSMulFn_x3f_677_; lean_object* v_intSMulFn_x3f_678_; lean_object* v_one_x3f_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_687_; 
v_id_664_ = lean_ctor_get(v_s_663_, 0);
v_type_665_ = lean_ctor_get(v_s_663_, 1);
v_u_666_ = lean_ctor_get(v_s_663_, 2);
v_ringInst_667_ = lean_ctor_get(v_s_663_, 3);
v_semiringInst_668_ = lean_ctor_get(v_s_663_, 4);
v_charInst_x3f_669_ = lean_ctor_get(v_s_663_, 5);
v_symbolicChar_670_ = lean_ctor_get_uint8(v_s_663_, sizeof(void*)*16);
v_mulFn_x3f_671_ = lean_ctor_get(v_s_663_, 7);
v_subFn_x3f_672_ = lean_ctor_get(v_s_663_, 8);
v_negFn_x3f_673_ = lean_ctor_get(v_s_663_, 9);
v_powFn_x3f_674_ = lean_ctor_get(v_s_663_, 10);
v_intCastFn_x3f_675_ = lean_ctor_get(v_s_663_, 11);
v_natCastFn_x3f_676_ = lean_ctor_get(v_s_663_, 12);
v_natSMulFn_x3f_677_ = lean_ctor_get(v_s_663_, 13);
v_intSMulFn_x3f_678_ = lean_ctor_get(v_s_663_, 14);
v_one_x3f_679_ = lean_ctor_get(v_s_663_, 15);
v_isSharedCheck_687_ = !lean_is_exclusive(v_s_663_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_s_663_, 6);
lean_dec(v_unused_688_);
v___x_681_ = v_s_663_;
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_one_x3f_679_);
lean_inc(v_intSMulFn_x3f_678_);
lean_inc(v_natSMulFn_x3f_677_);
lean_inc(v_natCastFn_x3f_676_);
lean_inc(v_intCastFn_x3f_675_);
lean_inc(v_powFn_x3f_674_);
lean_inc(v_negFn_x3f_673_);
lean_inc(v_subFn_x3f_672_);
lean_inc(v_mulFn_x3f_671_);
lean_inc(v_charInst_x3f_669_);
lean_inc(v_semiringInst_668_);
lean_inc(v_ringInst_667_);
lean_inc(v_u_666_);
lean_inc(v_type_665_);
lean_inc(v_id_664_);
lean_dec(v_s_663_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v_addFn_662_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 6, v___x_683_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_id_664_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_type_665_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_u_666_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_ringInst_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_semiringInst_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v_charInst_x3f_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_686_, 7, v_mulFn_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_686_, 8, v_subFn_x3f_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 9, v_negFn_x3f_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 10, v_powFn_x3f_674_);
lean_ctor_set(v_reuseFailAlloc_686_, 11, v_intCastFn_x3f_675_);
lean_ctor_set(v_reuseFailAlloc_686_, 12, v_natCastFn_x3f_676_);
lean_ctor_set(v_reuseFailAlloc_686_, 13, v_natSMulFn_x3f_677_);
lean_ctor_set(v_reuseFailAlloc_686_, 14, v_intSMulFn_x3f_678_);
lean_ctor_set(v_reuseFailAlloc_686_, 15, v_one_x3f_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*16, v_symbolicChar_670_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_689_, lean_object* v_addFn_690_, lean_object* v_____r_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = lean_apply_2(v_toPure_689_, lean_box(0), v_addFn_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_693_, lean_object* v_modifyRing_694_, lean_object* v_toBind_695_, lean_object* v_addFn_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___f_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_inc_ref(v_addFn_696_);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_697_, 0, v_addFn_696_);
v___f_698_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_698_, 0, v_toPure_693_);
lean_closure_set(v___f_698_, 1, v_addFn_696_);
v___x_699_ = lean_apply_1(v_modifyRing_694_, v___f_697_);
v___x_700_ = lean_apply_4(v_toBind_695_, lean_box(0), lean_box(0), v___x_699_, v___f_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_717_, lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_toBind_722_, lean_object* v___f_723_, lean_object* v_ring_724_){
_start:
{
lean_object* v_addFn_x3f_725_; 
v_addFn_x3f_725_ = lean_ctor_get(v_ring_724_, 6);
if (lean_obj_tag(v_addFn_x3f_725_) == 1)
{
lean_object* v_val_726_; lean_object* v___x_727_; 
lean_inc_ref(v_addFn_x3f_725_);
lean_dec_ref(v_ring_724_);
lean_dec(v___f_723_);
lean_dec(v_toBind_722_);
lean_dec_ref(v_inst_721_);
lean_dec_ref(v_inst_720_);
lean_dec_ref(v_inst_719_);
lean_dec(v_inst_718_);
v_val_726_ = lean_ctor_get(v_addFn_x3f_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v_addFn_x3f_725_, 1);
v___x_727_ = lean_apply_2(v_toPure_717_, lean_box(0), v_val_726_);
return v___x_727_;
}
else
{
lean_object* v_type_728_; lean_object* v_u_729_; lean_object* v_semiringInst_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_expectedInst_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v_toPure_717_);
v_type_728_ = lean_ctor_get(v_ring_724_, 1);
lean_inc_ref_n(v_type_728_, 3);
v_u_729_ = lean_ctor_get(v_ring_724_, 2);
lean_inc_n(v_u_729_, 2);
v_semiringInst_730_ = lean_ctor_get(v_ring_724_, 4);
lean_inc_ref(v_semiringInst_730_);
lean_dec_ref(v_ring_724_);
v___x_731_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v_u_729_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
lean_inc_ref(v___x_733_);
v___x_734_ = l_Lean_mkConst(v___x_731_, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_736_ = l_Lean_mkConst(v___x_735_, v___x_733_);
v___x_737_ = l_Lean_mkAppB(v___x_736_, v_type_728_, v_semiringInst_730_);
v_expectedInst_738_ = l_Lean_mkAppB(v___x_734_, v_type_728_, v___x_737_);
v___x_739_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_740_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_741_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_718_, v_inst_719_, v_inst_720_, v_inst_721_, v_type_728_, v_u_729_, v___x_739_, v___x_740_, v_expectedInst_738_);
v___x_742_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v___x_741_, v___f_723_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_){
_start:
{
lean_object* v_toApplicative_748_; lean_object* v_toBind_749_; lean_object* v_getRing_750_; lean_object* v_modifyRing_751_; lean_object* v_toPure_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
v_toApplicative_748_ = lean_ctor_get(v_inst_745_, 0);
v_toBind_749_ = lean_ctor_get(v_inst_745_, 1);
lean_inc_n(v_toBind_749_, 3);
v_getRing_750_ = lean_ctor_get(v_inst_747_, 0);
lean_inc(v_getRing_750_);
v_modifyRing_751_ = lean_ctor_get(v_inst_747_, 1);
lean_inc(v_modifyRing_751_);
lean_dec_ref(v_inst_747_);
v_toPure_752_ = lean_ctor_get(v_toApplicative_748_, 1);
lean_inc_n(v_toPure_752_, 2);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_753_, 0, v_toPure_752_);
lean_closure_set(v___f_753_, 1, v_modifyRing_751_);
lean_closure_set(v___f_753_, 2, v_toBind_749_);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_754_, 0, v_toPure_752_);
lean_closure_set(v___f_754_, 1, v_inst_743_);
lean_closure_set(v___f_754_, 2, v_inst_744_);
lean_closure_set(v___f_754_, 3, v_inst_745_);
lean_closure_set(v___f_754_, 4, v_inst_746_);
lean_closure_set(v___f_754_, 5, v_toBind_749_);
lean_closure_set(v___f_754_, 6, v___f_753_);
v___x_755_ = lean_apply_4(v_toBind_749_, lean_box(0), lean_box(0), v_getRing_750_, v___f_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_inst_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_757_, v_inst_758_, v_inst_759_, v_inst_760_, v_inst_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_763_, lean_object* v_s_764_){
_start:
{
lean_object* v_id_765_; lean_object* v_type_766_; lean_object* v_u_767_; lean_object* v_ringInst_768_; lean_object* v_semiringInst_769_; lean_object* v_charInst_x3f_770_; uint8_t v_symbolicChar_771_; lean_object* v_addFn_x3f_772_; lean_object* v_subFn_x3f_773_; lean_object* v_negFn_x3f_774_; lean_object* v_powFn_x3f_775_; lean_object* v_intCastFn_x3f_776_; lean_object* v_natCastFn_x3f_777_; lean_object* v_natSMulFn_x3f_778_; lean_object* v_intSMulFn_x3f_779_; lean_object* v_one_x3f_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_id_765_ = lean_ctor_get(v_s_764_, 0);
v_type_766_ = lean_ctor_get(v_s_764_, 1);
v_u_767_ = lean_ctor_get(v_s_764_, 2);
v_ringInst_768_ = lean_ctor_get(v_s_764_, 3);
v_semiringInst_769_ = lean_ctor_get(v_s_764_, 4);
v_charInst_x3f_770_ = lean_ctor_get(v_s_764_, 5);
v_symbolicChar_771_ = lean_ctor_get_uint8(v_s_764_, sizeof(void*)*16);
v_addFn_x3f_772_ = lean_ctor_get(v_s_764_, 6);
v_subFn_x3f_773_ = lean_ctor_get(v_s_764_, 8);
v_negFn_x3f_774_ = lean_ctor_get(v_s_764_, 9);
v_powFn_x3f_775_ = lean_ctor_get(v_s_764_, 10);
v_intCastFn_x3f_776_ = lean_ctor_get(v_s_764_, 11);
v_natCastFn_x3f_777_ = lean_ctor_get(v_s_764_, 12);
v_natSMulFn_x3f_778_ = lean_ctor_get(v_s_764_, 13);
v_intSMulFn_x3f_779_ = lean_ctor_get(v_s_764_, 14);
v_one_x3f_780_ = lean_ctor_get(v_s_764_, 15);
v_isSharedCheck_788_ = !lean_is_exclusive(v_s_764_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_s_764_, 7);
lean_dec(v_unused_789_);
v___x_782_ = v_s_764_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_one_x3f_780_);
lean_inc(v_intSMulFn_x3f_779_);
lean_inc(v_natSMulFn_x3f_778_);
lean_inc(v_natCastFn_x3f_777_);
lean_inc(v_intCastFn_x3f_776_);
lean_inc(v_powFn_x3f_775_);
lean_inc(v_negFn_x3f_774_);
lean_inc(v_subFn_x3f_773_);
lean_inc(v_addFn_x3f_772_);
lean_inc(v_charInst_x3f_770_);
lean_inc(v_semiringInst_769_);
lean_inc(v_ringInst_768_);
lean_inc(v_u_767_);
lean_inc(v_type_766_);
lean_inc(v_id_765_);
lean_dec(v_s_764_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_mulFn_763_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 7, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_id_765_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_type_766_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_u_767_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_ringInst_768_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_semiringInst_769_);
lean_ctor_set(v_reuseFailAlloc_787_, 5, v_charInst_x3f_770_);
lean_ctor_set(v_reuseFailAlloc_787_, 6, v_addFn_x3f_772_);
lean_ctor_set(v_reuseFailAlloc_787_, 7, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_787_, 8, v_subFn_x3f_773_);
lean_ctor_set(v_reuseFailAlloc_787_, 9, v_negFn_x3f_774_);
lean_ctor_set(v_reuseFailAlloc_787_, 10, v_powFn_x3f_775_);
lean_ctor_set(v_reuseFailAlloc_787_, 11, v_intCastFn_x3f_776_);
lean_ctor_set(v_reuseFailAlloc_787_, 12, v_natCastFn_x3f_777_);
lean_ctor_set(v_reuseFailAlloc_787_, 13, v_natSMulFn_x3f_778_);
lean_ctor_set(v_reuseFailAlloc_787_, 14, v_intSMulFn_x3f_779_);
lean_ctor_set(v_reuseFailAlloc_787_, 15, v_one_x3f_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_787_, sizeof(void*)*16, v_symbolicChar_771_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object* v_toPure_790_, lean_object* v_mulFn_791_, lean_object* v_____r_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = lean_apply_2(v_toPure_790_, lean_box(0), v_mulFn_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object* v_toPure_794_, lean_object* v_modifyRing_795_, lean_object* v_toBind_796_, lean_object* v_mulFn_797_){
_start:
{
lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_inc_ref(v_mulFn_797_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_798_, 0, v_mulFn_797_);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_799_, 0, v_toPure_794_);
lean_closure_set(v___f_799_, 1, v_mulFn_797_);
v___x_800_ = lean_apply_1(v_modifyRing_795_, v___f_798_);
v___x_801_ = lean_apply_4(v_toBind_796_, lean_box(0), lean_box(0), v___x_800_, v___f_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object* v_toPure_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_toBind_823_, lean_object* v___f_824_, lean_object* v_ring_825_){
_start:
{
lean_object* v_mulFn_x3f_826_; 
v_mulFn_x3f_826_ = lean_ctor_get(v_ring_825_, 7);
if (lean_obj_tag(v_mulFn_x3f_826_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_828_; 
lean_inc_ref(v_mulFn_x3f_826_);
lean_dec_ref(v_ring_825_);
lean_dec(v___f_824_);
lean_dec(v_toBind_823_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
lean_dec_ref(v_inst_820_);
lean_dec(v_inst_819_);
v_val_827_ = lean_ctor_get(v_mulFn_x3f_826_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v_mulFn_x3f_826_, 1);
v___x_828_ = lean_apply_2(v_toPure_818_, lean_box(0), v_val_827_);
return v___x_828_;
}
else
{
lean_object* v_type_829_; lean_object* v_u_830_; lean_object* v_semiringInst_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_expectedInst_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec(v_toPure_818_);
v_type_829_ = lean_ctor_get(v_ring_825_, 1);
lean_inc_ref_n(v_type_829_, 3);
v_u_830_ = lean_ctor_get(v_ring_825_, 2);
lean_inc_n(v_u_830_, 2);
v_semiringInst_831_ = lean_ctor_get(v_ring_825_, 4);
lean_inc_ref(v_semiringInst_831_);
lean_dec_ref(v_ring_825_);
v___x_832_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_833_ = lean_box(0);
v___x_834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_834_, 0, v_u_830_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
lean_inc_ref(v___x_834_);
v___x_835_ = l_Lean_mkConst(v___x_832_, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_837_ = l_Lean_mkConst(v___x_836_, v___x_834_);
v___x_838_ = l_Lean_mkAppB(v___x_837_, v_type_829_, v_semiringInst_831_);
v_expectedInst_839_ = l_Lean_mkAppB(v___x_835_, v_type_829_, v___x_838_);
v___x_840_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_841_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_842_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_819_, v_inst_820_, v_inst_821_, v_inst_822_, v_type_829_, v_u_830_, v___x_840_, v___x_841_, v_expectedInst_839_);
v___x_843_ = lean_apply_4(v_toBind_823_, lean_box(0), lean_box(0), v___x_842_, v___f_824_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_){
_start:
{
lean_object* v_toApplicative_849_; lean_object* v_toBind_850_; lean_object* v_getRing_851_; lean_object* v_modifyRing_852_; lean_object* v_toPure_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___x_856_; 
v_toApplicative_849_ = lean_ctor_get(v_inst_846_, 0);
v_toBind_850_ = lean_ctor_get(v_inst_846_, 1);
lean_inc_n(v_toBind_850_, 3);
v_getRing_851_ = lean_ctor_get(v_inst_848_, 0);
lean_inc(v_getRing_851_);
v_modifyRing_852_ = lean_ctor_get(v_inst_848_, 1);
lean_inc(v_modifyRing_852_);
lean_dec_ref(v_inst_848_);
v_toPure_853_ = lean_ctor_get(v_toApplicative_849_, 1);
lean_inc_n(v_toPure_853_, 2);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_854_, 0, v_toPure_853_);
lean_closure_set(v___f_854_, 1, v_modifyRing_852_);
lean_closure_set(v___f_854_, 2, v_toBind_850_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_855_, 0, v_toPure_853_);
lean_closure_set(v___f_855_, 1, v_inst_844_);
lean_closure_set(v___f_855_, 2, v_inst_845_);
lean_closure_set(v___f_855_, 3, v_inst_846_);
lean_closure_set(v___f_855_, 4, v_inst_847_);
lean_closure_set(v___f_855_, 5, v_toBind_850_);
lean_closure_set(v___f_855_, 6, v___f_854_);
v___x_856_ = lean_apply_4(v_toBind_850_, lean_box(0), lean_box(0), v_getRing_851_, v___f_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object* v_m_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_inst_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_858_, v_inst_859_, v_inst_860_, v_inst_861_, v_inst_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object* v_subFn_864_, lean_object* v_s_865_){
_start:
{
lean_object* v_id_866_; lean_object* v_type_867_; lean_object* v_u_868_; lean_object* v_ringInst_869_; lean_object* v_semiringInst_870_; lean_object* v_charInst_x3f_871_; uint8_t v_symbolicChar_872_; lean_object* v_addFn_x3f_873_; lean_object* v_mulFn_x3f_874_; lean_object* v_negFn_x3f_875_; lean_object* v_powFn_x3f_876_; lean_object* v_intCastFn_x3f_877_; lean_object* v_natCastFn_x3f_878_; lean_object* v_natSMulFn_x3f_879_; lean_object* v_intSMulFn_x3f_880_; lean_object* v_one_x3f_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_id_866_ = lean_ctor_get(v_s_865_, 0);
v_type_867_ = lean_ctor_get(v_s_865_, 1);
v_u_868_ = lean_ctor_get(v_s_865_, 2);
v_ringInst_869_ = lean_ctor_get(v_s_865_, 3);
v_semiringInst_870_ = lean_ctor_get(v_s_865_, 4);
v_charInst_x3f_871_ = lean_ctor_get(v_s_865_, 5);
v_symbolicChar_872_ = lean_ctor_get_uint8(v_s_865_, sizeof(void*)*16);
v_addFn_x3f_873_ = lean_ctor_get(v_s_865_, 6);
v_mulFn_x3f_874_ = lean_ctor_get(v_s_865_, 7);
v_negFn_x3f_875_ = lean_ctor_get(v_s_865_, 9);
v_powFn_x3f_876_ = lean_ctor_get(v_s_865_, 10);
v_intCastFn_x3f_877_ = lean_ctor_get(v_s_865_, 11);
v_natCastFn_x3f_878_ = lean_ctor_get(v_s_865_, 12);
v_natSMulFn_x3f_879_ = lean_ctor_get(v_s_865_, 13);
v_intSMulFn_x3f_880_ = lean_ctor_get(v_s_865_, 14);
v_one_x3f_881_ = lean_ctor_get(v_s_865_, 15);
v_isSharedCheck_889_ = !lean_is_exclusive(v_s_865_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_s_865_, 8);
lean_dec(v_unused_890_);
v___x_883_ = v_s_865_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_one_x3f_881_);
lean_inc(v_intSMulFn_x3f_880_);
lean_inc(v_natSMulFn_x3f_879_);
lean_inc(v_natCastFn_x3f_878_);
lean_inc(v_intCastFn_x3f_877_);
lean_inc(v_powFn_x3f_876_);
lean_inc(v_negFn_x3f_875_);
lean_inc(v_mulFn_x3f_874_);
lean_inc(v_addFn_x3f_873_);
lean_inc(v_charInst_x3f_871_);
lean_inc(v_semiringInst_870_);
lean_inc(v_ringInst_869_);
lean_inc(v_u_868_);
lean_inc(v_type_867_);
lean_inc(v_id_866_);
lean_dec(v_s_865_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_subFn_864_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 8, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_id_866_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_type_867_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_u_868_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_ringInst_869_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_semiringInst_870_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v_charInst_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_888_, 6, v_addFn_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 7, v_mulFn_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_888_, 8, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_888_, 9, v_negFn_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_888_, 10, v_powFn_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_888_, 11, v_intCastFn_x3f_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 12, v_natCastFn_x3f_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 13, v_natSMulFn_x3f_879_);
lean_ctor_set(v_reuseFailAlloc_888_, 14, v_intSMulFn_x3f_880_);
lean_ctor_set(v_reuseFailAlloc_888_, 15, v_one_x3f_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, sizeof(void*)*16, v_symbolicChar_872_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_891_, lean_object* v_subFn_892_, lean_object* v_____r_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_apply_2(v_toPure_891_, lean_box(0), v_subFn_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_895_, lean_object* v_modifyRing_896_, lean_object* v_toBind_897_, lean_object* v_subFn_898_){
_start:
{
lean_object* v___f_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_inc_ref(v_subFn_898_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_899_, 0, v_subFn_898_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_900_, 0, v_toPure_895_);
lean_closure_set(v___f_900_, 1, v_subFn_898_);
v___x_901_ = lean_apply_1(v_modifyRing_896_, v___f_899_);
v___x_902_ = lean_apply_4(v_toBind_897_, lean_box(0), lean_box(0), v___x_901_, v___f_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_toBind_924_, lean_object* v___f_925_, lean_object* v_ring_926_){
_start:
{
lean_object* v_subFn_x3f_927_; 
v_subFn_x3f_927_ = lean_ctor_get(v_ring_926_, 8);
if (lean_obj_tag(v_subFn_x3f_927_) == 1)
{
lean_object* v_val_928_; lean_object* v___x_929_; 
lean_inc_ref(v_subFn_x3f_927_);
lean_dec_ref(v_ring_926_);
lean_dec(v___f_925_);
lean_dec(v_toBind_924_);
lean_dec_ref(v_inst_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_inst_921_);
lean_dec(v_inst_920_);
v_val_928_ = lean_ctor_get(v_subFn_x3f_927_, 0);
lean_inc(v_val_928_);
lean_dec_ref_known(v_subFn_x3f_927_, 1);
v___x_929_ = lean_apply_2(v_toPure_919_, lean_box(0), v_val_928_);
return v___x_929_;
}
else
{
lean_object* v_type_930_; lean_object* v_u_931_; lean_object* v_ringInst_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_expectedInst_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v_toPure_919_);
v_type_930_ = lean_ctor_get(v_ring_926_, 1);
lean_inc_ref_n(v_type_930_, 3);
v_u_931_ = lean_ctor_get(v_ring_926_, 2);
lean_inc_n(v_u_931_, 2);
v_ringInst_932_ = lean_ctor_get(v_ring_926_, 3);
lean_inc_ref(v_ringInst_932_);
lean_dec_ref(v_ring_926_);
v___x_933_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_935_, 0, v_u_931_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
lean_inc_ref(v___x_935_);
v___x_936_ = l_Lean_mkConst(v___x_933_, v___x_935_);
v___x_937_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3));
v___x_938_ = l_Lean_mkConst(v___x_937_, v___x_935_);
v___x_939_ = l_Lean_mkAppB(v___x_938_, v_type_930_, v_ringInst_932_);
v_expectedInst_940_ = l_Lean_mkAppB(v___x_936_, v_type_930_, v___x_939_);
v___x_941_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5));
v___x_942_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7));
v___x_943_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_920_, v_inst_921_, v_inst_922_, v_inst_923_, v_type_930_, v_u_931_, v___x_941_, v___x_942_, v_expectedInst_940_);
v___x_944_ = lean_apply_4(v_toBind_924_, lean_box(0), lean_box(0), v___x_943_, v___f_925_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_inst_948_, lean_object* v_inst_949_){
_start:
{
lean_object* v_toApplicative_950_; lean_object* v_toBind_951_; lean_object* v_getRing_952_; lean_object* v_modifyRing_953_; lean_object* v_toPure_954_; lean_object* v___f_955_; lean_object* v___f_956_; lean_object* v___x_957_; 
v_toApplicative_950_ = lean_ctor_get(v_inst_947_, 0);
v_toBind_951_ = lean_ctor_get(v_inst_947_, 1);
lean_inc_n(v_toBind_951_, 3);
v_getRing_952_ = lean_ctor_get(v_inst_949_, 0);
lean_inc(v_getRing_952_);
v_modifyRing_953_ = lean_ctor_get(v_inst_949_, 1);
lean_inc(v_modifyRing_953_);
lean_dec_ref(v_inst_949_);
v_toPure_954_ = lean_ctor_get(v_toApplicative_950_, 1);
lean_inc_n(v_toPure_954_, 2);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_955_, 0, v_toPure_954_);
lean_closure_set(v___f_955_, 1, v_modifyRing_953_);
lean_closure_set(v___f_955_, 2, v_toBind_951_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_956_, 0, v_toPure_954_);
lean_closure_set(v___f_956_, 1, v_inst_945_);
lean_closure_set(v___f_956_, 2, v_inst_946_);
lean_closure_set(v___f_956_, 3, v_inst_947_);
lean_closure_set(v___f_956_, 4, v_inst_948_);
lean_closure_set(v___f_956_, 5, v_toBind_951_);
lean_closure_set(v___f_956_, 6, v___f_955_);
v___x_957_ = lean_apply_4(v_toBind_951_, lean_box(0), lean_box(0), v_getRing_952_, v___f_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_inst_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_959_, v_inst_960_, v_inst_961_, v_inst_962_, v_inst_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_965_, lean_object* v_s_966_){
_start:
{
lean_object* v_id_967_; lean_object* v_type_968_; lean_object* v_u_969_; lean_object* v_ringInst_970_; lean_object* v_semiringInst_971_; lean_object* v_charInst_x3f_972_; uint8_t v_symbolicChar_973_; lean_object* v_addFn_x3f_974_; lean_object* v_mulFn_x3f_975_; lean_object* v_subFn_x3f_976_; lean_object* v_powFn_x3f_977_; lean_object* v_intCastFn_x3f_978_; lean_object* v_natCastFn_x3f_979_; lean_object* v_natSMulFn_x3f_980_; lean_object* v_intSMulFn_x3f_981_; lean_object* v_one_x3f_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
v_id_967_ = lean_ctor_get(v_s_966_, 0);
v_type_968_ = lean_ctor_get(v_s_966_, 1);
v_u_969_ = lean_ctor_get(v_s_966_, 2);
v_ringInst_970_ = lean_ctor_get(v_s_966_, 3);
v_semiringInst_971_ = lean_ctor_get(v_s_966_, 4);
v_charInst_x3f_972_ = lean_ctor_get(v_s_966_, 5);
v_symbolicChar_973_ = lean_ctor_get_uint8(v_s_966_, sizeof(void*)*16);
v_addFn_x3f_974_ = lean_ctor_get(v_s_966_, 6);
v_mulFn_x3f_975_ = lean_ctor_get(v_s_966_, 7);
v_subFn_x3f_976_ = lean_ctor_get(v_s_966_, 8);
v_powFn_x3f_977_ = lean_ctor_get(v_s_966_, 10);
v_intCastFn_x3f_978_ = lean_ctor_get(v_s_966_, 11);
v_natCastFn_x3f_979_ = lean_ctor_get(v_s_966_, 12);
v_natSMulFn_x3f_980_ = lean_ctor_get(v_s_966_, 13);
v_intSMulFn_x3f_981_ = lean_ctor_get(v_s_966_, 14);
v_one_x3f_982_ = lean_ctor_get(v_s_966_, 15);
v_isSharedCheck_990_ = !lean_is_exclusive(v_s_966_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v_s_966_, 9);
lean_dec(v_unused_991_);
v___x_984_ = v_s_966_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_one_x3f_982_);
lean_inc(v_intSMulFn_x3f_981_);
lean_inc(v_natSMulFn_x3f_980_);
lean_inc(v_natCastFn_x3f_979_);
lean_inc(v_intCastFn_x3f_978_);
lean_inc(v_powFn_x3f_977_);
lean_inc(v_subFn_x3f_976_);
lean_inc(v_mulFn_x3f_975_);
lean_inc(v_addFn_x3f_974_);
lean_inc(v_charInst_x3f_972_);
lean_inc(v_semiringInst_971_);
lean_inc(v_ringInst_970_);
lean_inc(v_u_969_);
lean_inc(v_type_968_);
lean_inc(v_id_967_);
lean_dec(v_s_966_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_negFn_965_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 9, v___x_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_id_967_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_type_968_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_u_969_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_ringInst_970_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_semiringInst_971_);
lean_ctor_set(v_reuseFailAlloc_989_, 5, v_charInst_x3f_972_);
lean_ctor_set(v_reuseFailAlloc_989_, 6, v_addFn_x3f_974_);
lean_ctor_set(v_reuseFailAlloc_989_, 7, v_mulFn_x3f_975_);
lean_ctor_set(v_reuseFailAlloc_989_, 8, v_subFn_x3f_976_);
lean_ctor_set(v_reuseFailAlloc_989_, 9, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 10, v_powFn_x3f_977_);
lean_ctor_set(v_reuseFailAlloc_989_, 11, v_intCastFn_x3f_978_);
lean_ctor_set(v_reuseFailAlloc_989_, 12, v_natCastFn_x3f_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 13, v_natSMulFn_x3f_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 14, v_intSMulFn_x3f_981_);
lean_ctor_set(v_reuseFailAlloc_989_, 15, v_one_x3f_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*16, v_symbolicChar_973_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_992_, lean_object* v_negFn_993_, lean_object* v_____r_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = lean_apply_2(v_toPure_992_, lean_box(0), v_negFn_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_996_, lean_object* v_modifyRing_997_, lean_object* v_toBind_998_, lean_object* v_negFn_999_){
_start:
{
lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_inc_ref(v_negFn_999_);
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1000_, 0, v_negFn_999_);
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1001_, 0, v_toPure_996_);
lean_closure_set(v___f_1001_, 1, v_negFn_999_);
v___x_1002_ = lean_apply_1(v_modifyRing_997_, v___f_1000_);
v___x_1003_ = lean_apply_4(v_toBind_998_, lean_box(0), lean_box(0), v___x_1002_, v___f_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_toBind_1022_, lean_object* v___f_1023_, lean_object* v_ring_1024_){
_start:
{
lean_object* v_negFn_x3f_1025_; 
v_negFn_x3f_1025_ = lean_ctor_get(v_ring_1024_, 9);
if (lean_obj_tag(v_negFn_x3f_1025_) == 1)
{
lean_object* v_val_1026_; lean_object* v___x_1027_; 
lean_inc_ref(v_negFn_x3f_1025_);
lean_dec_ref(v_ring_1024_);
lean_dec(v___f_1023_);
lean_dec(v_toBind_1022_);
lean_dec_ref(v_inst_1021_);
lean_dec_ref(v_inst_1020_);
lean_dec_ref(v_inst_1019_);
lean_dec(v_inst_1018_);
v_val_1026_ = lean_ctor_get(v_negFn_x3f_1025_, 0);
lean_inc(v_val_1026_);
lean_dec_ref_known(v_negFn_x3f_1025_, 1);
v___x_1027_ = lean_apply_2(v_toPure_1017_, lean_box(0), v_val_1026_);
return v___x_1027_;
}
else
{
lean_object* v_type_1028_; lean_object* v_u_1029_; lean_object* v_ringInst_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_expectedInst_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v_toPure_1017_);
v_type_1028_ = lean_ctor_get(v_ring_1024_, 1);
lean_inc_ref_n(v_type_1028_, 2);
v_u_1029_ = lean_ctor_get(v_ring_1024_, 2);
lean_inc_n(v_u_1029_, 2);
v_ringInst_1030_ = lean_ctor_get(v_ring_1024_, 3);
lean_inc_ref(v_ringInst_1030_);
lean_dec_ref(v_ring_1024_);
v___x_1031_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_u_1029_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_mkConst(v___x_1031_, v___x_1033_);
v_expectedInst_1035_ = l_Lean_mkAppB(v___x_1034_, v_type_1028_, v_ringInst_1030_);
v___x_1036_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_1037_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_1038_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1018_, v_inst_1019_, v_inst_1020_, v_inst_1021_, v_type_1028_, v_u_1029_, v___x_1036_, v___x_1037_, v_expectedInst_1035_);
v___x_1039_ = lean_apply_4(v_toBind_1022_, lean_box(0), lean_box(0), v___x_1038_, v___f_1023_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_){
_start:
{
lean_object* v_toApplicative_1045_; lean_object* v_toBind_1046_; lean_object* v_getRing_1047_; lean_object* v_modifyRing_1048_; lean_object* v_toPure_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; 
v_toApplicative_1045_ = lean_ctor_get(v_inst_1042_, 0);
v_toBind_1046_ = lean_ctor_get(v_inst_1042_, 1);
lean_inc_n(v_toBind_1046_, 3);
v_getRing_1047_ = lean_ctor_get(v_inst_1044_, 0);
lean_inc(v_getRing_1047_);
v_modifyRing_1048_ = lean_ctor_get(v_inst_1044_, 1);
lean_inc(v_modifyRing_1048_);
lean_dec_ref(v_inst_1044_);
v_toPure_1049_ = lean_ctor_get(v_toApplicative_1045_, 1);
lean_inc_n(v_toPure_1049_, 2);
v___f_1050_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1050_, 0, v_toPure_1049_);
lean_closure_set(v___f_1050_, 1, v_modifyRing_1048_);
lean_closure_set(v___f_1050_, 2, v_toBind_1046_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1051_, 0, v_toPure_1049_);
lean_closure_set(v___f_1051_, 1, v_inst_1040_);
lean_closure_set(v___f_1051_, 2, v_inst_1041_);
lean_closure_set(v___f_1051_, 3, v_inst_1042_);
lean_closure_set(v___f_1051_, 4, v_inst_1043_);
lean_closure_set(v___f_1051_, 5, v_toBind_1046_);
lean_closure_set(v___f_1051_, 6, v___f_1050_);
v___x_1052_ = lean_apply_4(v_toBind_1046_, lean_box(0), lean_box(0), v_getRing_1047_, v___f_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_1054_, v_inst_1055_, v_inst_1056_, v_inst_1057_, v_inst_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_1060_, lean_object* v_s_1061_){
_start:
{
lean_object* v_id_1062_; lean_object* v_type_1063_; lean_object* v_u_1064_; lean_object* v_ringInst_1065_; lean_object* v_semiringInst_1066_; lean_object* v_charInst_x3f_1067_; uint8_t v_symbolicChar_1068_; lean_object* v_addFn_x3f_1069_; lean_object* v_mulFn_x3f_1070_; lean_object* v_subFn_x3f_1071_; lean_object* v_negFn_x3f_1072_; lean_object* v_intCastFn_x3f_1073_; lean_object* v_natCastFn_x3f_1074_; lean_object* v_natSMulFn_x3f_1075_; lean_object* v_intSMulFn_x3f_1076_; lean_object* v_one_x3f_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1085_; 
v_id_1062_ = lean_ctor_get(v_s_1061_, 0);
v_type_1063_ = lean_ctor_get(v_s_1061_, 1);
v_u_1064_ = lean_ctor_get(v_s_1061_, 2);
v_ringInst_1065_ = lean_ctor_get(v_s_1061_, 3);
v_semiringInst_1066_ = lean_ctor_get(v_s_1061_, 4);
v_charInst_x3f_1067_ = lean_ctor_get(v_s_1061_, 5);
v_symbolicChar_1068_ = lean_ctor_get_uint8(v_s_1061_, sizeof(void*)*16);
v_addFn_x3f_1069_ = lean_ctor_get(v_s_1061_, 6);
v_mulFn_x3f_1070_ = lean_ctor_get(v_s_1061_, 7);
v_subFn_x3f_1071_ = lean_ctor_get(v_s_1061_, 8);
v_negFn_x3f_1072_ = lean_ctor_get(v_s_1061_, 9);
v_intCastFn_x3f_1073_ = lean_ctor_get(v_s_1061_, 11);
v_natCastFn_x3f_1074_ = lean_ctor_get(v_s_1061_, 12);
v_natSMulFn_x3f_1075_ = lean_ctor_get(v_s_1061_, 13);
v_intSMulFn_x3f_1076_ = lean_ctor_get(v_s_1061_, 14);
v_one_x3f_1077_ = lean_ctor_get(v_s_1061_, 15);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_s_1061_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_s_1061_, 10);
lean_dec(v_unused_1086_);
v___x_1079_ = v_s_1061_;
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_one_x3f_1077_);
lean_inc(v_intSMulFn_x3f_1076_);
lean_inc(v_natSMulFn_x3f_1075_);
lean_inc(v_natCastFn_x3f_1074_);
lean_inc(v_intCastFn_x3f_1073_);
lean_inc(v_negFn_x3f_1072_);
lean_inc(v_subFn_x3f_1071_);
lean_inc(v_mulFn_x3f_1070_);
lean_inc(v_addFn_x3f_1069_);
lean_inc(v_charInst_x3f_1067_);
lean_inc(v_semiringInst_1066_);
lean_inc(v_ringInst_1065_);
lean_inc(v_u_1064_);
lean_inc(v_type_1063_);
lean_inc(v_id_1062_);
lean_dec(v_s_1061_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_powFn_1060_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 10, v___x_1081_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_id_1062_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_type_1063_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_u_1064_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v_ringInst_1065_);
lean_ctor_set(v_reuseFailAlloc_1084_, 4, v_semiringInst_1066_);
lean_ctor_set(v_reuseFailAlloc_1084_, 5, v_charInst_x3f_1067_);
lean_ctor_set(v_reuseFailAlloc_1084_, 6, v_addFn_x3f_1069_);
lean_ctor_set(v_reuseFailAlloc_1084_, 7, v_mulFn_x3f_1070_);
lean_ctor_set(v_reuseFailAlloc_1084_, 8, v_subFn_x3f_1071_);
lean_ctor_set(v_reuseFailAlloc_1084_, 9, v_negFn_x3f_1072_);
lean_ctor_set(v_reuseFailAlloc_1084_, 10, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1084_, 11, v_intCastFn_x3f_1073_);
lean_ctor_set(v_reuseFailAlloc_1084_, 12, v_natCastFn_x3f_1074_);
lean_ctor_set(v_reuseFailAlloc_1084_, 13, v_natSMulFn_x3f_1075_);
lean_ctor_set(v_reuseFailAlloc_1084_, 14, v_intSMulFn_x3f_1076_);
lean_ctor_set(v_reuseFailAlloc_1084_, 15, v_one_x3f_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*16, v_symbolicChar_1068_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_1087_, lean_object* v_powFn_1088_, lean_object* v_____r_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_apply_2(v_toPure_1087_, lean_box(0), v_powFn_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_1091_, lean_object* v_modifyRing_1092_, lean_object* v_toBind_1093_, lean_object* v_powFn_1094_){
_start:
{
lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_inc_ref(v_powFn_1094_);
v___f_1095_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1095_, 0, v_powFn_1094_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1096_, 0, v_toPure_1091_);
lean_closure_set(v___f_1096_, 1, v_powFn_1094_);
v___x_1097_ = lean_apply_1(v_modifyRing_1092_, v___f_1095_);
v___x_1098_ = lean_apply_4(v_toBind_1093_, lean_box(0), lean_box(0), v___x_1097_, v___f_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_toBind_1104_, lean_object* v___f_1105_, lean_object* v_ring_1106_){
_start:
{
lean_object* v_powFn_x3f_1107_; 
v_powFn_x3f_1107_ = lean_ctor_get(v_ring_1106_, 10);
if (lean_obj_tag(v_powFn_x3f_1107_) == 1)
{
lean_object* v_val_1108_; lean_object* v___x_1109_; 
lean_inc_ref(v_powFn_x3f_1107_);
lean_dec_ref(v_ring_1106_);
lean_dec(v___f_1105_);
lean_dec(v_toBind_1104_);
lean_dec_ref(v_inst_1103_);
lean_dec_ref(v_inst_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec(v_inst_1100_);
v_val_1108_ = lean_ctor_get(v_powFn_x3f_1107_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v_powFn_x3f_1107_, 1);
v___x_1109_ = lean_apply_2(v_toPure_1099_, lean_box(0), v_val_1108_);
return v___x_1109_;
}
else
{
lean_object* v_type_1110_; lean_object* v_u_1111_; lean_object* v_semiringInst_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v_toPure_1099_);
v_type_1110_ = lean_ctor_get(v_ring_1106_, 1);
lean_inc_ref(v_type_1110_);
v_u_1111_ = lean_ctor_get(v_ring_1106_, 2);
lean_inc(v_u_1111_);
v_semiringInst_1112_ = lean_ctor_get(v_ring_1106_, 4);
lean_inc_ref(v_semiringInst_1112_);
lean_dec_ref(v_ring_1106_);
v___x_1113_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1100_, v_inst_1101_, v_inst_1102_, v_inst_1103_, v_u_1111_, v_type_1110_, v_semiringInst_1112_);
v___x_1114_ = lean_apply_4(v_toBind_1104_, lean_box(0), lean_box(0), v___x_1113_, v___f_1105_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_){
_start:
{
lean_object* v_toApplicative_1120_; lean_object* v_toBind_1121_; lean_object* v_getRing_1122_; lean_object* v_modifyRing_1123_; lean_object* v_toPure_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; 
v_toApplicative_1120_ = lean_ctor_get(v_inst_1117_, 0);
v_toBind_1121_ = lean_ctor_get(v_inst_1117_, 1);
lean_inc_n(v_toBind_1121_, 3);
v_getRing_1122_ = lean_ctor_get(v_inst_1119_, 0);
lean_inc(v_getRing_1122_);
v_modifyRing_1123_ = lean_ctor_get(v_inst_1119_, 1);
lean_inc(v_modifyRing_1123_);
lean_dec_ref(v_inst_1119_);
v_toPure_1124_ = lean_ctor_get(v_toApplicative_1120_, 1);
lean_inc_n(v_toPure_1124_, 2);
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1125_, 0, v_toPure_1124_);
lean_closure_set(v___f_1125_, 1, v_modifyRing_1123_);
lean_closure_set(v___f_1125_, 2, v_toBind_1121_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1126_, 0, v_toPure_1124_);
lean_closure_set(v___f_1126_, 1, v_inst_1115_);
lean_closure_set(v___f_1126_, 2, v_inst_1116_);
lean_closure_set(v___f_1126_, 3, v_inst_1117_);
lean_closure_set(v___f_1126_, 4, v_inst_1118_);
lean_closure_set(v___f_1126_, 5, v_toBind_1121_);
lean_closure_set(v___f_1126_, 6, v___f_1125_);
v___x_1127_ = lean_apply_4(v_toBind_1121_, lean_box(0), lean_box(0), v_getRing_1122_, v___f_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_1129_, v_inst_1130_, v_inst_1131_, v_inst_1132_, v_inst_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_1135_, lean_object* v_s_1136_){
_start:
{
lean_object* v_id_1137_; lean_object* v_type_1138_; lean_object* v_u_1139_; lean_object* v_ringInst_1140_; lean_object* v_semiringInst_1141_; lean_object* v_charInst_x3f_1142_; uint8_t v_symbolicChar_1143_; lean_object* v_addFn_x3f_1144_; lean_object* v_mulFn_x3f_1145_; lean_object* v_subFn_x3f_1146_; lean_object* v_negFn_x3f_1147_; lean_object* v_powFn_x3f_1148_; lean_object* v_natCastFn_x3f_1149_; lean_object* v_natSMulFn_x3f_1150_; lean_object* v_intSMulFn_x3f_1151_; lean_object* v_one_x3f_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v_id_1137_ = lean_ctor_get(v_s_1136_, 0);
v_type_1138_ = lean_ctor_get(v_s_1136_, 1);
v_u_1139_ = lean_ctor_get(v_s_1136_, 2);
v_ringInst_1140_ = lean_ctor_get(v_s_1136_, 3);
v_semiringInst_1141_ = lean_ctor_get(v_s_1136_, 4);
v_charInst_x3f_1142_ = lean_ctor_get(v_s_1136_, 5);
v_symbolicChar_1143_ = lean_ctor_get_uint8(v_s_1136_, sizeof(void*)*16);
v_addFn_x3f_1144_ = lean_ctor_get(v_s_1136_, 6);
v_mulFn_x3f_1145_ = lean_ctor_get(v_s_1136_, 7);
v_subFn_x3f_1146_ = lean_ctor_get(v_s_1136_, 8);
v_negFn_x3f_1147_ = lean_ctor_get(v_s_1136_, 9);
v_powFn_x3f_1148_ = lean_ctor_get(v_s_1136_, 10);
v_natCastFn_x3f_1149_ = lean_ctor_get(v_s_1136_, 12);
v_natSMulFn_x3f_1150_ = lean_ctor_get(v_s_1136_, 13);
v_intSMulFn_x3f_1151_ = lean_ctor_get(v_s_1136_, 14);
v_one_x3f_1152_ = lean_ctor_get(v_s_1136_, 15);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_s_1136_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_s_1136_, 11);
lean_dec(v_unused_1161_);
v___x_1154_ = v_s_1136_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_one_x3f_1152_);
lean_inc(v_intSMulFn_x3f_1151_);
lean_inc(v_natSMulFn_x3f_1150_);
lean_inc(v_natCastFn_x3f_1149_);
lean_inc(v_powFn_x3f_1148_);
lean_inc(v_negFn_x3f_1147_);
lean_inc(v_subFn_x3f_1146_);
lean_inc(v_mulFn_x3f_1145_);
lean_inc(v_addFn_x3f_1144_);
lean_inc(v_charInst_x3f_1142_);
lean_inc(v_semiringInst_1141_);
lean_inc(v_ringInst_1140_);
lean_inc(v_u_1139_);
lean_inc(v_type_1138_);
lean_inc(v_id_1137_);
lean_dec(v_s_1136_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_intCastFn_1135_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 11, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_id_1137_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_type_1138_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_u_1139_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_ringInst_1140_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_semiringInst_1141_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v_charInst_x3f_1142_);
lean_ctor_set(v_reuseFailAlloc_1159_, 6, v_addFn_x3f_1144_);
lean_ctor_set(v_reuseFailAlloc_1159_, 7, v_mulFn_x3f_1145_);
lean_ctor_set(v_reuseFailAlloc_1159_, 8, v_subFn_x3f_1146_);
lean_ctor_set(v_reuseFailAlloc_1159_, 9, v_negFn_x3f_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 10, v_powFn_x3f_1148_);
lean_ctor_set(v_reuseFailAlloc_1159_, 11, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1159_, 12, v_natCastFn_x3f_1149_);
lean_ctor_set(v_reuseFailAlloc_1159_, 13, v_natSMulFn_x3f_1150_);
lean_ctor_set(v_reuseFailAlloc_1159_, 14, v_intSMulFn_x3f_1151_);
lean_ctor_set(v_reuseFailAlloc_1159_, 15, v_one_x3f_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1159_, sizeof(void*)*16, v_symbolicChar_1143_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_1162_, lean_object* v_intCastFn_1163_, lean_object* v_____r_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_apply_2(v_toPure_1162_, lean_box(0), v_intCastFn_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_1166_, lean_object* v_modifyRing_1167_, lean_object* v_toBind_1168_, lean_object* v_intCastFn_1169_){
_start:
{
lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v_intCastFn_1169_);
v___f_1170_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1170_, 0, v_intCastFn_1169_);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1171_, 0, v_toPure_1166_);
lean_closure_set(v___f_1171_, 1, v_intCastFn_1169_);
v___x_1172_ = lean_apply_1(v_modifyRing_1167_, v___f_1170_);
v___x_1173_ = lean_apply_4(v_toBind_1168_, lean_box(0), lean_box(0), v___x_1172_, v___f_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_1174_, lean_object* v___x_1175_, lean_object* v___x_1176_, lean_object* v_type_1177_, lean_object* v_canonExpr_1178_, lean_object* v_toBind_1179_, lean_object* v___f_1180_, lean_object* v_inst_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1182_ = l_Lean_Name_mkStr2(v___x_1174_, v___x_1175_);
v___x_1183_ = l_Lean_mkConst(v___x_1182_, v___x_1176_);
v___x_1184_ = l_Lean_mkAppB(v___x_1183_, v_type_1177_, v_inst_1181_);
v___x_1185_ = lean_apply_1(v_canonExpr_1178_, v___x_1184_);
v___x_1186_ = lean_apply_4(v_toBind_1179_, lean_box(0), lean_box(0), v___x_1185_, v___f_1180_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_1192_, lean_object* v_inst_x27_1193_, lean_object* v_toBind_1194_, lean_object* v___f_1195_, lean_object* v___f_1196_, lean_object* v_inst_1197_, lean_object* v_____do__lift_1198_){
_start:
{
if (lean_obj_tag(v_____do__lift_1198_) == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec(v_inst_1197_);
lean_dec(v___f_1196_);
v___x_1199_ = lean_apply_2(v_toPure_1192_, lean_box(0), v_inst_x27_1193_);
v___x_1200_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v___x_1199_, v___f_1195_);
return v___x_1200_;
}
else
{
lean_object* v_val_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v___f_1195_);
v_val_1201_ = lean_ctor_get(v_____do__lift_1198_, 0);
lean_inc_n(v_val_1201_, 2);
lean_dec_ref_known(v_____do__lift_1198_, 1);
lean_inc(v_toBind_1194_);
v___f_1202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1202_, 0, v_toPure_1192_);
lean_closure_set(v___f_1202_, 1, v_val_1201_);
lean_closure_set(v___f_1202_, 2, v_toBind_1194_);
lean_closure_set(v___f_1202_, 3, v___f_1196_);
v___x_1203_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_1204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_1204_, 0, v___x_1203_);
lean_closure_set(v___x_1204_, 1, v_val_1201_);
lean_closure_set(v___x_1204_, 2, v_inst_x27_1193_);
v___x_1205_ = lean_apply_2(v_inst_1197_, lean_box(0), v___x_1204_);
v___x_1206_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v___x_1205_, v___f_1202_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_1216_, lean_object* v_inst_1217_, lean_object* v_toBind_1218_, lean_object* v___f_1219_, lean_object* v_inst_1220_, lean_object* v_ring_1221_){
_start:
{
lean_object* v_intCastFn_x3f_1222_; 
v_intCastFn_x3f_1222_ = lean_ctor_get(v_ring_1221_, 11);
if (lean_obj_tag(v_intCastFn_x3f_1222_) == 1)
{
lean_object* v_val_1223_; lean_object* v___x_1224_; 
lean_inc_ref(v_intCastFn_x3f_1222_);
lean_dec_ref(v_ring_1221_);
lean_dec(v_inst_1220_);
lean_dec(v___f_1219_);
lean_dec(v_toBind_1218_);
lean_dec_ref(v_inst_1217_);
v_val_1223_ = lean_ctor_get(v_intCastFn_x3f_1222_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v_intCastFn_x3f_1222_, 1);
v___x_1224_ = lean_apply_2(v_toPure_1216_, lean_box(0), v_val_1223_);
return v___x_1224_;
}
else
{
lean_object* v_type_1225_; lean_object* v_u_1226_; lean_object* v_ringInst_1227_; lean_object* v_canonExpr_1228_; lean_object* v_synthInstance_x3f_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1250_; 
v_type_1225_ = lean_ctor_get(v_ring_1221_, 1);
lean_inc_ref(v_type_1225_);
v_u_1226_ = lean_ctor_get(v_ring_1221_, 2);
lean_inc(v_u_1226_);
v_ringInst_1227_ = lean_ctor_get(v_ring_1221_, 3);
lean_inc_ref(v_ringInst_1227_);
lean_dec_ref(v_ring_1221_);
v_canonExpr_1228_ = lean_ctor_get(v_inst_1217_, 0);
v_synthInstance_x3f_1229_ = lean_ctor_get(v_inst_1217_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_inst_1217_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1231_ = v_inst_1217_;
v_isShared_1232_ = v_isSharedCheck_1250_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_synthInstance_x3f_1229_);
lean_inc(v_canonExpr_1228_);
lean_dec(v_inst_1217_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1250_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1233_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_1234_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_1235_ = lean_box(0);
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 1);
lean_ctor_set(v___x_1231_, 1, v___x_1235_);
lean_ctor_set(v___x_1231_, 0, v_u_1226_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_u_1226_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v_inst_x27_1239_; lean_object* v___x_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_instType_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_inc_ref_n(v___x_1237_, 2);
v___x_1238_ = l_Lean_mkConst(v___x_1234_, v___x_1237_);
lean_inc_ref_n(v_type_1225_, 2);
v_inst_x27_1239_ = l_Lean_mkAppB(v___x_1238_, v_type_1225_, v_ringInst_1227_);
v___x_1240_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_1218_, 2);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1241_, 0, v___x_1240_);
lean_closure_set(v___f_1241_, 1, v___x_1233_);
lean_closure_set(v___f_1241_, 2, v___x_1237_);
lean_closure_set(v___f_1241_, 3, v_type_1225_);
lean_closure_set(v___f_1241_, 4, v_canonExpr_1228_);
lean_closure_set(v___f_1241_, 5, v_toBind_1218_);
lean_closure_set(v___f_1241_, 6, v___f_1219_);
v___f_1242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1242_, 0, v___f_1241_);
lean_inc_ref(v___f_1242_);
v___f_1243_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_1243_, 0, v_toPure_1216_);
lean_closure_set(v___f_1243_, 1, v_inst_x27_1239_);
lean_closure_set(v___f_1243_, 2, v_toBind_1218_);
lean_closure_set(v___f_1243_, 3, v___f_1242_);
lean_closure_set(v___f_1243_, 4, v___f_1242_);
lean_closure_set(v___f_1243_, 5, v_inst_1220_);
v___x_1244_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_1245_ = l_Lean_mkConst(v___x_1244_, v___x_1237_);
v_instType_1246_ = l_Lean_Expr_app___override(v___x_1245_, v_type_1225_);
v___x_1247_ = lean_apply_1(v_synthInstance_x3f_1229_, v_instType_1246_);
v___x_1248_ = lean_apply_4(v_toBind_1218_, lean_box(0), lean_box(0), v___x_1247_, v___f_1243_);
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_){
_start:
{
lean_object* v_toApplicative_1255_; lean_object* v_toBind_1256_; lean_object* v_getRing_1257_; lean_object* v_modifyRing_1258_; lean_object* v_toPure_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; 
v_toApplicative_1255_ = lean_ctor_get(v_inst_1252_, 0);
lean_inc_ref(v_toApplicative_1255_);
v_toBind_1256_ = lean_ctor_get(v_inst_1252_, 1);
lean_inc_n(v_toBind_1256_, 3);
lean_dec_ref(v_inst_1252_);
v_getRing_1257_ = lean_ctor_get(v_inst_1254_, 0);
lean_inc(v_getRing_1257_);
v_modifyRing_1258_ = lean_ctor_get(v_inst_1254_, 1);
lean_inc(v_modifyRing_1258_);
lean_dec_ref(v_inst_1254_);
v_toPure_1259_ = lean_ctor_get(v_toApplicative_1255_, 1);
lean_inc_n(v_toPure_1259_, 2);
lean_dec_ref(v_toApplicative_1255_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1260_, 0, v_toPure_1259_);
lean_closure_set(v___f_1260_, 1, v_modifyRing_1258_);
lean_closure_set(v___f_1260_, 2, v_toBind_1256_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_1261_, 0, v_toPure_1259_);
lean_closure_set(v___f_1261_, 1, v_inst_1253_);
lean_closure_set(v___f_1261_, 2, v_toBind_1256_);
lean_closure_set(v___f_1261_, 3, v___f_1260_);
lean_closure_set(v___f_1261_, 4, v_inst_1251_);
v___x_1262_ = lean_apply_4(v_toBind_1256_, lean_box(0), lean_box(0), v_getRing_1257_, v___f_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_1264_, v_inst_1265_, v_inst_1266_, v_inst_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_1269_, lean_object* v_s_1270_){
_start:
{
lean_object* v_id_1271_; lean_object* v_type_1272_; lean_object* v_u_1273_; lean_object* v_ringInst_1274_; lean_object* v_semiringInst_1275_; lean_object* v_charInst_x3f_1276_; uint8_t v_symbolicChar_1277_; lean_object* v_addFn_x3f_1278_; lean_object* v_mulFn_x3f_1279_; lean_object* v_subFn_x3f_1280_; lean_object* v_negFn_x3f_1281_; lean_object* v_powFn_x3f_1282_; lean_object* v_intCastFn_x3f_1283_; lean_object* v_natSMulFn_x3f_1284_; lean_object* v_intSMulFn_x3f_1285_; lean_object* v_one_x3f_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1294_; 
v_id_1271_ = lean_ctor_get(v_s_1270_, 0);
v_type_1272_ = lean_ctor_get(v_s_1270_, 1);
v_u_1273_ = lean_ctor_get(v_s_1270_, 2);
v_ringInst_1274_ = lean_ctor_get(v_s_1270_, 3);
v_semiringInst_1275_ = lean_ctor_get(v_s_1270_, 4);
v_charInst_x3f_1276_ = lean_ctor_get(v_s_1270_, 5);
v_symbolicChar_1277_ = lean_ctor_get_uint8(v_s_1270_, sizeof(void*)*16);
v_addFn_x3f_1278_ = lean_ctor_get(v_s_1270_, 6);
v_mulFn_x3f_1279_ = lean_ctor_get(v_s_1270_, 7);
v_subFn_x3f_1280_ = lean_ctor_get(v_s_1270_, 8);
v_negFn_x3f_1281_ = lean_ctor_get(v_s_1270_, 9);
v_powFn_x3f_1282_ = lean_ctor_get(v_s_1270_, 10);
v_intCastFn_x3f_1283_ = lean_ctor_get(v_s_1270_, 11);
v_natSMulFn_x3f_1284_ = lean_ctor_get(v_s_1270_, 13);
v_intSMulFn_x3f_1285_ = lean_ctor_get(v_s_1270_, 14);
v_one_x3f_1286_ = lean_ctor_get(v_s_1270_, 15);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_s_1270_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_s_1270_, 12);
lean_dec(v_unused_1295_);
v___x_1288_ = v_s_1270_;
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_one_x3f_1286_);
lean_inc(v_intSMulFn_x3f_1285_);
lean_inc(v_natSMulFn_x3f_1284_);
lean_inc(v_intCastFn_x3f_1283_);
lean_inc(v_powFn_x3f_1282_);
lean_inc(v_negFn_x3f_1281_);
lean_inc(v_subFn_x3f_1280_);
lean_inc(v_mulFn_x3f_1279_);
lean_inc(v_addFn_x3f_1278_);
lean_inc(v_charInst_x3f_1276_);
lean_inc(v_semiringInst_1275_);
lean_inc(v_ringInst_1274_);
lean_inc(v_u_1273_);
lean_inc(v_type_1272_);
lean_inc(v_id_1271_);
lean_dec(v_s_1270_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_natCastFn_1269_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 12, v___x_1290_);
v___x_1292_ = v___x_1288_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_id_1271_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_type_1272_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_u_1273_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_ringInst_1274_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_semiringInst_1275_);
lean_ctor_set(v_reuseFailAlloc_1293_, 5, v_charInst_x3f_1276_);
lean_ctor_set(v_reuseFailAlloc_1293_, 6, v_addFn_x3f_1278_);
lean_ctor_set(v_reuseFailAlloc_1293_, 7, v_mulFn_x3f_1279_);
lean_ctor_set(v_reuseFailAlloc_1293_, 8, v_subFn_x3f_1280_);
lean_ctor_set(v_reuseFailAlloc_1293_, 9, v_negFn_x3f_1281_);
lean_ctor_set(v_reuseFailAlloc_1293_, 10, v_powFn_x3f_1282_);
lean_ctor_set(v_reuseFailAlloc_1293_, 11, v_intCastFn_x3f_1283_);
lean_ctor_set(v_reuseFailAlloc_1293_, 12, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1293_, 13, v_natSMulFn_x3f_1284_);
lean_ctor_set(v_reuseFailAlloc_1293_, 14, v_intSMulFn_x3f_1285_);
lean_ctor_set(v_reuseFailAlloc_1293_, 15, v_one_x3f_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*16, v_symbolicChar_1277_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1296_, lean_object* v_natCastFn_1297_, lean_object* v_____r_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_apply_2(v_toPure_1296_, lean_box(0), v_natCastFn_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1300_, lean_object* v_modifyRing_1301_, lean_object* v_toBind_1302_, lean_object* v_natCastFn_1303_){
_start:
{
lean_object* v___f_1304_; lean_object* v___f_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_inc_ref(v_natCastFn_1303_);
v___f_1304_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1304_, 0, v_natCastFn_1303_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1305_, 0, v_toPure_1300_);
lean_closure_set(v___f_1305_, 1, v_natCastFn_1303_);
v___x_1306_ = lean_apply_1(v_modifyRing_1301_, v___f_1304_);
v___x_1307_ = lean_apply_4(v_toBind_1302_, lean_box(0), lean_box(0), v___x_1306_, v___f_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_toBind_1312_, lean_object* v___f_1313_, lean_object* v_ring_1314_){
_start:
{
lean_object* v_natCastFn_x3f_1315_; 
v_natCastFn_x3f_1315_ = lean_ctor_get(v_ring_1314_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1315_) == 1)
{
lean_object* v_val_1316_; lean_object* v___x_1317_; 
lean_inc_ref(v_natCastFn_x3f_1315_);
lean_dec_ref(v_ring_1314_);
lean_dec(v___f_1313_);
lean_dec(v_toBind_1312_);
lean_dec_ref(v_inst_1311_);
lean_dec_ref(v_inst_1310_);
lean_dec(v_inst_1309_);
v_val_1316_ = lean_ctor_get(v_natCastFn_x3f_1315_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v_natCastFn_x3f_1315_, 1);
v___x_1317_ = lean_apply_2(v_toPure_1308_, lean_box(0), v_val_1316_);
return v___x_1317_;
}
else
{
lean_object* v_type_1318_; lean_object* v_u_1319_; lean_object* v_semiringInst_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_toPure_1308_);
v_type_1318_ = lean_ctor_get(v_ring_1314_, 1);
lean_inc_ref(v_type_1318_);
v_u_1319_ = lean_ctor_get(v_ring_1314_, 2);
lean_inc(v_u_1319_);
v_semiringInst_1320_ = lean_ctor_get(v_ring_1314_, 4);
lean_inc_ref(v_semiringInst_1320_);
lean_dec_ref(v_ring_1314_);
v___x_1321_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1309_, v_inst_1310_, v_inst_1311_, v_u_1319_, v_type_1318_, v_semiringInst_1320_);
v___x_1322_ = lean_apply_4(v_toBind_1312_, lean_box(0), lean_box(0), v___x_1321_, v___f_1313_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_){
_start:
{
lean_object* v_toApplicative_1327_; lean_object* v_toBind_1328_; lean_object* v_getRing_1329_; lean_object* v_modifyRing_1330_; lean_object* v_toPure_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; 
v_toApplicative_1327_ = lean_ctor_get(v_inst_1324_, 0);
v_toBind_1328_ = lean_ctor_get(v_inst_1324_, 1);
lean_inc_n(v_toBind_1328_, 3);
v_getRing_1329_ = lean_ctor_get(v_inst_1326_, 0);
lean_inc(v_getRing_1329_);
v_modifyRing_1330_ = lean_ctor_get(v_inst_1326_, 1);
lean_inc(v_modifyRing_1330_);
lean_dec_ref(v_inst_1326_);
v_toPure_1331_ = lean_ctor_get(v_toApplicative_1327_, 1);
lean_inc_n(v_toPure_1331_, 2);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1332_, 0, v_toPure_1331_);
lean_closure_set(v___f_1332_, 1, v_modifyRing_1330_);
lean_closure_set(v___f_1332_, 2, v_toBind_1328_);
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1333_, 0, v_toPure_1331_);
lean_closure_set(v___f_1333_, 1, v_inst_1323_);
lean_closure_set(v___f_1333_, 2, v_inst_1324_);
lean_closure_set(v___f_1333_, 3, v_inst_1325_);
lean_closure_set(v___f_1333_, 4, v_toBind_1328_);
lean_closure_set(v___f_1333_, 5, v___f_1332_);
v___x_1334_ = lean_apply_4(v_toBind_1328_, lean_box(0), lean_box(0), v_getRing_1329_, v___f_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1341_, lean_object* v_s_1342_){
_start:
{
lean_object* v_toRing_1343_; lean_object* v_divFn_x3f_1344_; lean_object* v_semiringId_x3f_1345_; lean_object* v_commSemiringInst_1346_; lean_object* v_commRingInst_1347_; lean_object* v_noZeroDivInst_x3f_1348_; lean_object* v_fieldInst_x3f_1349_; lean_object* v_powIdentityInst_x3f_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1358_; 
v_toRing_1343_ = lean_ctor_get(v_s_1342_, 0);
v_divFn_x3f_1344_ = lean_ctor_get(v_s_1342_, 2);
v_semiringId_x3f_1345_ = lean_ctor_get(v_s_1342_, 3);
v_commSemiringInst_1346_ = lean_ctor_get(v_s_1342_, 4);
v_commRingInst_1347_ = lean_ctor_get(v_s_1342_, 5);
v_noZeroDivInst_x3f_1348_ = lean_ctor_get(v_s_1342_, 6);
v_fieldInst_x3f_1349_ = lean_ctor_get(v_s_1342_, 7);
v_powIdentityInst_x3f_1350_ = lean_ctor_get(v_s_1342_, 8);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_s_1342_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v_s_1342_, 1);
lean_dec(v_unused_1359_);
v___x_1352_ = v_s_1342_;
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1350_);
lean_inc(v_fieldInst_x3f_1349_);
lean_inc(v_noZeroDivInst_x3f_1348_);
lean_inc(v_commRingInst_1347_);
lean_inc(v_commSemiringInst_1346_);
lean_inc(v_semiringId_x3f_1345_);
lean_inc(v_divFn_x3f_1344_);
lean_inc(v_toRing_1343_);
lean_dec(v_s_1342_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_invFn_1341_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v___x_1354_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_toRing_1343_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_divFn_x3f_1344_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_semiringId_x3f_1345_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_commSemiringInst_1346_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_commRingInst_1347_);
lean_ctor_set(v_reuseFailAlloc_1357_, 6, v_noZeroDivInst_x3f_1348_);
lean_ctor_set(v_reuseFailAlloc_1357_, 7, v_fieldInst_x3f_1349_);
lean_ctor_set(v_reuseFailAlloc_1357_, 8, v_powIdentityInst_x3f_1350_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1360_, lean_object* v_invFn_1361_, lean_object* v_____r_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_apply_2(v_toPure_1360_, lean_box(0), v_invFn_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1364_, lean_object* v_modifyCommRing_1365_, lean_object* v_toBind_1366_, lean_object* v_invFn_1367_){
_start:
{
lean_object* v___f_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_inc_ref(v_invFn_1367_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1368_, 0, v_invFn_1367_);
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1369_, 0, v_toPure_1364_);
lean_closure_set(v___f_1369_, 1, v_invFn_1367_);
v___x_1370_ = lean_apply_1(v_modifyCommRing_1365_, v___f_1368_);
v___x_1371_ = lean_apply_4(v_toBind_1366_, lean_box(0), lean_box(0), v___x_1370_, v___f_1369_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1388_ = l_Lean_stringToMessageData(v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_toBind_1394_, lean_object* v___f_1395_, lean_object* v_ring_1396_){
_start:
{
lean_object* v_fieldInst_x3f_1397_; 
v_fieldInst_x3f_1397_ = lean_ctor_get(v_ring_1396_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1397_) == 1)
{
lean_object* v_invFn_x3f_1398_; 
lean_inc_ref(v_fieldInst_x3f_1397_);
v_invFn_x3f_1398_ = lean_ctor_get(v_ring_1396_, 1);
if (lean_obj_tag(v_invFn_x3f_1398_) == 1)
{
lean_object* v_val_1399_; lean_object* v___x_1400_; 
lean_inc_ref(v_invFn_x3f_1398_);
lean_dec_ref_known(v_fieldInst_x3f_1397_, 1);
lean_dec_ref(v_ring_1396_);
lean_dec(v___f_1395_);
lean_dec(v_toBind_1394_);
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
lean_dec_ref(v_inst_1391_);
lean_dec(v_inst_1390_);
v_val_1399_ = lean_ctor_get(v_invFn_x3f_1398_, 0);
lean_inc(v_val_1399_);
lean_dec_ref_known(v_invFn_x3f_1398_, 1);
v___x_1400_ = lean_apply_2(v_toPure_1389_, lean_box(0), v_val_1399_);
return v___x_1400_;
}
else
{
lean_object* v_toRing_1401_; lean_object* v_val_1402_; lean_object* v_type_1403_; lean_object* v_u_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_expectedInst_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec(v_toPure_1389_);
v_toRing_1401_ = lean_ctor_get(v_ring_1396_, 0);
lean_inc_ref(v_toRing_1401_);
lean_dec_ref(v_ring_1396_);
v_val_1402_ = lean_ctor_get(v_fieldInst_x3f_1397_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v_fieldInst_x3f_1397_, 1);
v_type_1403_ = lean_ctor_get(v_toRing_1401_, 1);
lean_inc_ref_n(v_type_1403_, 2);
v_u_1404_ = lean_ctor_get(v_toRing_1401_, 2);
lean_inc_n(v_u_1404_, 2);
lean_dec_ref(v_toRing_1401_);
v___x_1405_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1406_ = lean_box(0);
v___x_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_u_1404_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Lean_mkConst(v___x_1405_, v___x_1407_);
v_expectedInst_1409_ = l_Lean_mkAppB(v___x_1408_, v_type_1403_, v_val_1402_);
v___x_1410_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1411_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1412_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1390_, v_inst_1391_, v_inst_1392_, v_inst_1393_, v_type_1403_, v_u_1404_, v___x_1410_, v___x_1411_, v_expectedInst_1409_);
v___x_1413_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v___x_1412_, v___f_1395_);
return v___x_1413_;
}
}
else
{
lean_object* v_toRing_1414_; lean_object* v_type_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec(v___f_1395_);
lean_dec(v_toBind_1394_);
lean_dec_ref(v_inst_1393_);
lean_dec(v_inst_1390_);
lean_dec(v_toPure_1389_);
v_toRing_1414_ = lean_ctor_get(v_ring_1396_, 0);
lean_inc_ref(v_toRing_1414_);
lean_dec_ref(v_ring_1396_);
v_type_1415_ = lean_ctor_get(v_toRing_1414_, 1);
lean_inc_ref(v_type_1415_);
lean_dec_ref(v_toRing_1414_);
v___x_1416_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1417_ = l_Lean_indentExpr(v_type_1415_);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = l_Lean_throwError___redArg(v_inst_1392_, v_inst_1391_, v___x_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_){
_start:
{
lean_object* v_toApplicative_1425_; lean_object* v_toBind_1426_; lean_object* v_getCommRing_1427_; lean_object* v_modifyCommRing_1428_; lean_object* v_toPure_1429_; lean_object* v___f_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; 
v_toApplicative_1425_ = lean_ctor_get(v_inst_1422_, 0);
v_toBind_1426_ = lean_ctor_get(v_inst_1422_, 1);
lean_inc_n(v_toBind_1426_, 3);
v_getCommRing_1427_ = lean_ctor_get(v_inst_1424_, 0);
lean_inc(v_getCommRing_1427_);
v_modifyCommRing_1428_ = lean_ctor_get(v_inst_1424_, 1);
lean_inc(v_modifyCommRing_1428_);
lean_dec_ref(v_inst_1424_);
v_toPure_1429_ = lean_ctor_get(v_toApplicative_1425_, 1);
lean_inc_n(v_toPure_1429_, 2);
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1430_, 0, v_toPure_1429_);
lean_closure_set(v___f_1430_, 1, v_modifyCommRing_1428_);
lean_closure_set(v___f_1430_, 2, v_toBind_1426_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1431_, 0, v_toPure_1429_);
lean_closure_set(v___f_1431_, 1, v_inst_1420_);
lean_closure_set(v___f_1431_, 2, v_inst_1421_);
lean_closure_set(v___f_1431_, 3, v_inst_1422_);
lean_closure_set(v___f_1431_, 4, v_inst_1423_);
lean_closure_set(v___f_1431_, 5, v_toBind_1426_);
lean_closure_set(v___f_1431_, 6, v___f_1430_);
v___x_1432_ = lean_apply_4(v_toBind_1426_, lean_box(0), lean_box(0), v_getCommRing_1427_, v___f_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1434_, v_inst_1435_, v_inst_1436_, v_inst_1437_, v_inst_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0(lean_object* v_divFn_1440_, lean_object* v_s_1441_){
_start:
{
lean_object* v_toRing_1442_; lean_object* v_invFn_x3f_1443_; lean_object* v_semiringId_x3f_1444_; lean_object* v_commSemiringInst_1445_; lean_object* v_commRingInst_1446_; lean_object* v_noZeroDivInst_x3f_1447_; lean_object* v_fieldInst_x3f_1448_; lean_object* v_powIdentityInst_x3f_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1457_; 
v_toRing_1442_ = lean_ctor_get(v_s_1441_, 0);
v_invFn_x3f_1443_ = lean_ctor_get(v_s_1441_, 1);
v_semiringId_x3f_1444_ = lean_ctor_get(v_s_1441_, 3);
v_commSemiringInst_1445_ = lean_ctor_get(v_s_1441_, 4);
v_commRingInst_1446_ = lean_ctor_get(v_s_1441_, 5);
v_noZeroDivInst_x3f_1447_ = lean_ctor_get(v_s_1441_, 6);
v_fieldInst_x3f_1448_ = lean_ctor_get(v_s_1441_, 7);
v_powIdentityInst_x3f_1449_ = lean_ctor_get(v_s_1441_, 8);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_s_1441_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_s_1441_, 2);
lean_dec(v_unused_1458_);
v___x_1451_ = v_s_1441_;
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1449_);
lean_inc(v_fieldInst_x3f_1448_);
lean_inc(v_noZeroDivInst_x3f_1447_);
lean_inc(v_commRingInst_1446_);
lean_inc(v_commSemiringInst_1445_);
lean_inc(v_semiringId_x3f_1444_);
lean_inc(v_invFn_x3f_1443_);
lean_inc(v_toRing_1442_);
lean_dec(v_s_1441_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v_divFn_1440_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 2, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_toRing_1442_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_invFn_x3f_1443_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_semiringId_x3f_1444_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_commSemiringInst_1445_);
lean_ctor_set(v_reuseFailAlloc_1456_, 5, v_commRingInst_1446_);
lean_ctor_set(v_reuseFailAlloc_1456_, 6, v_noZeroDivInst_x3f_1447_);
lean_ctor_set(v_reuseFailAlloc_1456_, 7, v_fieldInst_x3f_1448_);
lean_ctor_set(v_reuseFailAlloc_1456_, 8, v_powIdentityInst_x3f_1449_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1(lean_object* v_toPure_1459_, lean_object* v_divFn_1460_, lean_object* v_____r_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_apply_2(v_toPure_1459_, lean_box(0), v_divFn_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2(lean_object* v_toPure_1463_, lean_object* v_modifyCommRing_1464_, lean_object* v_toBind_1465_, lean_object* v_divFn_1466_){
_start:
{
lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_inc_ref(v_divFn_1466_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1467_, 0, v_divFn_1466_);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1468_, 0, v_toPure_1463_);
lean_closure_set(v___f_1468_, 1, v_divFn_1466_);
v___x_1469_ = lean_apply_1(v_modifyCommRing_1464_, v___f_1467_);
v___x_1470_ = lean_apply_4(v_toBind_1465_, lean_box(0), lean_box(0), v___x_1469_, v___f_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3(lean_object* v_toPure_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_toBind_1492_, lean_object* v___f_1493_, lean_object* v_ring_1494_){
_start:
{
lean_object* v_fieldInst_x3f_1495_; 
v_fieldInst_x3f_1495_ = lean_ctor_get(v_ring_1494_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1495_) == 1)
{
lean_object* v_divFn_x3f_1496_; 
lean_inc_ref(v_fieldInst_x3f_1495_);
v_divFn_x3f_1496_ = lean_ctor_get(v_ring_1494_, 2);
if (lean_obj_tag(v_divFn_x3f_1496_) == 1)
{
lean_object* v_val_1497_; lean_object* v___x_1498_; 
lean_inc_ref(v_divFn_x3f_1496_);
lean_dec_ref_known(v_fieldInst_x3f_1495_, 1);
lean_dec_ref(v_ring_1494_);
lean_dec(v___f_1493_);
lean_dec(v_toBind_1492_);
lean_dec_ref(v_inst_1491_);
lean_dec_ref(v_inst_1490_);
lean_dec_ref(v_inst_1489_);
lean_dec(v_inst_1488_);
v_val_1497_ = lean_ctor_get(v_divFn_x3f_1496_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v_divFn_x3f_1496_, 1);
v___x_1498_ = lean_apply_2(v_toPure_1487_, lean_box(0), v_val_1497_);
return v___x_1498_;
}
else
{
lean_object* v_toRing_1499_; lean_object* v_val_1500_; lean_object* v_type_1501_; lean_object* v_u_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_expectedInst_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_toPure_1487_);
v_toRing_1499_ = lean_ctor_get(v_ring_1494_, 0);
lean_inc_ref(v_toRing_1499_);
lean_dec_ref(v_ring_1494_);
v_val_1500_ = lean_ctor_get(v_fieldInst_x3f_1495_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v_fieldInst_x3f_1495_, 1);
v_type_1501_ = lean_ctor_get(v_toRing_1499_, 1);
lean_inc_ref_n(v_type_1501_, 3);
v_u_1502_ = lean_ctor_get(v_toRing_1499_, 2);
lean_inc_n(v_u_1502_, 2);
lean_dec_ref(v_toRing_1499_);
v___x_1503_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1));
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_u_1502_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
lean_inc_ref(v___x_1505_);
v___x_1506_ = l_Lean_mkConst(v___x_1503_, v___x_1505_);
v___x_1507_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3));
v___x_1508_ = l_Lean_mkConst(v___x_1507_, v___x_1505_);
v___x_1509_ = l_Lean_mkAppB(v___x_1508_, v_type_1501_, v_val_1500_);
v_expectedInst_1510_ = l_Lean_mkAppB(v___x_1506_, v_type_1501_, v___x_1509_);
v___x_1511_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5));
v___x_1512_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7));
v___x_1513_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1488_, v_inst_1489_, v_inst_1490_, v_inst_1491_, v_type_1501_, v_u_1502_, v___x_1511_, v___x_1512_, v_expectedInst_1510_);
v___x_1514_ = lean_apply_4(v_toBind_1492_, lean_box(0), lean_box(0), v___x_1513_, v___f_1493_);
return v___x_1514_;
}
}
else
{
lean_object* v_toRing_1515_; lean_object* v_type_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec(v___f_1493_);
lean_dec(v_toBind_1492_);
lean_dec_ref(v_inst_1491_);
lean_dec(v_inst_1488_);
lean_dec(v_toPure_1487_);
v_toRing_1515_ = lean_ctor_get(v_ring_1494_, 0);
lean_inc_ref(v_toRing_1515_);
lean_dec_ref(v_ring_1494_);
v_type_1516_ = lean_ctor_get(v_toRing_1515_, 1);
lean_inc_ref(v_type_1516_);
lean_dec_ref(v_toRing_1515_);
v___x_1517_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1518_ = l_Lean_indentExpr(v_type_1516_);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_throwError___redArg(v_inst_1490_, v_inst_1489_, v___x_1519_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg(lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_){
_start:
{
lean_object* v_toApplicative_1526_; lean_object* v_toBind_1527_; lean_object* v_getCommRing_1528_; lean_object* v_modifyCommRing_1529_; lean_object* v_toPure_1530_; lean_object* v___f_1531_; lean_object* v___f_1532_; lean_object* v___x_1533_; 
v_toApplicative_1526_ = lean_ctor_get(v_inst_1523_, 0);
v_toBind_1527_ = lean_ctor_get(v_inst_1523_, 1);
lean_inc_n(v_toBind_1527_, 3);
v_getCommRing_1528_ = lean_ctor_get(v_inst_1525_, 0);
lean_inc(v_getCommRing_1528_);
v_modifyCommRing_1529_ = lean_ctor_get(v_inst_1525_, 1);
lean_inc(v_modifyCommRing_1529_);
lean_dec_ref(v_inst_1525_);
v_toPure_1530_ = lean_ctor_get(v_toApplicative_1526_, 1);
lean_inc_n(v_toPure_1530_, 2);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1531_, 0, v_toPure_1530_);
lean_closure_set(v___f_1531_, 1, v_modifyCommRing_1529_);
lean_closure_set(v___f_1531_, 2, v_toBind_1527_);
v___f_1532_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1532_, 0, v_toPure_1530_);
lean_closure_set(v___f_1532_, 1, v_inst_1521_);
lean_closure_set(v___f_1532_, 2, v_inst_1522_);
lean_closure_set(v___f_1532_, 3, v_inst_1523_);
lean_closure_set(v___f_1532_, 4, v_inst_1524_);
lean_closure_set(v___f_1532_, 5, v_toBind_1527_);
lean_closure_set(v___f_1532_, 6, v___f_1531_);
v___x_1533_ = lean_apply_4(v_toBind_1527_, lean_box(0), lean_box(0), v_getCommRing_1528_, v___f_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn(lean_object* v_m_1534_, lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Meta_Sym_Arith_getDivFn___redArg(v_inst_1535_, v_inst_1536_, v_inst_1537_, v_inst_1538_, v_inst_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0(lean_object* v_fn_1541_, lean_object* v_s_1542_){
_start:
{
lean_object* v_id_1543_; lean_object* v_type_1544_; lean_object* v_u_1545_; lean_object* v_semiringInst_1546_; lean_object* v_charInst_x3f_1547_; uint8_t v_symbolicChar_1548_; lean_object* v_addFn_x3f_1549_; lean_object* v_mulFn_x3f_1550_; lean_object* v_powFn_x3f_1551_; lean_object* v_natCastFn_x3f_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
v_id_1543_ = lean_ctor_get(v_s_1542_, 0);
v_type_1544_ = lean_ctor_get(v_s_1542_, 1);
v_u_1545_ = lean_ctor_get(v_s_1542_, 2);
v_semiringInst_1546_ = lean_ctor_get(v_s_1542_, 3);
v_charInst_x3f_1547_ = lean_ctor_get(v_s_1542_, 4);
v_symbolicChar_1548_ = lean_ctor_get_uint8(v_s_1542_, sizeof(void*)*10);
v_addFn_x3f_1549_ = lean_ctor_get(v_s_1542_, 5);
v_mulFn_x3f_1550_ = lean_ctor_get(v_s_1542_, 6);
v_powFn_x3f_1551_ = lean_ctor_get(v_s_1542_, 7);
v_natCastFn_x3f_1552_ = lean_ctor_get(v_s_1542_, 8);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_s_1542_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_s_1542_, 9);
lean_dec(v_unused_1561_);
v___x_1554_ = v_s_1542_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_natCastFn_x3f_1552_);
lean_inc(v_powFn_x3f_1551_);
lean_inc(v_mulFn_x3f_1550_);
lean_inc(v_addFn_x3f_1549_);
lean_inc(v_charInst_x3f_1547_);
lean_inc(v_semiringInst_1546_);
lean_inc(v_u_1545_);
lean_inc(v_type_1544_);
lean_inc(v_id_1543_);
lean_dec(v_s_1542_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_fn_1541_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 9, v___x_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_id_1543_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_type_1544_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_u_1545_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_semiringInst_1546_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_charInst_x3f_1547_);
lean_ctor_set(v_reuseFailAlloc_1559_, 5, v_addFn_x3f_1549_);
lean_ctor_set(v_reuseFailAlloc_1559_, 6, v_mulFn_x3f_1550_);
lean_ctor_set(v_reuseFailAlloc_1559_, 7, v_powFn_x3f_1551_);
lean_ctor_set(v_reuseFailAlloc_1559_, 8, v_natCastFn_x3f_1552_);
lean_ctor_set(v_reuseFailAlloc_1559_, 9, v___x_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, sizeof(void*)*10, v_symbolicChar_1548_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2(lean_object* v_toPure_1562_, lean_object* v_modifySemiring_1563_, lean_object* v_toBind_1564_, lean_object* v_fn_1565_){
_start:
{
lean_object* v___f_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_inc_ref(v_fn_1565_);
v___f_1566_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1566_, 0, v_fn_1565_);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1567_, 0, v_toPure_1562_);
lean_closure_set(v___f_1567_, 1, v_fn_1565_);
v___x_1568_ = lean_apply_1(v_modifySemiring_1563_, v___f_1566_);
v___x_1569_ = lean_apply_4(v_toBind_1564_, lean_box(0), lean_box(0), v___x_1568_, v___f_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1(lean_object* v_toPure_1570_, lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_inst_1573_, lean_object* v_toBind_1574_, lean_object* v___f_1575_, lean_object* v_sr_1576_){
_start:
{
lean_object* v_natSMulFn_x3f_1577_; 
v_natSMulFn_x3f_1577_ = lean_ctor_get(v_sr_1576_, 9);
if (lean_obj_tag(v_natSMulFn_x3f_1577_) == 1)
{
lean_object* v_val_1578_; lean_object* v___x_1579_; 
lean_inc_ref(v_natSMulFn_x3f_1577_);
lean_dec_ref(v_sr_1576_);
lean_dec(v___f_1575_);
lean_dec(v_toBind_1574_);
lean_dec_ref(v_inst_1573_);
lean_dec_ref(v_inst_1572_);
lean_dec(v_inst_1571_);
v_val_1578_ = lean_ctor_get(v_natSMulFn_x3f_1577_, 0);
lean_inc(v_val_1578_);
lean_dec_ref_known(v_natSMulFn_x3f_1577_, 1);
v___x_1579_ = lean_apply_2(v_toPure_1570_, lean_box(0), v_val_1578_);
return v___x_1579_;
}
else
{
lean_object* v_type_1580_; lean_object* v_u_1581_; lean_object* v_semiringInst_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_toPure_1570_);
v_type_1580_ = lean_ctor_get(v_sr_1576_, 1);
lean_inc_ref_n(v_type_1580_, 2);
v_u_1581_ = lean_ctor_get(v_sr_1576_, 2);
lean_inc_n(v_u_1581_, 2);
v_semiringInst_1582_ = lean_ctor_get(v_sr_1576_, 3);
lean_inc_ref(v_semiringInst_1582_);
lean_dec_ref(v_sr_1576_);
v___x_1583_ = l_Lean_Nat_mkType;
v___x_1584_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_u_1581_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_mkConst(v___x_1584_, v___x_1586_);
v___x_1588_ = l_Lean_mkAppB(v___x_1587_, v_type_1580_, v_semiringInst_1582_);
v___x_1589_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_1571_, v_inst_1572_, v_inst_1573_, v_u_1581_, v_type_1580_, v___x_1583_, v___x_1588_);
v___x_1590_ = lean_apply_4(v_toBind_1574_, lean_box(0), lean_box(0), v___x_1589_, v___f_1575_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_){
_start:
{
lean_object* v_toApplicative_1595_; lean_object* v_toBind_1596_; lean_object* v_getSemiring_1597_; lean_object* v_modifySemiring_1598_; lean_object* v_toPure_1599_; lean_object* v___f_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; 
v_toApplicative_1595_ = lean_ctor_get(v_inst_1592_, 0);
v_toBind_1596_ = lean_ctor_get(v_inst_1592_, 1);
lean_inc_n(v_toBind_1596_, 3);
v_getSemiring_1597_ = lean_ctor_get(v_inst_1594_, 0);
lean_inc(v_getSemiring_1597_);
v_modifySemiring_1598_ = lean_ctor_get(v_inst_1594_, 1);
lean_inc(v_modifySemiring_1598_);
lean_dec_ref(v_inst_1594_);
v_toPure_1599_ = lean_ctor_get(v_toApplicative_1595_, 1);
lean_inc_n(v_toPure_1599_, 2);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1600_, 0, v_toPure_1599_);
lean_closure_set(v___f_1600_, 1, v_modifySemiring_1598_);
lean_closure_set(v___f_1600_, 2, v_toBind_1596_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1601_, 0, v_toPure_1599_);
lean_closure_set(v___f_1601_, 1, v_inst_1591_);
lean_closure_set(v___f_1601_, 2, v_inst_1592_);
lean_closure_set(v___f_1601_, 3, v_inst_1593_);
lean_closure_set(v___f_1601_, 4, v_toBind_1596_);
lean_closure_set(v___f_1601_, 5, v___f_1600_);
v___x_1602_ = lean_apply_4(v_toBind_1596_, lean_box(0), lean_box(0), v_getSemiring_1597_, v___f_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27(lean_object* v_m_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(v_inst_1604_, v_inst_1605_, v_inst_1606_, v_inst_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_1609_, lean_object* v_s_1610_){
_start:
{
lean_object* v_id_1611_; lean_object* v_type_1612_; lean_object* v_u_1613_; lean_object* v_semiringInst_1614_; lean_object* v_charInst_x3f_1615_; uint8_t v_symbolicChar_1616_; lean_object* v_mulFn_x3f_1617_; lean_object* v_powFn_x3f_1618_; lean_object* v_natCastFn_x3f_1619_; lean_object* v_natSMulFn_x3f_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1628_; 
v_id_1611_ = lean_ctor_get(v_s_1610_, 0);
v_type_1612_ = lean_ctor_get(v_s_1610_, 1);
v_u_1613_ = lean_ctor_get(v_s_1610_, 2);
v_semiringInst_1614_ = lean_ctor_get(v_s_1610_, 3);
v_charInst_x3f_1615_ = lean_ctor_get(v_s_1610_, 4);
v_symbolicChar_1616_ = lean_ctor_get_uint8(v_s_1610_, sizeof(void*)*10);
v_mulFn_x3f_1617_ = lean_ctor_get(v_s_1610_, 6);
v_powFn_x3f_1618_ = lean_ctor_get(v_s_1610_, 7);
v_natCastFn_x3f_1619_ = lean_ctor_get(v_s_1610_, 8);
v_natSMulFn_x3f_1620_ = lean_ctor_get(v_s_1610_, 9);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_s_1610_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v_s_1610_, 5);
lean_dec(v_unused_1629_);
v___x_1622_ = v_s_1610_;
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_natSMulFn_x3f_1620_);
lean_inc(v_natCastFn_x3f_1619_);
lean_inc(v_powFn_x3f_1618_);
lean_inc(v_mulFn_x3f_1617_);
lean_inc(v_charInst_x3f_1615_);
lean_inc(v_semiringInst_1614_);
lean_inc(v_u_1613_);
lean_inc(v_type_1612_);
lean_inc(v_id_1611_);
lean_dec(v_s_1610_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v_addFn_1609_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 5, v___x_1624_);
v___x_1626_ = v___x_1622_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_id_1611_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_type_1612_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_u_1613_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_semiringInst_1614_);
lean_ctor_set(v_reuseFailAlloc_1627_, 4, v_charInst_x3f_1615_);
lean_ctor_set(v_reuseFailAlloc_1627_, 5, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1627_, 6, v_mulFn_x3f_1617_);
lean_ctor_set(v_reuseFailAlloc_1627_, 7, v_powFn_x3f_1618_);
lean_ctor_set(v_reuseFailAlloc_1627_, 8, v_natCastFn_x3f_1619_);
lean_ctor_set(v_reuseFailAlloc_1627_, 9, v_natSMulFn_x3f_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*10, v_symbolicChar_1616_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_1630_, lean_object* v_modifySemiring_1631_, lean_object* v_toBind_1632_, lean_object* v_addFn_1633_){
_start:
{
lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_inc_ref(v_addFn_1633_);
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1634_, 0, v_addFn_1633_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1635_, 0, v_toPure_1630_);
lean_closure_set(v___f_1635_, 1, v_addFn_1633_);
v___x_1636_ = lean_apply_1(v_modifySemiring_1631_, v___f_1634_);
v___x_1637_ = lean_apply_4(v_toBind_1632_, lean_box(0), lean_box(0), v___x_1636_, v___f_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_toBind_1643_, lean_object* v___f_1644_, lean_object* v_sr_1645_){
_start:
{
lean_object* v_addFn_x3f_1646_; 
v_addFn_x3f_1646_ = lean_ctor_get(v_sr_1645_, 5);
if (lean_obj_tag(v_addFn_x3f_1646_) == 1)
{
lean_object* v_val_1647_; lean_object* v___x_1648_; 
lean_inc_ref(v_addFn_x3f_1646_);
lean_dec_ref(v_sr_1645_);
lean_dec(v___f_1644_);
lean_dec(v_toBind_1643_);
lean_dec_ref(v_inst_1642_);
lean_dec_ref(v_inst_1641_);
lean_dec_ref(v_inst_1640_);
lean_dec(v_inst_1639_);
v_val_1647_ = lean_ctor_get(v_addFn_x3f_1646_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v_addFn_x3f_1646_, 1);
v___x_1648_ = lean_apply_2(v_toPure_1638_, lean_box(0), v_val_1647_);
return v___x_1648_;
}
else
{
lean_object* v_type_1649_; lean_object* v_u_1650_; lean_object* v_semiringInst_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v_expectedInst_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec(v_toPure_1638_);
v_type_1649_ = lean_ctor_get(v_sr_1645_, 1);
lean_inc_ref_n(v_type_1649_, 3);
v_u_1650_ = lean_ctor_get(v_sr_1645_, 2);
lean_inc_n(v_u_1650_, 2);
v_semiringInst_1651_ = lean_ctor_get(v_sr_1645_, 3);
lean_inc_ref(v_semiringInst_1651_);
lean_dec_ref(v_sr_1645_);
v___x_1652_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_u_1650_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
lean_inc_ref(v___x_1654_);
v___x_1655_ = l_Lean_mkConst(v___x_1652_, v___x_1654_);
v___x_1656_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1657_ = l_Lean_mkConst(v___x_1656_, v___x_1654_);
v___x_1658_ = l_Lean_mkAppB(v___x_1657_, v_type_1649_, v_semiringInst_1651_);
v_expectedInst_1659_ = l_Lean_mkAppB(v___x_1655_, v_type_1649_, v___x_1658_);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1661_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1662_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1639_, v_inst_1640_, v_inst_1641_, v_inst_1642_, v_type_1649_, v_u_1650_, v___x_1660_, v___x_1661_, v_expectedInst_1659_);
v___x_1663_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1662_, v___f_1644_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_inst_1668_){
_start:
{
lean_object* v_toApplicative_1669_; lean_object* v_toBind_1670_; lean_object* v_getSemiring_1671_; lean_object* v_modifySemiring_1672_; lean_object* v_toPure_1673_; lean_object* v___f_1674_; lean_object* v___f_1675_; lean_object* v___x_1676_; 
v_toApplicative_1669_ = lean_ctor_get(v_inst_1666_, 0);
v_toBind_1670_ = lean_ctor_get(v_inst_1666_, 1);
lean_inc_n(v_toBind_1670_, 3);
v_getSemiring_1671_ = lean_ctor_get(v_inst_1668_, 0);
lean_inc(v_getSemiring_1671_);
v_modifySemiring_1672_ = lean_ctor_get(v_inst_1668_, 1);
lean_inc(v_modifySemiring_1672_);
lean_dec_ref(v_inst_1668_);
v_toPure_1673_ = lean_ctor_get(v_toApplicative_1669_, 1);
lean_inc_n(v_toPure_1673_, 2);
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1674_, 0, v_toPure_1673_);
lean_closure_set(v___f_1674_, 1, v_modifySemiring_1672_);
lean_closure_set(v___f_1674_, 2, v_toBind_1670_);
v___f_1675_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1675_, 0, v_toPure_1673_);
lean_closure_set(v___f_1675_, 1, v_inst_1664_);
lean_closure_set(v___f_1675_, 2, v_inst_1665_);
lean_closure_set(v___f_1675_, 3, v_inst_1666_);
lean_closure_set(v___f_1675_, 4, v_inst_1667_);
lean_closure_set(v___f_1675_, 5, v_toBind_1670_);
lean_closure_set(v___f_1675_, 6, v___f_1674_);
v___x_1676_ = lean_apply_4(v_toBind_1670_, lean_box(0), lean_box(0), v_getSemiring_1671_, v___f_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1678_, v_inst_1679_, v_inst_1680_, v_inst_1681_, v_inst_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_1684_, lean_object* v_s_1685_){
_start:
{
lean_object* v_id_1686_; lean_object* v_type_1687_; lean_object* v_u_1688_; lean_object* v_semiringInst_1689_; lean_object* v_charInst_x3f_1690_; uint8_t v_symbolicChar_1691_; lean_object* v_addFn_x3f_1692_; lean_object* v_powFn_x3f_1693_; lean_object* v_natCastFn_x3f_1694_; lean_object* v_natSMulFn_x3f_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1703_; 
v_id_1686_ = lean_ctor_get(v_s_1685_, 0);
v_type_1687_ = lean_ctor_get(v_s_1685_, 1);
v_u_1688_ = lean_ctor_get(v_s_1685_, 2);
v_semiringInst_1689_ = lean_ctor_get(v_s_1685_, 3);
v_charInst_x3f_1690_ = lean_ctor_get(v_s_1685_, 4);
v_symbolicChar_1691_ = lean_ctor_get_uint8(v_s_1685_, sizeof(void*)*10);
v_addFn_x3f_1692_ = lean_ctor_get(v_s_1685_, 5);
v_powFn_x3f_1693_ = lean_ctor_get(v_s_1685_, 7);
v_natCastFn_x3f_1694_ = lean_ctor_get(v_s_1685_, 8);
v_natSMulFn_x3f_1695_ = lean_ctor_get(v_s_1685_, 9);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_s_1685_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v_s_1685_, 6);
lean_dec(v_unused_1704_);
v___x_1697_ = v_s_1685_;
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_natSMulFn_x3f_1695_);
lean_inc(v_natCastFn_x3f_1694_);
lean_inc(v_powFn_x3f_1693_);
lean_inc(v_addFn_x3f_1692_);
lean_inc(v_charInst_x3f_1690_);
lean_inc(v_semiringInst_1689_);
lean_inc(v_u_1688_);
lean_inc(v_type_1687_);
lean_inc(v_id_1686_);
lean_dec(v_s_1685_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_mulFn_1684_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 6, v___x_1699_);
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_id_1686_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_type_1687_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_u_1688_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_semiringInst_1689_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v_charInst_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1702_, 5, v_addFn_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1702_, 6, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1702_, 7, v_powFn_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1702_, 8, v_natCastFn_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1702_, 9, v_natSMulFn_x3f_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*10, v_symbolicChar_1691_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1705_, lean_object* v_modifySemiring_1706_, lean_object* v_toBind_1707_, lean_object* v_mulFn_1708_){
_start:
{
lean_object* v___f_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_inc_ref(v_mulFn_1708_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1709_, 0, v_mulFn_1708_);
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1710_, 0, v_toPure_1705_);
lean_closure_set(v___f_1710_, 1, v_mulFn_1708_);
v___x_1711_ = lean_apply_1(v_modifySemiring_1706_, v___f_1709_);
v___x_1712_ = lean_apply_4(v_toBind_1707_, lean_box(0), lean_box(0), v___x_1711_, v___f_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_toBind_1718_, lean_object* v___f_1719_, lean_object* v_sr_1720_){
_start:
{
lean_object* v_mulFn_x3f_1721_; 
v_mulFn_x3f_1721_ = lean_ctor_get(v_sr_1720_, 6);
if (lean_obj_tag(v_mulFn_x3f_1721_) == 1)
{
lean_object* v_val_1722_; lean_object* v___x_1723_; 
lean_inc_ref(v_mulFn_x3f_1721_);
lean_dec_ref(v_sr_1720_);
lean_dec(v___f_1719_);
lean_dec(v_toBind_1718_);
lean_dec_ref(v_inst_1717_);
lean_dec_ref(v_inst_1716_);
lean_dec_ref(v_inst_1715_);
lean_dec(v_inst_1714_);
v_val_1722_ = lean_ctor_get(v_mulFn_x3f_1721_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v_mulFn_x3f_1721_, 1);
v___x_1723_ = lean_apply_2(v_toPure_1713_, lean_box(0), v_val_1722_);
return v___x_1723_;
}
else
{
lean_object* v_type_1724_; lean_object* v_u_1725_; lean_object* v_semiringInst_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_expectedInst_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_toPure_1713_);
v_type_1724_ = lean_ctor_get(v_sr_1720_, 1);
lean_inc_ref_n(v_type_1724_, 3);
v_u_1725_ = lean_ctor_get(v_sr_1720_, 2);
lean_inc_n(v_u_1725_, 2);
v_semiringInst_1726_ = lean_ctor_get(v_sr_1720_, 3);
lean_inc_ref(v_semiringInst_1726_);
lean_dec_ref(v_sr_1720_);
v___x_1727_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_u_1725_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
lean_inc_ref(v___x_1729_);
v___x_1730_ = l_Lean_mkConst(v___x_1727_, v___x_1729_);
v___x_1731_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1732_ = l_Lean_mkConst(v___x_1731_, v___x_1729_);
v___x_1733_ = l_Lean_mkAppB(v___x_1732_, v_type_1724_, v_semiringInst_1726_);
v_expectedInst_1734_ = l_Lean_mkAppB(v___x_1730_, v_type_1724_, v___x_1733_);
v___x_1735_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1736_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1737_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1714_, v_inst_1715_, v_inst_1716_, v_inst_1717_, v_type_1724_, v_u_1725_, v___x_1735_, v___x_1736_, v_expectedInst_1734_);
v___x_1738_ = lean_apply_4(v_toBind_1718_, lean_box(0), lean_box(0), v___x_1737_, v___f_1719_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_){
_start:
{
lean_object* v_toApplicative_1744_; lean_object* v_toBind_1745_; lean_object* v_getSemiring_1746_; lean_object* v_modifySemiring_1747_; lean_object* v_toPure_1748_; lean_object* v___f_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; 
v_toApplicative_1744_ = lean_ctor_get(v_inst_1741_, 0);
v_toBind_1745_ = lean_ctor_get(v_inst_1741_, 1);
lean_inc_n(v_toBind_1745_, 3);
v_getSemiring_1746_ = lean_ctor_get(v_inst_1743_, 0);
lean_inc(v_getSemiring_1746_);
v_modifySemiring_1747_ = lean_ctor_get(v_inst_1743_, 1);
lean_inc(v_modifySemiring_1747_);
lean_dec_ref(v_inst_1743_);
v_toPure_1748_ = lean_ctor_get(v_toApplicative_1744_, 1);
lean_inc_n(v_toPure_1748_, 2);
v___f_1749_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1749_, 0, v_toPure_1748_);
lean_closure_set(v___f_1749_, 1, v_modifySemiring_1747_);
lean_closure_set(v___f_1749_, 2, v_toBind_1745_);
v___f_1750_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1750_, 0, v_toPure_1748_);
lean_closure_set(v___f_1750_, 1, v_inst_1739_);
lean_closure_set(v___f_1750_, 2, v_inst_1740_);
lean_closure_set(v___f_1750_, 3, v_inst_1741_);
lean_closure_set(v___f_1750_, 4, v_inst_1742_);
lean_closure_set(v___f_1750_, 5, v_toBind_1745_);
lean_closure_set(v___f_1750_, 6, v___f_1749_);
v___x_1751_ = lean_apply_4(v_toBind_1745_, lean_box(0), lean_box(0), v_getSemiring_1746_, v___f_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_1752_, lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1753_, v_inst_1754_, v_inst_1755_, v_inst_1756_, v_inst_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1759_, lean_object* v_s_1760_){
_start:
{
lean_object* v_id_1761_; lean_object* v_type_1762_; lean_object* v_u_1763_; lean_object* v_semiringInst_1764_; lean_object* v_charInst_x3f_1765_; uint8_t v_symbolicChar_1766_; lean_object* v_addFn_x3f_1767_; lean_object* v_mulFn_x3f_1768_; lean_object* v_natCastFn_x3f_1769_; lean_object* v_natSMulFn_x3f_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1778_; 
v_id_1761_ = lean_ctor_get(v_s_1760_, 0);
v_type_1762_ = lean_ctor_get(v_s_1760_, 1);
v_u_1763_ = lean_ctor_get(v_s_1760_, 2);
v_semiringInst_1764_ = lean_ctor_get(v_s_1760_, 3);
v_charInst_x3f_1765_ = lean_ctor_get(v_s_1760_, 4);
v_symbolicChar_1766_ = lean_ctor_get_uint8(v_s_1760_, sizeof(void*)*10);
v_addFn_x3f_1767_ = lean_ctor_get(v_s_1760_, 5);
v_mulFn_x3f_1768_ = lean_ctor_get(v_s_1760_, 6);
v_natCastFn_x3f_1769_ = lean_ctor_get(v_s_1760_, 8);
v_natSMulFn_x3f_1770_ = lean_ctor_get(v_s_1760_, 9);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_s_1760_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v_s_1760_, 7);
lean_dec(v_unused_1779_);
v___x_1772_ = v_s_1760_;
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_natSMulFn_x3f_1770_);
lean_inc(v_natCastFn_x3f_1769_);
lean_inc(v_mulFn_x3f_1768_);
lean_inc(v_addFn_x3f_1767_);
lean_inc(v_charInst_x3f_1765_);
lean_inc(v_semiringInst_1764_);
lean_inc(v_u_1763_);
lean_inc(v_type_1762_);
lean_inc(v_id_1761_);
lean_dec(v_s_1760_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_powFn_1759_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 7, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_id_1761_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_type_1762_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_u_1763_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_semiringInst_1764_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v_charInst_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1777_, 5, v_addFn_x3f_1767_);
lean_ctor_set(v_reuseFailAlloc_1777_, 6, v_mulFn_x3f_1768_);
lean_ctor_set(v_reuseFailAlloc_1777_, 7, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1777_, 8, v_natCastFn_x3f_1769_);
lean_ctor_set(v_reuseFailAlloc_1777_, 9, v_natSMulFn_x3f_1770_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*10, v_symbolicChar_1766_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1780_, lean_object* v_modifySemiring_1781_, lean_object* v_toBind_1782_, lean_object* v_powFn_1783_){
_start:
{
lean_object* v___f_1784_; lean_object* v___f_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_inc_ref(v_powFn_1783_);
v___f_1784_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1784_, 0, v_powFn_1783_);
v___f_1785_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1785_, 0, v_toPure_1780_);
lean_closure_set(v___f_1785_, 1, v_powFn_1783_);
v___x_1786_ = lean_apply_1(v_modifySemiring_1781_, v___f_1784_);
v___x_1787_ = lean_apply_4(v_toBind_1782_, lean_box(0), lean_box(0), v___x_1786_, v___f_1785_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_toBind_1793_, lean_object* v___f_1794_, lean_object* v_sr_1795_){
_start:
{
lean_object* v_powFn_x3f_1796_; 
v_powFn_x3f_1796_ = lean_ctor_get(v_sr_1795_, 7);
if (lean_obj_tag(v_powFn_x3f_1796_) == 1)
{
lean_object* v_val_1797_; lean_object* v___x_1798_; 
lean_inc_ref(v_powFn_x3f_1796_);
lean_dec_ref(v_sr_1795_);
lean_dec(v___f_1794_);
lean_dec(v_toBind_1793_);
lean_dec_ref(v_inst_1792_);
lean_dec_ref(v_inst_1791_);
lean_dec_ref(v_inst_1790_);
lean_dec(v_inst_1789_);
v_val_1797_ = lean_ctor_get(v_powFn_x3f_1796_, 0);
lean_inc(v_val_1797_);
lean_dec_ref_known(v_powFn_x3f_1796_, 1);
v___x_1798_ = lean_apply_2(v_toPure_1788_, lean_box(0), v_val_1797_);
return v___x_1798_;
}
else
{
lean_object* v_type_1799_; lean_object* v_u_1800_; lean_object* v_semiringInst_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_dec(v_toPure_1788_);
v_type_1799_ = lean_ctor_get(v_sr_1795_, 1);
lean_inc_ref(v_type_1799_);
v_u_1800_ = lean_ctor_get(v_sr_1795_, 2);
lean_inc(v_u_1800_);
v_semiringInst_1801_ = lean_ctor_get(v_sr_1795_, 3);
lean_inc_ref(v_semiringInst_1801_);
lean_dec_ref(v_sr_1795_);
v___x_1802_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1789_, v_inst_1790_, v_inst_1791_, v_inst_1792_, v_u_1800_, v_type_1799_, v_semiringInst_1801_);
v___x_1803_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v___x_1802_, v___f_1794_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_inst_1808_){
_start:
{
lean_object* v_toApplicative_1809_; lean_object* v_toBind_1810_; lean_object* v_getSemiring_1811_; lean_object* v_modifySemiring_1812_; lean_object* v_toPure_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; 
v_toApplicative_1809_ = lean_ctor_get(v_inst_1806_, 0);
v_toBind_1810_ = lean_ctor_get(v_inst_1806_, 1);
lean_inc_n(v_toBind_1810_, 3);
v_getSemiring_1811_ = lean_ctor_get(v_inst_1808_, 0);
lean_inc(v_getSemiring_1811_);
v_modifySemiring_1812_ = lean_ctor_get(v_inst_1808_, 1);
lean_inc(v_modifySemiring_1812_);
lean_dec_ref(v_inst_1808_);
v_toPure_1813_ = lean_ctor_get(v_toApplicative_1809_, 1);
lean_inc_n(v_toPure_1813_, 2);
v___f_1814_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1814_, 0, v_toPure_1813_);
lean_closure_set(v___f_1814_, 1, v_modifySemiring_1812_);
lean_closure_set(v___f_1814_, 2, v_toBind_1810_);
v___f_1815_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1815_, 0, v_toPure_1813_);
lean_closure_set(v___f_1815_, 1, v_inst_1804_);
lean_closure_set(v___f_1815_, 2, v_inst_1805_);
lean_closure_set(v___f_1815_, 3, v_inst_1806_);
lean_closure_set(v___f_1815_, 4, v_inst_1807_);
lean_closure_set(v___f_1815_, 5, v_toBind_1810_);
lean_closure_set(v___f_1815_, 6, v___f_1814_);
v___x_1816_ = lean_apply_4(v_toBind_1810_, lean_box(0), lean_box(0), v_getSemiring_1811_, v___f_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1818_, v_inst_1819_, v_inst_1820_, v_inst_1821_, v_inst_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1824_, lean_object* v_s_1825_){
_start:
{
lean_object* v_id_1826_; lean_object* v_type_1827_; lean_object* v_u_1828_; lean_object* v_semiringInst_1829_; lean_object* v_charInst_x3f_1830_; uint8_t v_symbolicChar_1831_; lean_object* v_addFn_x3f_1832_; lean_object* v_mulFn_x3f_1833_; lean_object* v_powFn_x3f_1834_; lean_object* v_natSMulFn_x3f_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_id_1826_ = lean_ctor_get(v_s_1825_, 0);
v_type_1827_ = lean_ctor_get(v_s_1825_, 1);
v_u_1828_ = lean_ctor_get(v_s_1825_, 2);
v_semiringInst_1829_ = lean_ctor_get(v_s_1825_, 3);
v_charInst_x3f_1830_ = lean_ctor_get(v_s_1825_, 4);
v_symbolicChar_1831_ = lean_ctor_get_uint8(v_s_1825_, sizeof(void*)*10);
v_addFn_x3f_1832_ = lean_ctor_get(v_s_1825_, 5);
v_mulFn_x3f_1833_ = lean_ctor_get(v_s_1825_, 6);
v_powFn_x3f_1834_ = lean_ctor_get(v_s_1825_, 7);
v_natSMulFn_x3f_1835_ = lean_ctor_get(v_s_1825_, 9);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_s_1825_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_s_1825_, 8);
lean_dec(v_unused_1844_);
v___x_1837_ = v_s_1825_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_natSMulFn_x3f_1835_);
lean_inc(v_powFn_x3f_1834_);
lean_inc(v_mulFn_x3f_1833_);
lean_inc(v_addFn_x3f_1832_);
lean_inc(v_charInst_x3f_1830_);
lean_inc(v_semiringInst_1829_);
lean_inc(v_u_1828_);
lean_inc(v_type_1827_);
lean_inc(v_id_1826_);
lean_dec(v_s_1825_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1839_, 0, v_natCastFn_1824_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 8, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_id_1826_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_type_1827_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_u_1828_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_semiringInst_1829_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_charInst_x3f_1830_);
lean_ctor_set(v_reuseFailAlloc_1842_, 5, v_addFn_x3f_1832_);
lean_ctor_set(v_reuseFailAlloc_1842_, 6, v_mulFn_x3f_1833_);
lean_ctor_set(v_reuseFailAlloc_1842_, 7, v_powFn_x3f_1834_);
lean_ctor_set(v_reuseFailAlloc_1842_, 8, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1842_, 9, v_natSMulFn_x3f_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*10, v_symbolicChar_1831_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1845_, lean_object* v_modifySemiring_1846_, lean_object* v_toBind_1847_, lean_object* v_natCastFn_1848_){
_start:
{
lean_object* v___f_1849_; lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_inc_ref(v_natCastFn_1848_);
v___f_1849_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1849_, 0, v_natCastFn_1848_);
v___f_1850_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1850_, 0, v_toPure_1845_);
lean_closure_set(v___f_1850_, 1, v_natCastFn_1848_);
v___x_1851_ = lean_apply_1(v_modifySemiring_1846_, v___f_1849_);
v___x_1852_ = lean_apply_4(v_toBind_1847_, lean_box(0), lean_box(0), v___x_1851_, v___f_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_toBind_1857_, lean_object* v___f_1858_, lean_object* v_sr_1859_){
_start:
{
lean_object* v_natCastFn_x3f_1860_; 
v_natCastFn_x3f_1860_ = lean_ctor_get(v_sr_1859_, 8);
if (lean_obj_tag(v_natCastFn_x3f_1860_) == 1)
{
lean_object* v_val_1861_; lean_object* v___x_1862_; 
lean_inc_ref(v_natCastFn_x3f_1860_);
lean_dec_ref(v_sr_1859_);
lean_dec(v___f_1858_);
lean_dec(v_toBind_1857_);
lean_dec_ref(v_inst_1856_);
lean_dec_ref(v_inst_1855_);
lean_dec(v_inst_1854_);
v_val_1861_ = lean_ctor_get(v_natCastFn_x3f_1860_, 0);
lean_inc(v_val_1861_);
lean_dec_ref_known(v_natCastFn_x3f_1860_, 1);
v___x_1862_ = lean_apply_2(v_toPure_1853_, lean_box(0), v_val_1861_);
return v___x_1862_;
}
else
{
lean_object* v_type_1863_; lean_object* v_u_1864_; lean_object* v_semiringInst_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec(v_toPure_1853_);
v_type_1863_ = lean_ctor_get(v_sr_1859_, 1);
lean_inc_ref(v_type_1863_);
v_u_1864_ = lean_ctor_get(v_sr_1859_, 2);
lean_inc(v_u_1864_);
v_semiringInst_1865_ = lean_ctor_get(v_sr_1859_, 3);
lean_inc_ref(v_semiringInst_1865_);
lean_dec_ref(v_sr_1859_);
v___x_1866_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1854_, v_inst_1855_, v_inst_1856_, v_u_1864_, v_type_1863_, v_semiringInst_1865_);
v___x_1867_ = lean_apply_4(v_toBind_1857_, lean_box(0), lean_box(0), v___x_1866_, v___f_1858_);
return v___x_1867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_){
_start:
{
lean_object* v_toApplicative_1872_; lean_object* v_toBind_1873_; lean_object* v_getSemiring_1874_; lean_object* v_modifySemiring_1875_; lean_object* v_toPure_1876_; lean_object* v___f_1877_; lean_object* v___f_1878_; lean_object* v___x_1879_; 
v_toApplicative_1872_ = lean_ctor_get(v_inst_1869_, 0);
v_toBind_1873_ = lean_ctor_get(v_inst_1869_, 1);
lean_inc_n(v_toBind_1873_, 3);
v_getSemiring_1874_ = lean_ctor_get(v_inst_1871_, 0);
lean_inc(v_getSemiring_1874_);
v_modifySemiring_1875_ = lean_ctor_get(v_inst_1871_, 1);
lean_inc(v_modifySemiring_1875_);
lean_dec_ref(v_inst_1871_);
v_toPure_1876_ = lean_ctor_get(v_toApplicative_1872_, 1);
lean_inc_n(v_toPure_1876_, 2);
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1877_, 0, v_toPure_1876_);
lean_closure_set(v___f_1877_, 1, v_modifySemiring_1875_);
lean_closure_set(v___f_1877_, 2, v_toBind_1873_);
v___f_1878_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1878_, 0, v_toPure_1876_);
lean_closure_set(v___f_1878_, 1, v_inst_1868_);
lean_closure_set(v___f_1878_, 2, v_inst_1869_);
lean_closure_set(v___f_1878_, 3, v_inst_1870_);
lean_closure_set(v___f_1878_, 4, v_toBind_1873_);
lean_closure_set(v___f_1878_, 5, v___f_1877_);
v___x_1879_ = lean_apply_4(v_toBind_1873_, lean_box(0), lean_box(0), v_getSemiring_1874_, v___f_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1881_, v_inst_1882_, v_inst_1883_, v_inst_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0(lean_object* v_toQFn_1886_, lean_object* v_s_1887_){
_start:
{
lean_object* v_toSemiring_1888_; lean_object* v_ringId_1889_; lean_object* v_commSemiringInst_1890_; lean_object* v_addRightCancelInst_x3f_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
v_toSemiring_1888_ = lean_ctor_get(v_s_1887_, 0);
v_ringId_1889_ = lean_ctor_get(v_s_1887_, 1);
v_commSemiringInst_1890_ = lean_ctor_get(v_s_1887_, 2);
v_addRightCancelInst_x3f_1891_ = lean_ctor_get(v_s_1887_, 3);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_s_1887_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_s_1887_, 4);
lean_dec(v_unused_1900_);
v___x_1893_ = v_s_1887_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_1891_);
lean_inc(v_commSemiringInst_1890_);
lean_inc(v_ringId_1889_);
lean_inc(v_toSemiring_1888_);
lean_dec(v_s_1887_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_toQFn_1886_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 4, v___x_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_toSemiring_1888_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_ringId_1889_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_commSemiringInst_1890_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_addRightCancelInst_x3f_1891_);
lean_ctor_set(v_reuseFailAlloc_1898_, 4, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1(lean_object* v_toPure_1901_, lean_object* v_toQFn_1902_, lean_object* v_____r_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_apply_2(v_toPure_1901_, lean_box(0), v_toQFn_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2(lean_object* v_toPure_1905_, lean_object* v_modifyCommSemiring_1906_, lean_object* v_toBind_1907_, lean_object* v_toQFn_1908_){
_start:
{
lean_object* v___f_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_inc_ref(v_toQFn_1908_);
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1909_, 0, v_toQFn_1908_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1910_, 0, v_toPure_1905_);
lean_closure_set(v___f_1910_, 1, v_toQFn_1908_);
v___x_1911_ = lean_apply_1(v_modifyCommSemiring_1906_, v___f_1909_);
v___x_1912_ = lean_apply_4(v_toBind_1907_, lean_box(0), lean_box(0), v___x_1911_, v___f_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3(lean_object* v_toPure_1921_, lean_object* v_inst_1922_, lean_object* v_toBind_1923_, lean_object* v___f_1924_, lean_object* v_s_1925_){
_start:
{
lean_object* v_toQFn_x3f_1926_; 
v_toQFn_x3f_1926_ = lean_ctor_get(v_s_1925_, 4);
if (lean_obj_tag(v_toQFn_x3f_1926_) == 1)
{
lean_object* v_val_1927_; lean_object* v___x_1928_; 
lean_inc_ref(v_toQFn_x3f_1926_);
lean_dec_ref(v_s_1925_);
lean_dec(v___f_1924_);
lean_dec(v_toBind_1923_);
lean_dec_ref(v_inst_1922_);
v_val_1927_ = lean_ctor_get(v_toQFn_x3f_1926_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v_toQFn_x3f_1926_, 1);
v___x_1928_ = lean_apply_2(v_toPure_1921_, lean_box(0), v_val_1927_);
return v___x_1928_;
}
else
{
lean_object* v_toSemiring_1929_; lean_object* v_canonExpr_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_toPure_1921_);
v_toSemiring_1929_ = lean_ctor_get(v_s_1925_, 0);
lean_inc_ref(v_toSemiring_1929_);
lean_dec_ref(v_s_1925_);
v_canonExpr_1930_ = lean_ctor_get(v_inst_1922_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_inst_1922_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v_inst_1922_, 1);
lean_dec(v_unused_1947_);
v___x_1932_ = v_inst_1922_;
v_isShared_1933_ = v_isSharedCheck_1946_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_canonExpr_1930_);
lean_dec(v_inst_1922_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1946_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v_type_1934_; lean_object* v_u_1935_; lean_object* v_semiringInst_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v_type_1934_ = lean_ctor_get(v_toSemiring_1929_, 1);
lean_inc_ref(v_type_1934_);
v_u_1935_ = lean_ctor_get(v_toSemiring_1929_, 2);
lean_inc(v_u_1935_);
v_semiringInst_1936_ = lean_ctor_get(v_toSemiring_1929_, 3);
lean_inc_ref(v_semiringInst_1936_);
lean_dec_ref(v_toSemiring_1929_);
v___x_1937_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2));
v___x_1938_ = lean_box(0);
if (v_isShared_1933_ == 0)
{
lean_ctor_set_tag(v___x_1932_, 1);
lean_ctor_set(v___x_1932_, 1, v___x_1938_);
lean_ctor_set(v___x_1932_, 0, v_u_1935_);
v___x_1940_ = v___x_1932_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_u_1935_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1941_ = l_Lean_mkConst(v___x_1937_, v___x_1940_);
v___x_1942_ = l_Lean_mkAppB(v___x_1941_, v_type_1934_, v_semiringInst_1936_);
v___x_1943_ = lean_apply_1(v_canonExpr_1930_, v___x_1942_);
v___x_1944_ = lean_apply_4(v_toBind_1923_, lean_box(0), lean_box(0), v___x_1943_, v___f_1924_);
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg(lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_){
_start:
{
lean_object* v_toApplicative_1951_; lean_object* v_toBind_1952_; lean_object* v_getCommSemiring_1953_; lean_object* v_modifyCommSemiring_1954_; lean_object* v_toPure_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; 
v_toApplicative_1951_ = lean_ctor_get(v_inst_1948_, 0);
lean_inc_ref(v_toApplicative_1951_);
v_toBind_1952_ = lean_ctor_get(v_inst_1948_, 1);
lean_inc_n(v_toBind_1952_, 3);
lean_dec_ref(v_inst_1948_);
v_getCommSemiring_1953_ = lean_ctor_get(v_inst_1950_, 0);
lean_inc(v_getCommSemiring_1953_);
v_modifyCommSemiring_1954_ = lean_ctor_get(v_inst_1950_, 1);
lean_inc(v_modifyCommSemiring_1954_);
lean_dec_ref(v_inst_1950_);
v_toPure_1955_ = lean_ctor_get(v_toApplicative_1951_, 1);
lean_inc_n(v_toPure_1955_, 2);
lean_dec_ref(v_toApplicative_1951_);
v___f_1956_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1956_, 0, v_toPure_1955_);
lean_closure_set(v___f_1956_, 1, v_modifyCommSemiring_1954_);
lean_closure_set(v___f_1956_, 2, v_toBind_1952_);
v___f_1957_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1957_, 0, v_toPure_1955_);
lean_closure_set(v___f_1957_, 1, v_inst_1949_);
lean_closure_set(v___f_1957_, 2, v_toBind_1952_);
lean_closure_set(v___f_1957_, 3, v___f_1956_);
v___x_1958_ = lean_apply_4(v_toBind_1952_, lean_box(0), lean_box(0), v_getCommSemiring_1953_, v___f_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn(lean_object* v_m_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_Meta_Sym_Arith_getToQFn___redArg(v_inst_1960_, v_inst_1961_, v_inst_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0(lean_object* v_addRightCancelInst_x3f_1964_, lean_object* v_s_1965_){
_start:
{
lean_object* v_toSemiring_1966_; lean_object* v_ringId_1967_; lean_object* v_commSemiringInst_1968_; lean_object* v_toQFn_x3f_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1977_; 
v_toSemiring_1966_ = lean_ctor_get(v_s_1965_, 0);
v_ringId_1967_ = lean_ctor_get(v_s_1965_, 1);
v_commSemiringInst_1968_ = lean_ctor_get(v_s_1965_, 2);
v_toQFn_x3f_1969_ = lean_ctor_get(v_s_1965_, 4);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_s_1965_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v_s_1965_, 3);
lean_dec(v_unused_1978_);
v___x_1971_ = v_s_1965_;
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_toQFn_x3f_1969_);
lean_inc(v_commSemiringInst_1968_);
lean_inc(v_ringId_1967_);
lean_inc(v_toSemiring_1966_);
lean_dec(v_s_1965_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_addRightCancelInst_x3f_1964_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 3, v___x_1973_);
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_toSemiring_1966_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_ringId_1967_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_commSemiringInst_1968_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v_toQFn_x3f_1969_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1(lean_object* v_toPure_1979_, lean_object* v_addRightCancelInst_x3f_1980_, lean_object* v_____r_1981_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_apply_2(v_toPure_1979_, lean_box(0), v_addRightCancelInst_x3f_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2(lean_object* v_toPure_1983_, lean_object* v_modifyCommSemiring_1984_, lean_object* v_toBind_1985_, lean_object* v_addRightCancelInst_x3f_1986_){
_start:
{
lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_inc(v_addRightCancelInst_x3f_1986_);
v___f_1987_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1987_, 0, v_addRightCancelInst_x3f_1986_);
v___f_1988_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1988_, 0, v_toPure_1983_);
lean_closure_set(v___f_1988_, 1, v_addRightCancelInst_x3f_1986_);
v___x_1989_ = lean_apply_1(v_modifyCommSemiring_1984_, v___f_1987_);
v___x_1990_ = lean_apply_4(v_toBind_1985_, lean_box(0), lean_box(0), v___x_1989_, v___f_1988_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3(lean_object* v___f_1991_, lean_object* v_addRightCancelInst_x3f_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_apply_1(v___f_1991_, v_addRightCancelInst_x3f_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5(lean_object* v___x_1999_, lean_object* v_type_2000_, lean_object* v_synthInstance_x3f_2001_, lean_object* v_toBind_2002_, lean_object* v___f_2003_, lean_object* v_toPure_2004_, lean_object* v___f_2005_, lean_object* v_____x_2006_){
_start:
{
if (lean_obj_tag(v_____x_2006_) == 1)
{
lean_object* v_val_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_dec(v___f_2005_);
lean_dec(v_toPure_2004_);
v_val_2007_ = lean_ctor_get(v_____x_2006_, 0);
lean_inc(v_val_2007_);
lean_dec_ref_known(v_____x_2006_, 1);
v___x_2008_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1));
v___x_2009_ = l_Lean_mkConst(v___x_2008_, v___x_1999_);
v___x_2010_ = l_Lean_mkAppB(v___x_2009_, v_type_2000_, v_val_2007_);
v___x_2011_ = lean_apply_1(v_synthInstance_x3f_2001_, v___x_2010_);
v___x_2012_ = lean_apply_4(v_toBind_2002_, lean_box(0), lean_box(0), v___x_2011_, v___f_2003_);
return v___x_2012_;
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v_____x_2006_);
lean_dec(v___f_2003_);
lean_dec(v_synthInstance_x3f_2001_);
lean_dec_ref(v_type_2000_);
lean_dec(v___x_1999_);
v___x_2013_ = lean_box(0);
v___x_2014_ = lean_apply_2(v_toPure_2004_, lean_box(0), v___x_2013_);
v___x_2015_ = lean_apply_4(v_toBind_2002_, lean_box(0), lean_box(0), v___x_2014_, v___f_2005_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4(lean_object* v_toPure_2019_, lean_object* v_inst_2020_, lean_object* v_toBind_2021_, lean_object* v___f_2022_, lean_object* v___f_2023_, lean_object* v_s_2024_){
_start:
{
lean_object* v_addRightCancelInst_x3f_2025_; 
v_addRightCancelInst_x3f_2025_ = lean_ctor_get(v_s_2024_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_2025_) == 1)
{
lean_object* v_val_2026_; lean_object* v___x_2027_; 
lean_inc_ref(v_addRightCancelInst_x3f_2025_);
lean_dec_ref(v_s_2024_);
lean_dec(v___f_2023_);
lean_dec(v___f_2022_);
lean_dec(v_toBind_2021_);
lean_dec_ref(v_inst_2020_);
v_val_2026_ = lean_ctor_get(v_addRightCancelInst_x3f_2025_, 0);
lean_inc(v_val_2026_);
lean_dec_ref_known(v_addRightCancelInst_x3f_2025_, 1);
v___x_2027_ = lean_apply_2(v_toPure_2019_, lean_box(0), v_val_2026_);
return v___x_2027_;
}
else
{
lean_object* v_toSemiring_2028_; lean_object* v_synthInstance_x3f_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2045_; 
v_toSemiring_2028_ = lean_ctor_get(v_s_2024_, 0);
lean_inc_ref(v_toSemiring_2028_);
lean_dec_ref(v_s_2024_);
v_synthInstance_x3f_2029_ = lean_ctor_get(v_inst_2020_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_inst_2020_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_inst_2020_, 0);
lean_dec(v_unused_2046_);
v___x_2031_ = v_inst_2020_;
v_isShared_2032_ = v_isSharedCheck_2045_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_synthInstance_x3f_2029_);
lean_dec(v_inst_2020_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2045_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_type_2033_; lean_object* v_u_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_type_2033_ = lean_ctor_get(v_toSemiring_2028_, 1);
lean_inc_ref(v_type_2033_);
v_u_2034_ = lean_ctor_get(v_toSemiring_2028_, 2);
lean_inc(v_u_2034_);
lean_dec_ref(v_toSemiring_2028_);
v___x_2035_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1));
v___x_2036_ = lean_box(0);
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 1);
lean_ctor_set(v___x_2031_, 1, v___x_2036_);
lean_ctor_set(v___x_2031_, 0, v_u_2034_);
v___x_2038_ = v___x_2031_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_u_2034_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___f_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_inc(v_toBind_2021_);
lean_inc(v_synthInstance_x3f_2029_);
lean_inc_ref(v_type_2033_);
lean_inc_ref(v___x_2038_);
v___f_2039_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_2039_, 0, v___x_2038_);
lean_closure_set(v___f_2039_, 1, v_type_2033_);
lean_closure_set(v___f_2039_, 2, v_synthInstance_x3f_2029_);
lean_closure_set(v___f_2039_, 3, v_toBind_2021_);
lean_closure_set(v___f_2039_, 4, v___f_2022_);
lean_closure_set(v___f_2039_, 5, v_toPure_2019_);
lean_closure_set(v___f_2039_, 6, v___f_2023_);
v___x_2040_ = l_Lean_mkConst(v___x_2035_, v___x_2038_);
v___x_2041_ = l_Lean_Expr_app___override(v___x_2040_, v_type_2033_);
v___x_2042_ = lean_apply_1(v_synthInstance_x3f_2029_, v___x_2041_);
v___x_2043_ = lean_apply_4(v_toBind_2021_, lean_box(0), lean_box(0), v___x_2042_, v___f_2039_);
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_){
_start:
{
lean_object* v_toApplicative_2050_; lean_object* v_toBind_2051_; lean_object* v_getCommSemiring_2052_; lean_object* v_modifyCommSemiring_2053_; lean_object* v_toPure_2054_; lean_object* v___f_2055_; lean_object* v___f_2056_; lean_object* v___f_2057_; lean_object* v___x_2058_; 
v_toApplicative_2050_ = lean_ctor_get(v_inst_2047_, 0);
lean_inc_ref(v_toApplicative_2050_);
v_toBind_2051_ = lean_ctor_get(v_inst_2047_, 1);
lean_inc_n(v_toBind_2051_, 3);
lean_dec_ref(v_inst_2047_);
v_getCommSemiring_2052_ = lean_ctor_get(v_inst_2049_, 0);
lean_inc(v_getCommSemiring_2052_);
v_modifyCommSemiring_2053_ = lean_ctor_get(v_inst_2049_, 1);
lean_inc(v_modifyCommSemiring_2053_);
lean_dec_ref(v_inst_2049_);
v_toPure_2054_ = lean_ctor_get(v_toApplicative_2050_, 1);
lean_inc_n(v_toPure_2054_, 2);
lean_dec_ref(v_toApplicative_2050_);
v___f_2055_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2055_, 0, v_toPure_2054_);
lean_closure_set(v___f_2055_, 1, v_modifyCommSemiring_2053_);
lean_closure_set(v___f_2055_, 2, v_toBind_2051_);
v___f_2056_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2056_, 0, v___f_2055_);
lean_inc_ref(v___f_2056_);
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4), 6, 5);
lean_closure_set(v___f_2057_, 0, v_toPure_2054_);
lean_closure_set(v___f_2057_, 1, v_inst_2048_);
lean_closure_set(v___f_2057_, 2, v_toBind_2051_);
lean_closure_set(v___f_2057_, 3, v___f_2056_);
lean_closure_set(v___f_2057_, 4, v___f_2056_);
v___x_2058_ = lean_apply_4(v_toBind_2051_, lean_box(0), lean_box(0), v_getCommSemiring_2052_, v___f_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f(lean_object* v_m_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(v_inst_2060_, v_inst_2061_, v_inst_2062_);
return v___x_2063_;
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
