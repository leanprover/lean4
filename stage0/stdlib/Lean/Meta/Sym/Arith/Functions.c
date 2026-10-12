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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0));
v___x_54_ = l_Lean_stringToMessageData(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2));
v___x_57_ = l_Lean_stringToMessageData(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4));
v___x_60_ = l_Lean_stringToMessageData(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6));
v___x_63_ = l_Lean_stringToMessageData(v___x_62_);
return v___x_63_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object* v_declName_64_, lean_object* v_inst_65_, lean_object* v_inst_x27_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___y_73_; lean_object* v___x_106_; uint8_t v_transparency_107_; uint8_t v___x_108_; uint8_t v___x_109_; 
v___x_106_ = l_Lean_Meta_Context_config(v_a_67_);
v_transparency_107_ = lean_ctor_get_uint8(v___x_106_, 9);
lean_dec_ref(v___x_106_);
v___x_108_ = 3;
v___x_109_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v_keyedConfig_110_; uint8_t v_trackZetaDelta_111_; lean_object* v_zetaDeltaSet_112_; lean_object* v_lctx_113_; lean_object* v_localInstances_114_; lean_object* v_defEqCtx_x3f_115_; lean_object* v_synthPendingDepth_116_; lean_object* v_customCanUnfoldPredicate_x3f_117_; uint8_t v_univApprox_118_; uint8_t v_inTypeClassResolution_119_; uint8_t v_cacheInferType_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_keyedConfig_110_ = lean_ctor_get(v_a_67_, 0);
v_trackZetaDelta_111_ = lean_ctor_get_uint8(v_a_67_, sizeof(void*)*7);
v_zetaDeltaSet_112_ = lean_ctor_get(v_a_67_, 1);
v_lctx_113_ = lean_ctor_get(v_a_67_, 2);
v_localInstances_114_ = lean_ctor_get(v_a_67_, 3);
v_defEqCtx_x3f_115_ = lean_ctor_get(v_a_67_, 4);
v_synthPendingDepth_116_ = lean_ctor_get(v_a_67_, 5);
v_customCanUnfoldPredicate_x3f_117_ = lean_ctor_get(v_a_67_, 6);
v_univApprox_118_ = lean_ctor_get_uint8(v_a_67_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_119_ = lean_ctor_get_uint8(v_a_67_, sizeof(void*)*7 + 2);
v_cacheInferType_120_ = lean_ctor_get_uint8(v_a_67_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_110_);
v___x_121_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_108_, v_keyedConfig_110_);
lean_inc(v_customCanUnfoldPredicate_x3f_117_);
lean_inc(v_synthPendingDepth_116_);
lean_inc(v_defEqCtx_x3f_115_);
lean_inc_ref(v_localInstances_114_);
lean_inc_ref(v_lctx_113_);
lean_inc(v_zetaDeltaSet_112_);
v___x_122_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v_zetaDeltaSet_112_);
lean_ctor_set(v___x_122_, 2, v_lctx_113_);
lean_ctor_set(v___x_122_, 3, v_localInstances_114_);
lean_ctor_set(v___x_122_, 4, v_defEqCtx_x3f_115_);
lean_ctor_set(v___x_122_, 5, v_synthPendingDepth_116_);
lean_ctor_set(v___x_122_, 6, v_customCanUnfoldPredicate_x3f_117_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*7, v_trackZetaDelta_111_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*7 + 1, v_univApprox_118_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*7 + 2, v_inTypeClassResolution_119_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*7 + 3, v_cacheInferType_120_);
lean_inc_ref(v_inst_x27_66_);
lean_inc_ref(v_inst_65_);
v___x_123_ = l_Lean_Meta_isExprDefEq(v_inst_65_, v_inst_x27_66_, v___x_122_, v_a_68_, v_a_69_, v_a_70_);
lean_dec_ref_known(v___x_122_, 7);
v___y_73_ = v___x_123_;
goto v___jp_72_;
}
else
{
lean_object* v___x_124_; 
lean_inc_ref(v_inst_x27_66_);
lean_inc_ref(v_inst_65_);
v___x_124_ = l_Lean_Meta_isExprDefEq(v_inst_65_, v_inst_x27_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
v___y_73_ = v___x_124_;
goto v___jp_72_;
}
v___jp_72_:
{
if (lean_obj_tag(v___y_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_97_; 
v_a_74_ = lean_ctor_get(v___y_73_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___y_73_);
if (v_isSharedCheck_97_ == 0)
{
v___x_76_ = v___y_73_;
v_isShared_77_ = v_isSharedCheck_97_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___y_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_97_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
uint8_t v___x_78_; 
v___x_78_ = lean_unbox(v_a_74_);
lean_dec(v_a_74_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_del_object(v___x_76_);
v___x_79_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1);
v___x_80_ = l_Lean_MessageData_ofName(v_declName_64_);
v___x_81_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3);
v___x_83_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = l_Lean_indentExpr(v_inst_65_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5);
v___x_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = l_Lean_indentExpr(v_inst_x27_66_);
v___x_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7);
v___x_91_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_91_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_95_; 
lean_dec_ref(v_inst_x27_66_);
lean_dec_ref(v_inst_65_);
lean_dec(v_declName_64_);
v___x_93_ = lean_box(0);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_93_);
v___x_95_ = v___x_76_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec_ref(v_inst_x27_66_);
lean_dec_ref(v_inst_65_);
lean_dec(v_declName_64_);
v_a_98_ = lean_ctor_get(v___y_73_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___y_73_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___y_73_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___y_73_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_64_ = stack[0].m_obj;
lean_object* v_inst_65_ = stack[1].m_obj;
lean_object* v_inst_x27_66_ = stack[2].m_obj;
lean_object* v_a_67_ = stack[3].m_obj;
lean_object* v_a_68_ = stack[4].m_obj;
lean_object* v_a_69_ = stack[5].m_obj;
lean_object* v_a_70_ = stack[6].m_obj;
lean_object* v_res_125_;
v_res_125_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_64_, v_inst_65_, v_inst_x27_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object* v_declName_126_, lean_object* v_inst_127_, lean_object* v_inst_x27_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_126_, v_inst_127_, v_inst_x27_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
return v_res_134_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object* v_00_u03b1_135_, lean_object* v_msg_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
return v___x_142_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_136_ = stack[1].m_obj;
lean_object* v___y_137_ = stack[2].m_obj;
lean_object* v___y_138_ = stack[3].m_obj;
lean_object* v___y_139_ = stack[4].m_obj;
lean_object* v___y_140_ = stack[5].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_box(0), v_msg_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(lean_object* v_00_u03b1_144_, lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(v_00_u03b1_144_, v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object* v_inst_152_, lean_object* v_declName_153_, lean_object* v___x_154_, lean_object* v_type_155_, lean_object* v_inst_156_, lean_object* v_____r_157_){
_start:
{
lean_object* v_canonExpr_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_canonExpr_158_ = lean_ctor_get(v_inst_152_, 0);
lean_inc(v_canonExpr_158_);
lean_dec_ref(v_inst_152_);
v___x_159_ = l_Lean_mkConst(v_declName_153_, v___x_154_);
v___x_160_ = l_Lean_mkAppB(v___x_159_, v_type_155_, v_inst_156_);
v___x_161_ = lean_apply_1(v_canonExpr_158_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object* v_inst_162_, lean_object* v_declName_163_, lean_object* v___x_164_, lean_object* v_type_165_, lean_object* v_expectedInst_166_, lean_object* v_inst_167_, lean_object* v_toBind_168_, lean_object* v_inst_169_){
_start:
{
lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
lean_inc_ref(v_inst_169_);
lean_inc(v_declName_163_);
v___f_170_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_170_, 0, v_inst_162_);
lean_closure_set(v___f_170_, 1, v_declName_163_);
lean_closure_set(v___f_170_, 2, v___x_164_);
lean_closure_set(v___f_170_, 3, v_type_165_);
lean_closure_set(v___f_170_, 4, v_inst_169_);
v___x_171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_171_, 0, v_declName_163_);
lean_closure_set(v___x_171_, 1, v_inst_169_);
lean_closure_set(v___x_171_, 2, v_expectedInst_166_);
v___x_172_ = lean_apply_2(v_inst_167_, lean_box(0), v___x_171_);
v___x_173_ = lean_apply_4(v_toBind_168_, lean_box(0), lean_box(0), v___x_172_, v___f_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_type_178_, lean_object* v_u_179_, lean_object* v_instDeclName_180_, lean_object* v_declName_181_, lean_object* v_expectedInst_182_){
_start:
{
lean_object* v_toBind_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_toBind_183_ = lean_ctor_get(v_inst_176_, 1);
lean_inc_n(v_toBind_183_, 2);
v___x_184_ = lean_box(0);
v___x_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_185_, 0, v_u_179_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
lean_inc_ref(v_type_178_);
lean_inc_ref(v___x_185_);
lean_inc_ref(v_inst_177_);
v___f_186_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_186_, 0, v_inst_177_);
lean_closure_set(v___f_186_, 1, v_declName_181_);
lean_closure_set(v___f_186_, 2, v___x_185_);
lean_closure_set(v___f_186_, 3, v_type_178_);
lean_closure_set(v___f_186_, 4, v_expectedInst_182_);
lean_closure_set(v___f_186_, 5, v_inst_174_);
lean_closure_set(v___f_186_, 6, v_toBind_183_);
v___x_187_ = l_Lean_mkConst(v_instDeclName_180_, v___x_185_);
v___x_188_ = l_Lean_Expr_app___override(v___x_187_, v_type_178_);
v___x_189_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_176_, v_inst_175_, v_inst_177_, v___x_188_);
v___x_190_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_189_, v___f_186_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object* v_m_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_type_196_, lean_object* v_u_197_, lean_object* v_instDeclName_198_, lean_object* v_declName_199_, lean_object* v_expectedInst_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_192_, v_inst_193_, v_inst_194_, v_inst_195_, v_type_196_, v_u_197_, v_instDeclName_198_, v_declName_199_, v_expectedInst_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_202_, lean_object* v_declName_203_, lean_object* v___x_204_, lean_object* v_type_205_, lean_object* v_inst_206_, lean_object* v_____r_207_){
_start:
{
lean_object* v_canonExpr_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_canonExpr_208_ = lean_ctor_get(v_inst_202_, 0);
lean_inc(v_canonExpr_208_);
lean_dec_ref(v_inst_202_);
v___x_209_ = l_Lean_mkConst(v_declName_203_, v___x_204_);
lean_inc_ref_n(v_type_205_, 2);
v___x_210_ = l_Lean_mkApp4(v___x_209_, v_type_205_, v_type_205_, v_type_205_, v_inst_206_);
v___x_211_ = lean_apply_1(v_canonExpr_208_, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_212_, lean_object* v_declName_213_, lean_object* v___x_214_, lean_object* v_type_215_, lean_object* v_expectedInst_216_, lean_object* v_inst_217_, lean_object* v_toBind_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_inc_ref(v_inst_219_);
lean_inc(v_declName_213_);
v___f_220_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_220_, 0, v_inst_212_);
lean_closure_set(v___f_220_, 1, v_declName_213_);
lean_closure_set(v___f_220_, 2, v___x_214_);
lean_closure_set(v___f_220_, 3, v_type_215_);
lean_closure_set(v___f_220_, 4, v_inst_219_);
v___x_221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_221_, 0, v_declName_213_);
lean_closure_set(v___x_221_, 1, v_inst_219_);
lean_closure_set(v___x_221_, 2, v_expectedInst_216_);
v___x_222_ = lean_apply_2(v_inst_217_, lean_box(0), v___x_221_);
v___x_223_ = lean_apply_4(v_toBind_218_, lean_box(0), lean_box(0), v___x_222_, v___f_220_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_type_228_, lean_object* v_u_229_, lean_object* v_instDeclName_230_, lean_object* v_declName_231_, lean_object* v_expectedInst_232_){
_start:
{
lean_object* v_toBind_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_toBind_233_ = lean_ctor_get(v_inst_226_, 1);
lean_inc_n(v_toBind_233_, 2);
v___x_234_ = lean_box(0);
lean_inc_n(v_u_229_, 2);
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v_u_229_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v_u_229_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v_u_229_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
lean_inc_ref_n(v_type_228_, 3);
lean_inc_ref(v___x_237_);
lean_inc_ref(v_inst_227_);
v___f_238_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_238_, 0, v_inst_227_);
lean_closure_set(v___f_238_, 1, v_declName_231_);
lean_closure_set(v___f_238_, 2, v___x_237_);
lean_closure_set(v___f_238_, 3, v_type_228_);
lean_closure_set(v___f_238_, 4, v_expectedInst_232_);
lean_closure_set(v___f_238_, 5, v_inst_224_);
lean_closure_set(v___f_238_, 6, v_toBind_233_);
v___x_239_ = l_Lean_mkConst(v_instDeclName_230_, v___x_237_);
v___x_240_ = l_Lean_mkApp3(v___x_239_, v_type_228_, v_type_228_, v_type_228_);
v___x_241_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_226_, v_inst_225_, v_inst_227_, v___x_240_);
v___x_242_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v___x_241_, v___f_238_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object* v_m_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_type_248_, lean_object* v_u_249_, lean_object* v_instDeclName_250_, lean_object* v_declName_251_, lean_object* v_expectedInst_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_244_, v_inst_245_, v_inst_246_, v_inst_247_, v_type_248_, v_u_249_, v_instDeclName_250_, v_declName_251_, v_expectedInst_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object* v_inst_254_, lean_object* v___x_255_, lean_object* v___x_256_, lean_object* v_type_257_, lean_object* v___x_258_, lean_object* v_inst_259_, lean_object* v_____r_260_){
_start:
{
lean_object* v_canonExpr_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_canonExpr_261_ = lean_ctor_get(v_inst_254_, 0);
lean_inc(v_canonExpr_261_);
lean_dec_ref(v_inst_254_);
v___x_262_ = l_Lean_mkConst(v___x_255_, v___x_256_);
lean_inc_ref(v_type_257_);
v___x_263_ = l_Lean_mkApp4(v___x_262_, v_type_257_, v___x_258_, v_type_257_, v_inst_259_);
v___x_264_ = lean_apply_1(v_canonExpr_261_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object* v___x_275_, lean_object* v_type_276_, lean_object* v_semiringInst_277_, lean_object* v___x_278_, lean_object* v_inst_279_, lean_object* v___x_280_, lean_object* v___x_281_, lean_object* v_inst_282_, lean_object* v_toBind_283_, lean_object* v_inst_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_inst_x27_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_285_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4));
v___x_286_ = l_Lean_mkConst(v___x_285_, v___x_275_);
lean_inc_ref(v_type_276_);
v_inst_x27_287_ = l_Lean_mkAppB(v___x_286_, v_type_276_, v_semiringInst_277_);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5));
v___x_289_ = l_Lean_Name_mkStr2(v___x_278_, v___x_288_);
lean_inc_ref(v_inst_284_);
lean_inc(v___x_289_);
v___f_290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_290_, 0, v_inst_279_);
lean_closure_set(v___f_290_, 1, v___x_289_);
lean_closure_set(v___f_290_, 2, v___x_280_);
lean_closure_set(v___f_290_, 3, v_type_276_);
lean_closure_set(v___f_290_, 4, v___x_281_);
lean_closure_set(v___f_290_, 5, v_inst_284_);
v___x_291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_291_, 0, v___x_289_);
lean_closure_set(v___x_291_, 1, v_inst_284_);
lean_closure_set(v___x_291_, 2, v_inst_x27_287_);
v___x_292_ = lean_apply_2(v_inst_282_, lean_box(0), v___x_291_);
v___x_293_ = lean_apply_4(v_toBind_283_, lean_box(0), lean_box(0), v___x_292_, v___f_290_);
return v___x_293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = l_Lean_Level_ofNat(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_u_303_, lean_object* v_type_304_, lean_object* v_semiringInst_305_){
_start:
{
lean_object* v_toBind_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_toBind_306_ = lean_ctor_get(v_inst_301_, 1);
lean_inc_n(v_toBind_306_, 2);
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0));
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1));
v___x_309_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_310_ = lean_box(0);
lean_inc(v_u_303_);
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v_u_303_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
lean_inc_ref(v___x_311_);
v___x_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_309_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v_u_303_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
lean_inc_ref(v___x_313_);
v___x_314_ = l_Lean_mkConst(v___x_308_, v___x_313_);
v___x_315_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_302_);
lean_inc_ref_n(v_type_304_, 2);
v___f_316_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_316_, 0, v___x_311_);
lean_closure_set(v___f_316_, 1, v_type_304_);
lean_closure_set(v___f_316_, 2, v_semiringInst_305_);
lean_closure_set(v___f_316_, 3, v___x_307_);
lean_closure_set(v___f_316_, 4, v_inst_302_);
lean_closure_set(v___f_316_, 5, v___x_313_);
lean_closure_set(v___f_316_, 6, v___x_315_);
lean_closure_set(v___f_316_, 7, v_inst_299_);
lean_closure_set(v___f_316_, 8, v_toBind_306_);
v___x_317_ = l_Lean_mkApp3(v___x_314_, v_type_304_, v___x_315_, v_type_304_);
v___x_318_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_301_, v_inst_300_, v_inst_302_, v___x_317_);
v___x_319_ = lean_apply_4(v_toBind_306_, lean_box(0), lean_box(0), v___x_318_, v___f_316_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object* v_m_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_u_325_, lean_object* v_type_326_, lean_object* v_semiringInst_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_321_, v_inst_322_, v_inst_323_, v_inst_324_, v_u_325_, v_type_326_, v_semiringInst_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object* v___x_329_, lean_object* v___x_330_, lean_object* v___x_331_, lean_object* v_type_332_, lean_object* v_canonExpr_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = l_Lean_Name_mkStr2(v___x_329_, v___x_330_);
v___x_336_ = l_Lean_mkConst(v___x_335_, v___x_331_);
v___x_337_ = l_Lean_mkAppB(v___x_336_, v_type_332_, v_inst_334_);
v___x_338_ = lean_apply_1(v_canonExpr_333_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object* v___f_339_, lean_object* v_inst_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_apply_1(v___f_339_, v_inst_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_342_, lean_object* v_val_343_, lean_object* v_toBind_344_, lean_object* v___f_345_, lean_object* v_____r_346_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_apply_2(v_toPure_342_, lean_box(0), v_val_343_);
v___x_348_ = lean_apply_4(v_toBind_344_, lean_box(0), lean_box(0), v___x_347_, v___f_345_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_349_, lean_object* v_inst_x27_350_, lean_object* v_toBind_351_, lean_object* v___f_352_, lean_object* v___f_353_, lean_object* v___x_354_, lean_object* v___x_355_, lean_object* v_inst_356_, lean_object* v_____do__lift_357_){
_start:
{
if (lean_obj_tag(v_____do__lift_357_) == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_inst_356_);
lean_dec_ref(v___x_355_);
lean_dec_ref(v___x_354_);
lean_dec(v___f_353_);
v___x_358_ = lean_apply_2(v_toPure_349_, lean_box(0), v_inst_x27_350_);
v___x_359_ = lean_apply_4(v_toBind_351_, lean_box(0), lean_box(0), v___x_358_, v___f_352_);
return v___x_359_;
}
else
{
lean_object* v_val_360_; lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v___f_352_);
v_val_360_ = lean_ctor_get(v_____do__lift_357_, 0);
lean_inc_n(v_val_360_, 2);
lean_dec_ref_known(v_____do__lift_357_, 1);
lean_inc(v_toBind_351_);
v___f_361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_361_, 0, v_toPure_349_);
lean_closure_set(v___f_361_, 1, v_val_360_);
lean_closure_set(v___f_361_, 2, v_toBind_351_);
lean_closure_set(v___f_361_, 3, v___f_353_);
v___x_362_ = l_Lean_Name_mkStr2(v___x_354_, v___x_355_);
v___x_363_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_363_, 0, v___x_362_);
lean_closure_set(v___x_363_, 1, v_val_360_);
lean_closure_set(v___x_363_, 2, v_inst_x27_350_);
v___x_364_ = lean_apply_2(v_inst_356_, lean_box(0), v___x_363_);
v___x_365_ = lean_apply_4(v_toBind_351_, lean_box(0), lean_box(0), v___x_364_, v___f_361_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_u_378_, lean_object* v_type_379_, lean_object* v_semiringInst_380_){
_start:
{
lean_object* v_toApplicative_381_; lean_object* v_toBind_382_; lean_object* v_canonExpr_383_; lean_object* v_synthInstance_x3f_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_406_; 
v_toApplicative_381_ = lean_ctor_get(v_inst_376_, 0);
lean_inc_ref(v_toApplicative_381_);
v_toBind_382_ = lean_ctor_get(v_inst_376_, 1);
lean_inc(v_toBind_382_);
lean_dec_ref(v_inst_376_);
v_canonExpr_383_ = lean_ctor_get(v_inst_377_, 0);
v_synthInstance_x3f_384_ = lean_ctor_get(v_inst_377_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_inst_377_);
if (v_isSharedCheck_406_ == 0)
{
v___x_386_ = v_inst_377_;
v_isShared_387_ = v_isSharedCheck_406_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_synthInstance_x3f_384_);
lean_inc(v_canonExpr_383_);
lean_dec(v_inst_377_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_406_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_toPure_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v_toPure_388_ = lean_ctor_get(v_toApplicative_381_, 1);
lean_inc(v_toPure_388_);
lean_dec_ref(v_toApplicative_381_);
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0));
v___x_390_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1));
v___x_391_ = lean_box(0);
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 1);
lean_ctor_set(v___x_386_, 1, v___x_391_);
lean_ctor_set(v___x_386_, 0, v_u_378_);
v___x_393_ = v___x_386_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_u_378_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_391_);
v___x_393_ = v_reuseFailAlloc_405_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v_inst_x27_395_; lean_object* v___x_396_; lean_object* v___f_397_; lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_instType_401_; lean_object* v___x_402_; lean_object* v___f_403_; lean_object* v___x_404_; 
lean_inc_ref_n(v___x_393_, 2);
v___x_394_ = l_Lean_mkConst(v___x_390_, v___x_393_);
lean_inc_ref_n(v_type_379_, 2);
v_inst_x27_395_ = l_Lean_mkAppB(v___x_394_, v_type_379_, v_semiringInst_380_);
v___x_396_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2));
v___f_397_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_397_, 0, v___x_396_);
lean_closure_set(v___f_397_, 1, v___x_389_);
lean_closure_set(v___f_397_, 2, v___x_393_);
lean_closure_set(v___f_397_, 3, v_type_379_);
lean_closure_set(v___f_397_, 4, v_canonExpr_383_);
v___f_398_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_398_, 0, v___f_397_);
v___x_399_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3));
v___x_400_ = l_Lean_mkConst(v___x_399_, v___x_393_);
v_instType_401_ = l_Lean_Expr_app___override(v___x_400_, v_type_379_);
v___x_402_ = lean_apply_1(v_synthInstance_x3f_384_, v_instType_401_);
lean_inc_ref(v___f_398_);
lean_inc(v_toBind_382_);
v___f_403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_403_, 0, v_toPure_388_);
lean_closure_set(v___f_403_, 1, v_inst_x27_395_);
lean_closure_set(v___f_403_, 2, v_toBind_382_);
lean_closure_set(v___f_403_, 3, v___f_398_);
lean_closure_set(v___f_403_, 4, v___f_398_);
lean_closure_set(v___f_403_, 5, v___x_396_);
lean_closure_set(v___f_403_, 6, v___x_389_);
lean_closure_set(v___f_403_, 7, v_inst_375_);
v___x_404_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v___x_402_, v___f_403_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object* v_m_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_u_411_, lean_object* v_type_412_, lean_object* v_semiringInst_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_408_, v_inst_409_, v_inst_410_, v_u_411_, v_type_412_, v_semiringInst_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0(lean_object* v___x_416_, lean_object* v___x_417_, lean_object* v_scalar_418_, lean_object* v_type_419_, lean_object* v_canonExpr_420_, lean_object* v_inst_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0));
v___x_423_ = l_Lean_Name_mkStr2(v___x_416_, v___x_422_);
v___x_424_ = l_Lean_mkConst(v___x_423_, v___x_417_);
lean_inc_ref(v_type_419_);
v___x_425_ = l_Lean_mkApp4(v___x_424_, v_scalar_418_, v_type_419_, v_type_419_, v_inst_421_);
v___x_426_ = lean_apply_1(v_canonExpr_420_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4(lean_object* v_toPure_427_, lean_object* v_inst_x27_428_, lean_object* v_toBind_429_, lean_object* v___f_430_, lean_object* v___f_431_, lean_object* v___x_432_, lean_object* v_inst_433_, lean_object* v_____do__lift_434_){
_start:
{
if (lean_obj_tag(v_____do__lift_434_) == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_inst_433_);
lean_dec_ref(v___x_432_);
lean_dec(v___f_431_);
v___x_435_ = lean_apply_2(v_toPure_427_, lean_box(0), v_inst_x27_428_);
v___x_436_ = lean_apply_4(v_toBind_429_, lean_box(0), lean_box(0), v___x_435_, v___f_430_);
return v___x_436_;
}
else
{
lean_object* v_val_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v___f_430_);
v_val_437_ = lean_ctor_get(v_____do__lift_434_, 0);
lean_inc_n(v_val_437_, 2);
lean_dec_ref_known(v_____do__lift_434_, 1);
lean_inc(v_toBind_429_);
v___f_438_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_438_, 0, v_toPure_427_);
lean_closure_set(v___f_438_, 1, v_val_437_);
lean_closure_set(v___f_438_, 2, v_toBind_429_);
lean_closure_set(v___f_438_, 3, v___f_431_);
v___x_439_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0));
v___x_440_ = l_Lean_Name_mkStr2(v___x_432_, v___x_439_);
v___x_441_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_441_, 0, v___x_440_);
lean_closure_set(v___x_441_, 1, v_val_437_);
lean_closure_set(v___x_441_, 2, v_inst_x27_428_);
v___x_442_ = lean_apply_2(v_inst_433_, lean_box(0), v___x_441_);
v___x_443_ = lean_apply_4(v_toBind_429_, lean_box(0), lean_box(0), v___x_442_, v___f_438_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_u_453_, lean_object* v_type_454_, lean_object* v_scalar_455_, lean_object* v_expectedSMulInst_456_){
_start:
{
lean_object* v_toApplicative_457_; lean_object* v_toBind_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_491_; 
v_toApplicative_457_ = lean_ctor_get(v_inst_451_, 0);
v_toBind_458_ = lean_ctor_get(v_inst_451_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v_inst_451_);
if (v_isSharedCheck_491_ == 0)
{
v___x_460_ = v_inst_451_;
v_isShared_461_ = v_isSharedCheck_491_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_toBind_458_);
lean_inc(v_toApplicative_457_);
lean_dec(v_inst_451_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_491_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_canonExpr_462_; lean_object* v_synthInstance_x3f_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_490_; 
v_canonExpr_462_ = lean_ctor_get(v_inst_452_, 0);
v_synthInstance_x3f_463_ = lean_ctor_get(v_inst_452_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_inst_452_);
if (v_isSharedCheck_490_ == 0)
{
v___x_465_ = v_inst_452_;
v_isShared_466_ = v_isSharedCheck_490_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_synthInstance_x3f_463_);
lean_inc(v_canonExpr_462_);
lean_dec(v_inst_452_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_490_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_467_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1));
v___x_468_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_469_ = lean_box(0);
lean_inc(v_u_453_);
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 1);
lean_ctor_set(v___x_465_, 1, v___x_469_);
lean_ctor_set(v___x_465_, 0, v_u_453_);
v___x_471_ = v___x_465_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_u_453_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_489_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
lean_inc_ref(v___x_471_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 1);
lean_ctor_set(v___x_460_, 1, v___x_471_);
lean_ctor_set(v___x_460_, 0, v___x_468_);
v___x_473_ = v___x_460_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_488_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v_inst_x27_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_toPure_482_; lean_object* v___f_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___f_486_; lean_object* v___x_487_; 
v___x_474_ = l_Lean_mkConst(v___x_467_, v___x_473_);
lean_inc_ref_n(v_type_454_, 3);
lean_inc_ref_n(v_scalar_455_, 2);
v_inst_x27_475_ = l_Lean_mkApp3(v___x_474_, v_scalar_455_, v_type_454_, v_expectedSMulInst_456_);
v___x_476_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2));
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3));
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v_u_453_);
lean_ctor_set(v___x_478_, 1, v___x_471_);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_468_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
lean_inc_ref(v___x_479_);
v___x_480_ = l_Lean_mkConst(v___x_477_, v___x_479_);
v___x_481_ = l_Lean_mkApp3(v___x_480_, v_scalar_455_, v_type_454_, v_type_454_);
v_toPure_482_ = lean_ctor_get(v_toApplicative_457_, 1);
lean_inc(v_toPure_482_);
lean_dec_ref(v_toApplicative_457_);
v___f_483_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_483_, 0, v___x_476_);
lean_closure_set(v___f_483_, 1, v___x_479_);
lean_closure_set(v___f_483_, 2, v_scalar_455_);
lean_closure_set(v___f_483_, 3, v_type_454_);
lean_closure_set(v___f_483_, 4, v_canonExpr_462_);
v___f_484_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_484_, 0, v___f_483_);
v___x_485_ = lean_apply_1(v_synthInstance_x3f_463_, v___x_481_);
lean_inc_ref(v___f_484_);
lean_inc(v_toBind_458_);
v___f_486_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4), 8, 7);
lean_closure_set(v___f_486_, 0, v_toPure_482_);
lean_closure_set(v___f_486_, 1, v_inst_x27_475_);
lean_closure_set(v___f_486_, 2, v_toBind_458_);
lean_closure_set(v___f_486_, 3, v___f_484_);
lean_closure_set(v___f_486_, 4, v___f_484_);
lean_closure_set(v___f_486_, 5, v___x_476_);
lean_closure_set(v___f_486_, 6, v_inst_450_);
v___x_487_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v___x_485_, v___f_486_);
return v___x_487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn(lean_object* v_m_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_u_496_, lean_object* v_type_497_, lean_object* v_scalar_498_, lean_object* v_expectedSMulInst_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_493_, v_inst_494_, v_inst_495_, v_u_496_, v_type_497_, v_scalar_498_, v_expectedSMulInst_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0(lean_object* v_fn_501_, lean_object* v_s_502_){
_start:
{
lean_object* v_id_503_; lean_object* v_type_504_; lean_object* v_u_505_; lean_object* v_ringInst_506_; lean_object* v_semiringInst_507_; lean_object* v_charInst_x3f_508_; lean_object* v_addFn_x3f_509_; lean_object* v_mulFn_x3f_510_; lean_object* v_subFn_x3f_511_; lean_object* v_negFn_x3f_512_; lean_object* v_powFn_x3f_513_; lean_object* v_intCastFn_x3f_514_; lean_object* v_natCastFn_x3f_515_; lean_object* v_intSMulFn_x3f_516_; lean_object* v_one_x3f_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_id_503_ = lean_ctor_get(v_s_502_, 0);
v_type_504_ = lean_ctor_get(v_s_502_, 1);
v_u_505_ = lean_ctor_get(v_s_502_, 2);
v_ringInst_506_ = lean_ctor_get(v_s_502_, 3);
v_semiringInst_507_ = lean_ctor_get(v_s_502_, 4);
v_charInst_x3f_508_ = lean_ctor_get(v_s_502_, 5);
v_addFn_x3f_509_ = lean_ctor_get(v_s_502_, 6);
v_mulFn_x3f_510_ = lean_ctor_get(v_s_502_, 7);
v_subFn_x3f_511_ = lean_ctor_get(v_s_502_, 8);
v_negFn_x3f_512_ = lean_ctor_get(v_s_502_, 9);
v_powFn_x3f_513_ = lean_ctor_get(v_s_502_, 10);
v_intCastFn_x3f_514_ = lean_ctor_get(v_s_502_, 11);
v_natCastFn_x3f_515_ = lean_ctor_get(v_s_502_, 12);
v_intSMulFn_x3f_516_ = lean_ctor_get(v_s_502_, 14);
v_one_x3f_517_ = lean_ctor_get(v_s_502_, 15);
v_isSharedCheck_525_ = !lean_is_exclusive(v_s_502_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v_s_502_, 13);
lean_dec(v_unused_526_);
v___x_519_ = v_s_502_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_one_x3f_517_);
lean_inc(v_intSMulFn_x3f_516_);
lean_inc(v_natCastFn_x3f_515_);
lean_inc(v_intCastFn_x3f_514_);
lean_inc(v_powFn_x3f_513_);
lean_inc(v_negFn_x3f_512_);
lean_inc(v_subFn_x3f_511_);
lean_inc(v_mulFn_x3f_510_);
lean_inc(v_addFn_x3f_509_);
lean_inc(v_charInst_x3f_508_);
lean_inc(v_semiringInst_507_);
lean_inc(v_ringInst_506_);
lean_inc(v_u_505_);
lean_inc(v_type_504_);
lean_inc(v_id_503_);
lean_dec(v_s_502_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_fn_501_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 13, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_id_503_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_type_504_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_u_505_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_ringInst_506_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_semiringInst_507_);
lean_ctor_set(v_reuseFailAlloc_524_, 5, v_charInst_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_524_, 6, v_addFn_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_524_, 7, v_mulFn_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_524_, 8, v_subFn_x3f_511_);
lean_ctor_set(v_reuseFailAlloc_524_, 9, v_negFn_x3f_512_);
lean_ctor_set(v_reuseFailAlloc_524_, 10, v_powFn_x3f_513_);
lean_ctor_set(v_reuseFailAlloc_524_, 11, v_intCastFn_x3f_514_);
lean_ctor_set(v_reuseFailAlloc_524_, 12, v_natCastFn_x3f_515_);
lean_ctor_set(v_reuseFailAlloc_524_, 13, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_524_, 14, v_intSMulFn_x3f_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 15, v_one_x3f_517_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1(lean_object* v_toPure_527_, lean_object* v_fn_528_, lean_object* v_____r_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_apply_2(v_toPure_527_, lean_box(0), v_fn_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2(lean_object* v_toPure_531_, lean_object* v_modifyRing_532_, lean_object* v_toBind_533_, lean_object* v_fn_534_){
_start:
{
lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_inc_ref(v_fn_534_);
v___f_535_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_535_, 0, v_fn_534_);
v___f_536_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_536_, 0, v_toPure_531_);
lean_closure_set(v___f_536_, 1, v_fn_534_);
v___x_537_ = lean_apply_1(v_modifyRing_532_, v___f_535_);
v___x_538_ = lean_apply_4(v_toBind_533_, lean_box(0), lean_box(0), v___x_537_, v___f_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3(lean_object* v_toPure_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_toBind_549_, lean_object* v___f_550_, lean_object* v_ring_551_){
_start:
{
lean_object* v_natSMulFn_x3f_552_; 
v_natSMulFn_x3f_552_ = lean_ctor_get(v_ring_551_, 13);
if (lean_obj_tag(v_natSMulFn_x3f_552_) == 1)
{
lean_object* v_val_553_; lean_object* v___x_554_; 
lean_inc_ref(v_natSMulFn_x3f_552_);
lean_dec_ref(v_ring_551_);
lean_dec(v___f_550_);
lean_dec(v_toBind_549_);
lean_dec_ref(v_inst_548_);
lean_dec_ref(v_inst_547_);
lean_dec(v_inst_546_);
v_val_553_ = lean_ctor_get(v_natSMulFn_x3f_552_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v_natSMulFn_x3f_552_, 1);
v___x_554_ = lean_apply_2(v_toPure_545_, lean_box(0), v_val_553_);
return v___x_554_;
}
else
{
lean_object* v_type_555_; lean_object* v_u_556_; lean_object* v_semiringInst_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_toPure_545_);
v_type_555_ = lean_ctor_get(v_ring_551_, 1);
lean_inc_ref_n(v_type_555_, 2);
v_u_556_ = lean_ctor_get(v_ring_551_, 2);
lean_inc_n(v_u_556_, 2);
v_semiringInst_557_ = lean_ctor_get(v_ring_551_, 4);
lean_inc_ref(v_semiringInst_557_);
lean_dec_ref(v_ring_551_);
v___x_558_ = l_Lean_Nat_mkType;
v___x_559_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v_u_556_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_mkConst(v___x_559_, v___x_561_);
v___x_563_ = l_Lean_mkAppB(v___x_562_, v_type_555_, v_semiringInst_557_);
v___x_564_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_546_, v_inst_547_, v_inst_548_, v_u_556_, v_type_555_, v___x_558_, v___x_563_);
v___x_565_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v___x_564_, v___f_550_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_){
_start:
{
lean_object* v_toApplicative_570_; lean_object* v_toBind_571_; lean_object* v_getRing_572_; lean_object* v_modifyRing_573_; lean_object* v_toPure_574_; lean_object* v___f_575_; lean_object* v___f_576_; lean_object* v___x_577_; 
v_toApplicative_570_ = lean_ctor_get(v_inst_567_, 0);
v_toBind_571_ = lean_ctor_get(v_inst_567_, 1);
lean_inc_n(v_toBind_571_, 3);
v_getRing_572_ = lean_ctor_get(v_inst_569_, 0);
lean_inc(v_getRing_572_);
v_modifyRing_573_ = lean_ctor_get(v_inst_569_, 1);
lean_inc(v_modifyRing_573_);
lean_dec_ref(v_inst_569_);
v_toPure_574_ = lean_ctor_get(v_toApplicative_570_, 1);
lean_inc_n(v_toPure_574_, 2);
v___f_575_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_575_, 0, v_toPure_574_);
lean_closure_set(v___f_575_, 1, v_modifyRing_573_);
lean_closure_set(v___f_575_, 2, v_toBind_571_);
v___f_576_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_576_, 0, v_toPure_574_);
lean_closure_set(v___f_576_, 1, v_inst_566_);
lean_closure_set(v___f_576_, 2, v_inst_567_);
lean_closure_set(v___f_576_, 3, v_inst_568_);
lean_closure_set(v___f_576_, 4, v_toBind_571_);
lean_closure_set(v___f_576_, 5, v___f_575_);
v___x_577_ = lean_apply_4(v_toBind_571_, lean_box(0), lean_box(0), v_getRing_572_, v___f_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn(lean_object* v_m_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(v_inst_579_, v_inst_580_, v_inst_581_, v_inst_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0(lean_object* v_fn_584_, lean_object* v_s_585_){
_start:
{
lean_object* v_id_586_; lean_object* v_type_587_; lean_object* v_u_588_; lean_object* v_ringInst_589_; lean_object* v_semiringInst_590_; lean_object* v_charInst_x3f_591_; lean_object* v_addFn_x3f_592_; lean_object* v_mulFn_x3f_593_; lean_object* v_subFn_x3f_594_; lean_object* v_negFn_x3f_595_; lean_object* v_powFn_x3f_596_; lean_object* v_intCastFn_x3f_597_; lean_object* v_natCastFn_x3f_598_; lean_object* v_natSMulFn_x3f_599_; lean_object* v_one_x3f_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v_id_586_ = lean_ctor_get(v_s_585_, 0);
v_type_587_ = lean_ctor_get(v_s_585_, 1);
v_u_588_ = lean_ctor_get(v_s_585_, 2);
v_ringInst_589_ = lean_ctor_get(v_s_585_, 3);
v_semiringInst_590_ = lean_ctor_get(v_s_585_, 4);
v_charInst_x3f_591_ = lean_ctor_get(v_s_585_, 5);
v_addFn_x3f_592_ = lean_ctor_get(v_s_585_, 6);
v_mulFn_x3f_593_ = lean_ctor_get(v_s_585_, 7);
v_subFn_x3f_594_ = lean_ctor_get(v_s_585_, 8);
v_negFn_x3f_595_ = lean_ctor_get(v_s_585_, 9);
v_powFn_x3f_596_ = lean_ctor_get(v_s_585_, 10);
v_intCastFn_x3f_597_ = lean_ctor_get(v_s_585_, 11);
v_natCastFn_x3f_598_ = lean_ctor_get(v_s_585_, 12);
v_natSMulFn_x3f_599_ = lean_ctor_get(v_s_585_, 13);
v_one_x3f_600_ = lean_ctor_get(v_s_585_, 15);
v_isSharedCheck_608_ = !lean_is_exclusive(v_s_585_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v_s_585_, 14);
lean_dec(v_unused_609_);
v___x_602_ = v_s_585_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_one_x3f_600_);
lean_inc(v_natSMulFn_x3f_599_);
lean_inc(v_natCastFn_x3f_598_);
lean_inc(v_intCastFn_x3f_597_);
lean_inc(v_powFn_x3f_596_);
lean_inc(v_negFn_x3f_595_);
lean_inc(v_subFn_x3f_594_);
lean_inc(v_mulFn_x3f_593_);
lean_inc(v_addFn_x3f_592_);
lean_inc(v_charInst_x3f_591_);
lean_inc(v_semiringInst_590_);
lean_inc(v_ringInst_589_);
lean_inc(v_u_588_);
lean_inc(v_type_587_);
lean_inc(v_id_586_);
lean_dec(v_s_585_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v_fn_584_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 14, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_id_586_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_type_587_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_u_588_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_ringInst_589_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_semiringInst_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 5, v_charInst_x3f_591_);
lean_ctor_set(v_reuseFailAlloc_607_, 6, v_addFn_x3f_592_);
lean_ctor_set(v_reuseFailAlloc_607_, 7, v_mulFn_x3f_593_);
lean_ctor_set(v_reuseFailAlloc_607_, 8, v_subFn_x3f_594_);
lean_ctor_set(v_reuseFailAlloc_607_, 9, v_negFn_x3f_595_);
lean_ctor_set(v_reuseFailAlloc_607_, 10, v_powFn_x3f_596_);
lean_ctor_set(v_reuseFailAlloc_607_, 11, v_intCastFn_x3f_597_);
lean_ctor_set(v_reuseFailAlloc_607_, 12, v_natCastFn_x3f_598_);
lean_ctor_set(v_reuseFailAlloc_607_, 13, v_natSMulFn_x3f_599_);
lean_ctor_set(v_reuseFailAlloc_607_, 14, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 15, v_one_x3f_600_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2(lean_object* v_toPure_610_, lean_object* v_modifyRing_611_, lean_object* v_toBind_612_, lean_object* v_fn_613_){
_start:
{
lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_inc_ref(v_fn_613_);
v___f_614_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_614_, 0, v_fn_613_);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_615_, 0, v_toPure_610_);
lean_closure_set(v___f_615_, 1, v_fn_613_);
v___x_616_ = lean_apply_1(v_modifyRing_611_, v___f_614_);
v___x_617_ = lean_apply_4(v_toBind_612_, lean_box(0), lean_box(0), v___x_616_, v___f_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1(lean_object* v_toPure_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_toBind_629_, lean_object* v___f_630_, lean_object* v_ring_631_){
_start:
{
lean_object* v_intSMulFn_x3f_632_; 
v_intSMulFn_x3f_632_ = lean_ctor_get(v_ring_631_, 14);
if (lean_obj_tag(v_intSMulFn_x3f_632_) == 1)
{
lean_object* v_val_633_; lean_object* v___x_634_; 
lean_inc_ref(v_intSMulFn_x3f_632_);
lean_dec_ref(v_ring_631_);
lean_dec(v___f_630_);
lean_dec(v_toBind_629_);
lean_dec_ref(v_inst_628_);
lean_dec_ref(v_inst_627_);
lean_dec(v_inst_626_);
v_val_633_ = lean_ctor_get(v_intSMulFn_x3f_632_, 0);
lean_inc(v_val_633_);
lean_dec_ref_known(v_intSMulFn_x3f_632_, 1);
v___x_634_ = lean_apply_2(v_toPure_625_, lean_box(0), v_val_633_);
return v___x_634_;
}
else
{
lean_object* v_type_635_; lean_object* v_u_636_; lean_object* v_ringInst_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_toPure_625_);
v_type_635_ = lean_ctor_get(v_ring_631_, 1);
lean_inc_ref_n(v_type_635_, 2);
v_u_636_ = lean_ctor_get(v_ring_631_, 2);
lean_inc_n(v_u_636_, 2);
v_ringInst_637_ = lean_ctor_get(v_ring_631_, 3);
lean_inc_ref(v_ringInst_637_);
lean_dec_ref(v_ring_631_);
v___x_638_ = l_Lean_Int_mkType;
v___x_639_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2));
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v_u_636_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_mkConst(v___x_639_, v___x_641_);
v___x_643_ = l_Lean_mkAppB(v___x_642_, v_type_635_, v_ringInst_637_);
v___x_644_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_626_, v_inst_627_, v_inst_628_, v_u_636_, v_type_635_, v___x_638_, v___x_643_);
v___x_645_ = lean_apply_4(v_toBind_629_, lean_box(0), lean_box(0), v___x_644_, v___f_630_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_){
_start:
{
lean_object* v_toApplicative_650_; lean_object* v_toBind_651_; lean_object* v_getRing_652_; lean_object* v_modifyRing_653_; lean_object* v_toPure_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___x_657_; 
v_toApplicative_650_ = lean_ctor_get(v_inst_647_, 0);
v_toBind_651_ = lean_ctor_get(v_inst_647_, 1);
lean_inc_n(v_toBind_651_, 3);
v_getRing_652_ = lean_ctor_get(v_inst_649_, 0);
lean_inc(v_getRing_652_);
v_modifyRing_653_ = lean_ctor_get(v_inst_649_, 1);
lean_inc(v_modifyRing_653_);
lean_dec_ref(v_inst_649_);
v_toPure_654_ = lean_ctor_get(v_toApplicative_650_, 1);
lean_inc_n(v_toPure_654_, 2);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_655_, 0, v_toPure_654_);
lean_closure_set(v___f_655_, 1, v_modifyRing_653_);
lean_closure_set(v___f_655_, 2, v_toBind_651_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1), 7, 6);
lean_closure_set(v___f_656_, 0, v_toPure_654_);
lean_closure_set(v___f_656_, 1, v_inst_646_);
lean_closure_set(v___f_656_, 2, v_inst_647_);
lean_closure_set(v___f_656_, 3, v_inst_648_);
lean_closure_set(v___f_656_, 4, v_toBind_651_);
lean_closure_set(v___f_656_, 5, v___f_655_);
v___x_657_ = lean_apply_4(v_toBind_651_, lean_box(0), lean_box(0), v_getRing_652_, v___f_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn(lean_object* v_m_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(v_inst_659_, v_inst_660_, v_inst_661_, v_inst_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_664_, lean_object* v_s_665_){
_start:
{
lean_object* v_id_666_; lean_object* v_type_667_; lean_object* v_u_668_; lean_object* v_ringInst_669_; lean_object* v_semiringInst_670_; lean_object* v_charInst_x3f_671_; lean_object* v_mulFn_x3f_672_; lean_object* v_subFn_x3f_673_; lean_object* v_negFn_x3f_674_; lean_object* v_powFn_x3f_675_; lean_object* v_intCastFn_x3f_676_; lean_object* v_natCastFn_x3f_677_; lean_object* v_natSMulFn_x3f_678_; lean_object* v_intSMulFn_x3f_679_; lean_object* v_one_x3f_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_688_; 
v_id_666_ = lean_ctor_get(v_s_665_, 0);
v_type_667_ = lean_ctor_get(v_s_665_, 1);
v_u_668_ = lean_ctor_get(v_s_665_, 2);
v_ringInst_669_ = lean_ctor_get(v_s_665_, 3);
v_semiringInst_670_ = lean_ctor_get(v_s_665_, 4);
v_charInst_x3f_671_ = lean_ctor_get(v_s_665_, 5);
v_mulFn_x3f_672_ = lean_ctor_get(v_s_665_, 7);
v_subFn_x3f_673_ = lean_ctor_get(v_s_665_, 8);
v_negFn_x3f_674_ = lean_ctor_get(v_s_665_, 9);
v_powFn_x3f_675_ = lean_ctor_get(v_s_665_, 10);
v_intCastFn_x3f_676_ = lean_ctor_get(v_s_665_, 11);
v_natCastFn_x3f_677_ = lean_ctor_get(v_s_665_, 12);
v_natSMulFn_x3f_678_ = lean_ctor_get(v_s_665_, 13);
v_intSMulFn_x3f_679_ = lean_ctor_get(v_s_665_, 14);
v_one_x3f_680_ = lean_ctor_get(v_s_665_, 15);
v_isSharedCheck_688_ = !lean_is_exclusive(v_s_665_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v_s_665_, 6);
lean_dec(v_unused_689_);
v___x_682_ = v_s_665_;
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_one_x3f_680_);
lean_inc(v_intSMulFn_x3f_679_);
lean_inc(v_natSMulFn_x3f_678_);
lean_inc(v_natCastFn_x3f_677_);
lean_inc(v_intCastFn_x3f_676_);
lean_inc(v_powFn_x3f_675_);
lean_inc(v_negFn_x3f_674_);
lean_inc(v_subFn_x3f_673_);
lean_inc(v_mulFn_x3f_672_);
lean_inc(v_charInst_x3f_671_);
lean_inc(v_semiringInst_670_);
lean_inc(v_ringInst_669_);
lean_inc(v_u_668_);
lean_inc(v_type_667_);
lean_inc(v_id_666_);
lean_dec(v_s_665_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v_addFn_664_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 6, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_id_666_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_type_667_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_u_668_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_ringInst_669_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_semiringInst_670_);
lean_ctor_set(v_reuseFailAlloc_687_, 5, v_charInst_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_687_, 6, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 7, v_mulFn_x3f_672_);
lean_ctor_set(v_reuseFailAlloc_687_, 8, v_subFn_x3f_673_);
lean_ctor_set(v_reuseFailAlloc_687_, 9, v_negFn_x3f_674_);
lean_ctor_set(v_reuseFailAlloc_687_, 10, v_powFn_x3f_675_);
lean_ctor_set(v_reuseFailAlloc_687_, 11, v_intCastFn_x3f_676_);
lean_ctor_set(v_reuseFailAlloc_687_, 12, v_natCastFn_x3f_677_);
lean_ctor_set(v_reuseFailAlloc_687_, 13, v_natSMulFn_x3f_678_);
lean_ctor_set(v_reuseFailAlloc_687_, 14, v_intSMulFn_x3f_679_);
lean_ctor_set(v_reuseFailAlloc_687_, 15, v_one_x3f_680_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_690_, lean_object* v_addFn_691_, lean_object* v_____r_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_apply_2(v_toPure_690_, lean_box(0), v_addFn_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_694_, lean_object* v_modifyRing_695_, lean_object* v_toBind_696_, lean_object* v_addFn_697_){
_start:
{
lean_object* v___f_698_; lean_object* v___f_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_inc_ref(v_addFn_697_);
v___f_698_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_698_, 0, v_addFn_697_);
v___f_699_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_699_, 0, v_toPure_694_);
lean_closure_set(v___f_699_, 1, v_addFn_697_);
v___x_700_ = lean_apply_1(v_modifyRing_695_, v___f_698_);
v___x_701_ = lean_apply_4(v_toBind_696_, lean_box(0), lean_box(0), v___x_700_, v___f_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_toBind_723_, lean_object* v___f_724_, lean_object* v_ring_725_){
_start:
{
lean_object* v_addFn_x3f_726_; 
v_addFn_x3f_726_ = lean_ctor_get(v_ring_725_, 6);
if (lean_obj_tag(v_addFn_x3f_726_) == 1)
{
lean_object* v_val_727_; lean_object* v___x_728_; 
lean_inc_ref(v_addFn_x3f_726_);
lean_dec_ref(v_ring_725_);
lean_dec(v___f_724_);
lean_dec(v_toBind_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_inst_721_);
lean_dec_ref(v_inst_720_);
lean_dec(v_inst_719_);
v_val_727_ = lean_ctor_get(v_addFn_x3f_726_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v_addFn_x3f_726_, 1);
v___x_728_ = lean_apply_2(v_toPure_718_, lean_box(0), v_val_727_);
return v___x_728_;
}
else
{
lean_object* v_type_729_; lean_object* v_u_730_; lean_object* v_semiringInst_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_expectedInst_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v_toPure_718_);
v_type_729_ = lean_ctor_get(v_ring_725_, 1);
lean_inc_ref_n(v_type_729_, 3);
v_u_730_ = lean_ctor_get(v_ring_725_, 2);
lean_inc_n(v_u_730_, 2);
v_semiringInst_731_ = lean_ctor_get(v_ring_725_, 4);
lean_inc_ref(v_semiringInst_731_);
lean_dec_ref(v_ring_725_);
v___x_732_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_733_ = lean_box(0);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v_u_730_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
lean_inc_ref(v___x_734_);
v___x_735_ = l_Lean_mkConst(v___x_732_, v___x_734_);
v___x_736_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_737_ = l_Lean_mkConst(v___x_736_, v___x_734_);
v___x_738_ = l_Lean_mkAppB(v___x_737_, v_type_729_, v_semiringInst_731_);
v_expectedInst_739_ = l_Lean_mkAppB(v___x_735_, v_type_729_, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_741_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_742_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_719_, v_inst_720_, v_inst_721_, v_inst_722_, v_type_729_, v_u_730_, v___x_740_, v___x_741_, v_expectedInst_739_);
v___x_743_ = lean_apply_4(v_toBind_723_, lean_box(0), lean_box(0), v___x_742_, v___f_724_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_inst_748_){
_start:
{
lean_object* v_toApplicative_749_; lean_object* v_toBind_750_; lean_object* v_getRing_751_; lean_object* v_modifyRing_752_; lean_object* v_toPure_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_756_; 
v_toApplicative_749_ = lean_ctor_get(v_inst_746_, 0);
v_toBind_750_ = lean_ctor_get(v_inst_746_, 1);
lean_inc_n(v_toBind_750_, 3);
v_getRing_751_ = lean_ctor_get(v_inst_748_, 0);
lean_inc(v_getRing_751_);
v_modifyRing_752_ = lean_ctor_get(v_inst_748_, 1);
lean_inc(v_modifyRing_752_);
lean_dec_ref(v_inst_748_);
v_toPure_753_ = lean_ctor_get(v_toApplicative_749_, 1);
lean_inc_n(v_toPure_753_, 2);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_754_, 0, v_toPure_753_);
lean_closure_set(v___f_754_, 1, v_modifyRing_752_);
lean_closure_set(v___f_754_, 2, v_toBind_750_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_755_, 0, v_toPure_753_);
lean_closure_set(v___f_755_, 1, v_inst_744_);
lean_closure_set(v___f_755_, 2, v_inst_745_);
lean_closure_set(v___f_755_, 3, v_inst_746_);
lean_closure_set(v___f_755_, 4, v_inst_747_);
lean_closure_set(v___f_755_, 5, v_toBind_750_);
lean_closure_set(v___f_755_, 6, v___f_754_);
v___x_756_ = lean_apply_4(v_toBind_750_, lean_box(0), lean_box(0), v_getRing_751_, v___f_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_inst_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_758_, v_inst_759_, v_inst_760_, v_inst_761_, v_inst_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_764_, lean_object* v_s_765_){
_start:
{
lean_object* v_id_766_; lean_object* v_type_767_; lean_object* v_u_768_; lean_object* v_ringInst_769_; lean_object* v_semiringInst_770_; lean_object* v_charInst_x3f_771_; lean_object* v_addFn_x3f_772_; lean_object* v_subFn_x3f_773_; lean_object* v_negFn_x3f_774_; lean_object* v_powFn_x3f_775_; lean_object* v_intCastFn_x3f_776_; lean_object* v_natCastFn_x3f_777_; lean_object* v_natSMulFn_x3f_778_; lean_object* v_intSMulFn_x3f_779_; lean_object* v_one_x3f_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_id_766_ = lean_ctor_get(v_s_765_, 0);
v_type_767_ = lean_ctor_get(v_s_765_, 1);
v_u_768_ = lean_ctor_get(v_s_765_, 2);
v_ringInst_769_ = lean_ctor_get(v_s_765_, 3);
v_semiringInst_770_ = lean_ctor_get(v_s_765_, 4);
v_charInst_x3f_771_ = lean_ctor_get(v_s_765_, 5);
v_addFn_x3f_772_ = lean_ctor_get(v_s_765_, 6);
v_subFn_x3f_773_ = lean_ctor_get(v_s_765_, 8);
v_negFn_x3f_774_ = lean_ctor_get(v_s_765_, 9);
v_powFn_x3f_775_ = lean_ctor_get(v_s_765_, 10);
v_intCastFn_x3f_776_ = lean_ctor_get(v_s_765_, 11);
v_natCastFn_x3f_777_ = lean_ctor_get(v_s_765_, 12);
v_natSMulFn_x3f_778_ = lean_ctor_get(v_s_765_, 13);
v_intSMulFn_x3f_779_ = lean_ctor_get(v_s_765_, 14);
v_one_x3f_780_ = lean_ctor_get(v_s_765_, 15);
v_isSharedCheck_788_ = !lean_is_exclusive(v_s_765_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_s_765_, 7);
lean_dec(v_unused_789_);
v___x_782_ = v_s_765_;
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
lean_inc(v_charInst_x3f_771_);
lean_inc(v_semiringInst_770_);
lean_inc(v_ringInst_769_);
lean_inc(v_u_768_);
lean_inc(v_type_767_);
lean_inc(v_id_766_);
lean_dec(v_s_765_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_mulFn_764_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 7, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_id_766_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_type_767_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_u_768_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_ringInst_769_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_semiringInst_770_);
lean_ctor_set(v_reuseFailAlloc_787_, 5, v_charInst_x3f_771_);
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
lean_object* v_id_866_; lean_object* v_type_867_; lean_object* v_u_868_; lean_object* v_ringInst_869_; lean_object* v_semiringInst_870_; lean_object* v_charInst_x3f_871_; lean_object* v_addFn_x3f_872_; lean_object* v_mulFn_x3f_873_; lean_object* v_negFn_x3f_874_; lean_object* v_powFn_x3f_875_; lean_object* v_intCastFn_x3f_876_; lean_object* v_natCastFn_x3f_877_; lean_object* v_natSMulFn_x3f_878_; lean_object* v_intSMulFn_x3f_879_; lean_object* v_one_x3f_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_id_866_ = lean_ctor_get(v_s_865_, 0);
v_type_867_ = lean_ctor_get(v_s_865_, 1);
v_u_868_ = lean_ctor_get(v_s_865_, 2);
v_ringInst_869_ = lean_ctor_get(v_s_865_, 3);
v_semiringInst_870_ = lean_ctor_get(v_s_865_, 4);
v_charInst_x3f_871_ = lean_ctor_get(v_s_865_, 5);
v_addFn_x3f_872_ = lean_ctor_get(v_s_865_, 6);
v_mulFn_x3f_873_ = lean_ctor_get(v_s_865_, 7);
v_negFn_x3f_874_ = lean_ctor_get(v_s_865_, 9);
v_powFn_x3f_875_ = lean_ctor_get(v_s_865_, 10);
v_intCastFn_x3f_876_ = lean_ctor_get(v_s_865_, 11);
v_natCastFn_x3f_877_ = lean_ctor_get(v_s_865_, 12);
v_natSMulFn_x3f_878_ = lean_ctor_get(v_s_865_, 13);
v_intSMulFn_x3f_879_ = lean_ctor_get(v_s_865_, 14);
v_one_x3f_880_ = lean_ctor_get(v_s_865_, 15);
v_isSharedCheck_888_ = !lean_is_exclusive(v_s_865_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_s_865_, 8);
lean_dec(v_unused_889_);
v___x_882_ = v_s_865_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_one_x3f_880_);
lean_inc(v_intSMulFn_x3f_879_);
lean_inc(v_natSMulFn_x3f_878_);
lean_inc(v_natCastFn_x3f_877_);
lean_inc(v_intCastFn_x3f_876_);
lean_inc(v_powFn_x3f_875_);
lean_inc(v_negFn_x3f_874_);
lean_inc(v_mulFn_x3f_873_);
lean_inc(v_addFn_x3f_872_);
lean_inc(v_charInst_x3f_871_);
lean_inc(v_semiringInst_870_);
lean_inc(v_ringInst_869_);
lean_inc(v_u_868_);
lean_inc(v_type_867_);
lean_inc(v_id_866_);
lean_dec(v_s_865_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v_subFn_864_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 8, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_id_866_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_type_867_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_u_868_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v_ringInst_869_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_semiringInst_870_);
lean_ctor_set(v_reuseFailAlloc_887_, 5, v_charInst_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_887_, 6, v_addFn_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_887_, 7, v_mulFn_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_887_, 8, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 9, v_negFn_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_887_, 10, v_powFn_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_887_, 11, v_intCastFn_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 12, v_natCastFn_x3f_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 13, v_natSMulFn_x3f_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 14, v_intSMulFn_x3f_879_);
lean_ctor_set(v_reuseFailAlloc_887_, 15, v_one_x3f_880_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_890_, lean_object* v_subFn_891_, lean_object* v_____r_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_apply_2(v_toPure_890_, lean_box(0), v_subFn_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_894_, lean_object* v_modifyRing_895_, lean_object* v_toBind_896_, lean_object* v_subFn_897_){
_start:
{
lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_inc_ref(v_subFn_897_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_898_, 0, v_subFn_897_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_899_, 0, v_toPure_894_);
lean_closure_set(v___f_899_, 1, v_subFn_897_);
v___x_900_ = lean_apply_1(v_modifyRing_895_, v___f_898_);
v___x_901_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_900_, v___f_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_toBind_923_, lean_object* v___f_924_, lean_object* v_ring_925_){
_start:
{
lean_object* v_subFn_x3f_926_; 
v_subFn_x3f_926_ = lean_ctor_get(v_ring_925_, 8);
if (lean_obj_tag(v_subFn_x3f_926_) == 1)
{
lean_object* v_val_927_; lean_object* v___x_928_; 
lean_inc_ref(v_subFn_x3f_926_);
lean_dec_ref(v_ring_925_);
lean_dec(v___f_924_);
lean_dec(v_toBind_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_inst_921_);
lean_dec_ref(v_inst_920_);
lean_dec(v_inst_919_);
v_val_927_ = lean_ctor_get(v_subFn_x3f_926_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v_subFn_x3f_926_, 1);
v___x_928_ = lean_apply_2(v_toPure_918_, lean_box(0), v_val_927_);
return v___x_928_;
}
else
{
lean_object* v_type_929_; lean_object* v_u_930_; lean_object* v_ringInst_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_expectedInst_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_toPure_918_);
v_type_929_ = lean_ctor_get(v_ring_925_, 1);
lean_inc_ref_n(v_type_929_, 3);
v_u_930_ = lean_ctor_get(v_ring_925_, 2);
lean_inc_n(v_u_930_, 2);
v_ringInst_931_ = lean_ctor_get(v_ring_925_, 3);
lean_inc_ref(v_ringInst_931_);
lean_dec_ref(v_ring_925_);
v___x_932_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_933_ = lean_box(0);
v___x_934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_934_, 0, v_u_930_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_inc_ref(v___x_934_);
v___x_935_ = l_Lean_mkConst(v___x_932_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3));
v___x_937_ = l_Lean_mkConst(v___x_936_, v___x_934_);
v___x_938_ = l_Lean_mkAppB(v___x_937_, v_type_929_, v_ringInst_931_);
v_expectedInst_939_ = l_Lean_mkAppB(v___x_935_, v_type_929_, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5));
v___x_941_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7));
v___x_942_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_919_, v_inst_920_, v_inst_921_, v_inst_922_, v_type_929_, v_u_930_, v___x_940_, v___x_941_, v_expectedInst_939_);
v___x_943_ = lean_apply_4(v_toBind_923_, lean_box(0), lean_box(0), v___x_942_, v___f_924_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_inst_948_){
_start:
{
lean_object* v_toApplicative_949_; lean_object* v_toBind_950_; lean_object* v_getRing_951_; lean_object* v_modifyRing_952_; lean_object* v_toPure_953_; lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v___x_956_; 
v_toApplicative_949_ = lean_ctor_get(v_inst_946_, 0);
v_toBind_950_ = lean_ctor_get(v_inst_946_, 1);
lean_inc_n(v_toBind_950_, 3);
v_getRing_951_ = lean_ctor_get(v_inst_948_, 0);
lean_inc(v_getRing_951_);
v_modifyRing_952_ = lean_ctor_get(v_inst_948_, 1);
lean_inc(v_modifyRing_952_);
lean_dec_ref(v_inst_948_);
v_toPure_953_ = lean_ctor_get(v_toApplicative_949_, 1);
lean_inc_n(v_toPure_953_, 2);
v___f_954_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_954_, 0, v_toPure_953_);
lean_closure_set(v___f_954_, 1, v_modifyRing_952_);
lean_closure_set(v___f_954_, 2, v_toBind_950_);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_955_, 0, v_toPure_953_);
lean_closure_set(v___f_955_, 1, v_inst_944_);
lean_closure_set(v___f_955_, 2, v_inst_945_);
lean_closure_set(v___f_955_, 3, v_inst_946_);
lean_closure_set(v___f_955_, 4, v_inst_947_);
lean_closure_set(v___f_955_, 5, v_toBind_950_);
lean_closure_set(v___f_955_, 6, v___f_954_);
v___x_956_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v_getRing_951_, v___f_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_inst_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_958_, v_inst_959_, v_inst_960_, v_inst_961_, v_inst_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_964_, lean_object* v_s_965_){
_start:
{
lean_object* v_id_966_; lean_object* v_type_967_; lean_object* v_u_968_; lean_object* v_ringInst_969_; lean_object* v_semiringInst_970_; lean_object* v_charInst_x3f_971_; lean_object* v_addFn_x3f_972_; lean_object* v_mulFn_x3f_973_; lean_object* v_subFn_x3f_974_; lean_object* v_powFn_x3f_975_; lean_object* v_intCastFn_x3f_976_; lean_object* v_natCastFn_x3f_977_; lean_object* v_natSMulFn_x3f_978_; lean_object* v_intSMulFn_x3f_979_; lean_object* v_one_x3f_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_988_; 
v_id_966_ = lean_ctor_get(v_s_965_, 0);
v_type_967_ = lean_ctor_get(v_s_965_, 1);
v_u_968_ = lean_ctor_get(v_s_965_, 2);
v_ringInst_969_ = lean_ctor_get(v_s_965_, 3);
v_semiringInst_970_ = lean_ctor_get(v_s_965_, 4);
v_charInst_x3f_971_ = lean_ctor_get(v_s_965_, 5);
v_addFn_x3f_972_ = lean_ctor_get(v_s_965_, 6);
v_mulFn_x3f_973_ = lean_ctor_get(v_s_965_, 7);
v_subFn_x3f_974_ = lean_ctor_get(v_s_965_, 8);
v_powFn_x3f_975_ = lean_ctor_get(v_s_965_, 10);
v_intCastFn_x3f_976_ = lean_ctor_get(v_s_965_, 11);
v_natCastFn_x3f_977_ = lean_ctor_get(v_s_965_, 12);
v_natSMulFn_x3f_978_ = lean_ctor_get(v_s_965_, 13);
v_intSMulFn_x3f_979_ = lean_ctor_get(v_s_965_, 14);
v_one_x3f_980_ = lean_ctor_get(v_s_965_, 15);
v_isSharedCheck_988_ = !lean_is_exclusive(v_s_965_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v_s_965_, 9);
lean_dec(v_unused_989_);
v___x_982_ = v_s_965_;
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_one_x3f_980_);
lean_inc(v_intSMulFn_x3f_979_);
lean_inc(v_natSMulFn_x3f_978_);
lean_inc(v_natCastFn_x3f_977_);
lean_inc(v_intCastFn_x3f_976_);
lean_inc(v_powFn_x3f_975_);
lean_inc(v_subFn_x3f_974_);
lean_inc(v_mulFn_x3f_973_);
lean_inc(v_addFn_x3f_972_);
lean_inc(v_charInst_x3f_971_);
lean_inc(v_semiringInst_970_);
lean_inc(v_ringInst_969_);
lean_inc(v_u_968_);
lean_inc(v_type_967_);
lean_inc(v_id_966_);
lean_dec(v_s_965_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v_negFn_964_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 9, v___x_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_id_966_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_type_967_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_u_968_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_ringInst_969_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_semiringInst_970_);
lean_ctor_set(v_reuseFailAlloc_987_, 5, v_charInst_x3f_971_);
lean_ctor_set(v_reuseFailAlloc_987_, 6, v_addFn_x3f_972_);
lean_ctor_set(v_reuseFailAlloc_987_, 7, v_mulFn_x3f_973_);
lean_ctor_set(v_reuseFailAlloc_987_, 8, v_subFn_x3f_974_);
lean_ctor_set(v_reuseFailAlloc_987_, 9, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_987_, 10, v_powFn_x3f_975_);
lean_ctor_set(v_reuseFailAlloc_987_, 11, v_intCastFn_x3f_976_);
lean_ctor_set(v_reuseFailAlloc_987_, 12, v_natCastFn_x3f_977_);
lean_ctor_set(v_reuseFailAlloc_987_, 13, v_natSMulFn_x3f_978_);
lean_ctor_set(v_reuseFailAlloc_987_, 14, v_intSMulFn_x3f_979_);
lean_ctor_set(v_reuseFailAlloc_987_, 15, v_one_x3f_980_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_990_, lean_object* v_negFn_991_, lean_object* v_____r_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = lean_apply_2(v_toPure_990_, lean_box(0), v_negFn_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_994_, lean_object* v_modifyRing_995_, lean_object* v_toBind_996_, lean_object* v_negFn_997_){
_start:
{
lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_inc_ref(v_negFn_997_);
v___f_998_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_998_, 0, v_negFn_997_);
v___f_999_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_999_, 0, v_toPure_994_);
lean_closure_set(v___f_999_, 1, v_negFn_997_);
v___x_1000_ = lean_apply_1(v_modifyRing_995_, v___f_998_);
v___x_1001_ = lean_apply_4(v_toBind_996_, lean_box(0), lean_box(0), v___x_1000_, v___f_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_toBind_1020_, lean_object* v___f_1021_, lean_object* v_ring_1022_){
_start:
{
lean_object* v_negFn_x3f_1023_; 
v_negFn_x3f_1023_ = lean_ctor_get(v_ring_1022_, 9);
if (lean_obj_tag(v_negFn_x3f_1023_) == 1)
{
lean_object* v_val_1024_; lean_object* v___x_1025_; 
lean_inc_ref(v_negFn_x3f_1023_);
lean_dec_ref(v_ring_1022_);
lean_dec(v___f_1021_);
lean_dec(v_toBind_1020_);
lean_dec_ref(v_inst_1019_);
lean_dec_ref(v_inst_1018_);
lean_dec_ref(v_inst_1017_);
lean_dec(v_inst_1016_);
v_val_1024_ = lean_ctor_get(v_negFn_x3f_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref_known(v_negFn_x3f_1023_, 1);
v___x_1025_ = lean_apply_2(v_toPure_1015_, lean_box(0), v_val_1024_);
return v___x_1025_;
}
else
{
lean_object* v_type_1026_; lean_object* v_u_1027_; lean_object* v_ringInst_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_expectedInst_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec(v_toPure_1015_);
v_type_1026_ = lean_ctor_get(v_ring_1022_, 1);
lean_inc_ref_n(v_type_1026_, 2);
v_u_1027_ = lean_ctor_get(v_ring_1022_, 2);
lean_inc_n(v_u_1027_, 2);
v_ringInst_1028_ = lean_ctor_get(v_ring_1022_, 3);
lean_inc_ref(v_ringInst_1028_);
lean_dec_ref(v_ring_1022_);
v___x_1029_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_u_1027_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l_Lean_mkConst(v___x_1029_, v___x_1031_);
v_expectedInst_1033_ = l_Lean_mkAppB(v___x_1032_, v_type_1026_, v_ringInst_1028_);
v___x_1034_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_1035_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_1036_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1016_, v_inst_1017_, v_inst_1018_, v_inst_1019_, v_type_1026_, v_u_1027_, v___x_1034_, v___x_1035_, v_expectedInst_1033_);
v___x_1037_ = lean_apply_4(v_toBind_1020_, lean_box(0), lean_box(0), v___x_1036_, v___f_1021_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_){
_start:
{
lean_object* v_toApplicative_1043_; lean_object* v_toBind_1044_; lean_object* v_getRing_1045_; lean_object* v_modifyRing_1046_; lean_object* v_toPure_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; 
v_toApplicative_1043_ = lean_ctor_get(v_inst_1040_, 0);
v_toBind_1044_ = lean_ctor_get(v_inst_1040_, 1);
lean_inc_n(v_toBind_1044_, 3);
v_getRing_1045_ = lean_ctor_get(v_inst_1042_, 0);
lean_inc(v_getRing_1045_);
v_modifyRing_1046_ = lean_ctor_get(v_inst_1042_, 1);
lean_inc(v_modifyRing_1046_);
lean_dec_ref(v_inst_1042_);
v_toPure_1047_ = lean_ctor_get(v_toApplicative_1043_, 1);
lean_inc_n(v_toPure_1047_, 2);
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1048_, 0, v_toPure_1047_);
lean_closure_set(v___f_1048_, 1, v_modifyRing_1046_);
lean_closure_set(v___f_1048_, 2, v_toBind_1044_);
v___f_1049_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1049_, 0, v_toPure_1047_);
lean_closure_set(v___f_1049_, 1, v_inst_1038_);
lean_closure_set(v___f_1049_, 2, v_inst_1039_);
lean_closure_set(v___f_1049_, 3, v_inst_1040_);
lean_closure_set(v___f_1049_, 4, v_inst_1041_);
lean_closure_set(v___f_1049_, 5, v_toBind_1044_);
lean_closure_set(v___f_1049_, 6, v___f_1048_);
v___x_1050_ = lean_apply_4(v_toBind_1044_, lean_box(0), lean_box(0), v_getRing_1045_, v___f_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_1052_, v_inst_1053_, v_inst_1054_, v_inst_1055_, v_inst_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_1058_, lean_object* v_s_1059_){
_start:
{
lean_object* v_id_1060_; lean_object* v_type_1061_; lean_object* v_u_1062_; lean_object* v_ringInst_1063_; lean_object* v_semiringInst_1064_; lean_object* v_charInst_x3f_1065_; lean_object* v_addFn_x3f_1066_; lean_object* v_mulFn_x3f_1067_; lean_object* v_subFn_x3f_1068_; lean_object* v_negFn_x3f_1069_; lean_object* v_intCastFn_x3f_1070_; lean_object* v_natCastFn_x3f_1071_; lean_object* v_natSMulFn_x3f_1072_; lean_object* v_intSMulFn_x3f_1073_; lean_object* v_one_x3f_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_id_1060_ = lean_ctor_get(v_s_1059_, 0);
v_type_1061_ = lean_ctor_get(v_s_1059_, 1);
v_u_1062_ = lean_ctor_get(v_s_1059_, 2);
v_ringInst_1063_ = lean_ctor_get(v_s_1059_, 3);
v_semiringInst_1064_ = lean_ctor_get(v_s_1059_, 4);
v_charInst_x3f_1065_ = lean_ctor_get(v_s_1059_, 5);
v_addFn_x3f_1066_ = lean_ctor_get(v_s_1059_, 6);
v_mulFn_x3f_1067_ = lean_ctor_get(v_s_1059_, 7);
v_subFn_x3f_1068_ = lean_ctor_get(v_s_1059_, 8);
v_negFn_x3f_1069_ = lean_ctor_get(v_s_1059_, 9);
v_intCastFn_x3f_1070_ = lean_ctor_get(v_s_1059_, 11);
v_natCastFn_x3f_1071_ = lean_ctor_get(v_s_1059_, 12);
v_natSMulFn_x3f_1072_ = lean_ctor_get(v_s_1059_, 13);
v_intSMulFn_x3f_1073_ = lean_ctor_get(v_s_1059_, 14);
v_one_x3f_1074_ = lean_ctor_get(v_s_1059_, 15);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_s_1059_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_s_1059_, 10);
lean_dec(v_unused_1083_);
v___x_1076_ = v_s_1059_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_one_x3f_1074_);
lean_inc(v_intSMulFn_x3f_1073_);
lean_inc(v_natSMulFn_x3f_1072_);
lean_inc(v_natCastFn_x3f_1071_);
lean_inc(v_intCastFn_x3f_1070_);
lean_inc(v_negFn_x3f_1069_);
lean_inc(v_subFn_x3f_1068_);
lean_inc(v_mulFn_x3f_1067_);
lean_inc(v_addFn_x3f_1066_);
lean_inc(v_charInst_x3f_1065_);
lean_inc(v_semiringInst_1064_);
lean_inc(v_ringInst_1063_);
lean_inc(v_u_1062_);
lean_inc(v_type_1061_);
lean_inc(v_id_1060_);
lean_dec(v_s_1059_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_powFn_1058_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 10, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_id_1060_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_type_1061_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_u_1062_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_ringInst_1063_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v_semiringInst_1064_);
lean_ctor_set(v_reuseFailAlloc_1081_, 5, v_charInst_x3f_1065_);
lean_ctor_set(v_reuseFailAlloc_1081_, 6, v_addFn_x3f_1066_);
lean_ctor_set(v_reuseFailAlloc_1081_, 7, v_mulFn_x3f_1067_);
lean_ctor_set(v_reuseFailAlloc_1081_, 8, v_subFn_x3f_1068_);
lean_ctor_set(v_reuseFailAlloc_1081_, 9, v_negFn_x3f_1069_);
lean_ctor_set(v_reuseFailAlloc_1081_, 10, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 11, v_intCastFn_x3f_1070_);
lean_ctor_set(v_reuseFailAlloc_1081_, 12, v_natCastFn_x3f_1071_);
lean_ctor_set(v_reuseFailAlloc_1081_, 13, v_natSMulFn_x3f_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 14, v_intSMulFn_x3f_1073_);
lean_ctor_set(v_reuseFailAlloc_1081_, 15, v_one_x3f_1074_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_1084_, lean_object* v_powFn_1085_, lean_object* v_____r_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_apply_2(v_toPure_1084_, lean_box(0), v_powFn_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_1088_, lean_object* v_modifyRing_1089_, lean_object* v_toBind_1090_, lean_object* v_powFn_1091_){
_start:
{
lean_object* v___f_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_inc_ref(v_powFn_1091_);
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1092_, 0, v_powFn_1091_);
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1093_, 0, v_toPure_1088_);
lean_closure_set(v___f_1093_, 1, v_powFn_1091_);
v___x_1094_ = lean_apply_1(v_modifyRing_1089_, v___f_1092_);
v___x_1095_ = lean_apply_4(v_toBind_1090_, lean_box(0), lean_box(0), v___x_1094_, v___f_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_toBind_1101_, lean_object* v___f_1102_, lean_object* v_ring_1103_){
_start:
{
lean_object* v_powFn_x3f_1104_; 
v_powFn_x3f_1104_ = lean_ctor_get(v_ring_1103_, 10);
if (lean_obj_tag(v_powFn_x3f_1104_) == 1)
{
lean_object* v_val_1105_; lean_object* v___x_1106_; 
lean_inc_ref(v_powFn_x3f_1104_);
lean_dec_ref(v_ring_1103_);
lean_dec(v___f_1102_);
lean_dec(v_toBind_1101_);
lean_dec_ref(v_inst_1100_);
lean_dec_ref(v_inst_1099_);
lean_dec_ref(v_inst_1098_);
lean_dec(v_inst_1097_);
v_val_1105_ = lean_ctor_get(v_powFn_x3f_1104_, 0);
lean_inc(v_val_1105_);
lean_dec_ref_known(v_powFn_x3f_1104_, 1);
v___x_1106_ = lean_apply_2(v_toPure_1096_, lean_box(0), v_val_1105_);
return v___x_1106_;
}
else
{
lean_object* v_type_1107_; lean_object* v_u_1108_; lean_object* v_semiringInst_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v_toPure_1096_);
v_type_1107_ = lean_ctor_get(v_ring_1103_, 1);
lean_inc_ref(v_type_1107_);
v_u_1108_ = lean_ctor_get(v_ring_1103_, 2);
lean_inc(v_u_1108_);
v_semiringInst_1109_ = lean_ctor_get(v_ring_1103_, 4);
lean_inc_ref(v_semiringInst_1109_);
lean_dec_ref(v_ring_1103_);
v___x_1110_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1097_, v_inst_1098_, v_inst_1099_, v_inst_1100_, v_u_1108_, v_type_1107_, v_semiringInst_1109_);
v___x_1111_ = lean_apply_4(v_toBind_1101_, lean_box(0), lean_box(0), v___x_1110_, v___f_1102_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_){
_start:
{
lean_object* v_toApplicative_1117_; lean_object* v_toBind_1118_; lean_object* v_getRing_1119_; lean_object* v_modifyRing_1120_; lean_object* v_toPure_1121_; lean_object* v___f_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; 
v_toApplicative_1117_ = lean_ctor_get(v_inst_1114_, 0);
v_toBind_1118_ = lean_ctor_get(v_inst_1114_, 1);
lean_inc_n(v_toBind_1118_, 3);
v_getRing_1119_ = lean_ctor_get(v_inst_1116_, 0);
lean_inc(v_getRing_1119_);
v_modifyRing_1120_ = lean_ctor_get(v_inst_1116_, 1);
lean_inc(v_modifyRing_1120_);
lean_dec_ref(v_inst_1116_);
v_toPure_1121_ = lean_ctor_get(v_toApplicative_1117_, 1);
lean_inc_n(v_toPure_1121_, 2);
v___f_1122_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1122_, 0, v_toPure_1121_);
lean_closure_set(v___f_1122_, 1, v_modifyRing_1120_);
lean_closure_set(v___f_1122_, 2, v_toBind_1118_);
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1123_, 0, v_toPure_1121_);
lean_closure_set(v___f_1123_, 1, v_inst_1112_);
lean_closure_set(v___f_1123_, 2, v_inst_1113_);
lean_closure_set(v___f_1123_, 3, v_inst_1114_);
lean_closure_set(v___f_1123_, 4, v_inst_1115_);
lean_closure_set(v___f_1123_, 5, v_toBind_1118_);
lean_closure_set(v___f_1123_, 6, v___f_1122_);
v___x_1124_ = lean_apply_4(v_toBind_1118_, lean_box(0), lean_box(0), v_getRing_1119_, v___f_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_1126_, v_inst_1127_, v_inst_1128_, v_inst_1129_, v_inst_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_1132_, lean_object* v_s_1133_){
_start:
{
lean_object* v_id_1134_; lean_object* v_type_1135_; lean_object* v_u_1136_; lean_object* v_ringInst_1137_; lean_object* v_semiringInst_1138_; lean_object* v_charInst_x3f_1139_; lean_object* v_addFn_x3f_1140_; lean_object* v_mulFn_x3f_1141_; lean_object* v_subFn_x3f_1142_; lean_object* v_negFn_x3f_1143_; lean_object* v_powFn_x3f_1144_; lean_object* v_natCastFn_x3f_1145_; lean_object* v_natSMulFn_x3f_1146_; lean_object* v_intSMulFn_x3f_1147_; lean_object* v_one_x3f_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_id_1134_ = lean_ctor_get(v_s_1133_, 0);
v_type_1135_ = lean_ctor_get(v_s_1133_, 1);
v_u_1136_ = lean_ctor_get(v_s_1133_, 2);
v_ringInst_1137_ = lean_ctor_get(v_s_1133_, 3);
v_semiringInst_1138_ = lean_ctor_get(v_s_1133_, 4);
v_charInst_x3f_1139_ = lean_ctor_get(v_s_1133_, 5);
v_addFn_x3f_1140_ = lean_ctor_get(v_s_1133_, 6);
v_mulFn_x3f_1141_ = lean_ctor_get(v_s_1133_, 7);
v_subFn_x3f_1142_ = lean_ctor_get(v_s_1133_, 8);
v_negFn_x3f_1143_ = lean_ctor_get(v_s_1133_, 9);
v_powFn_x3f_1144_ = lean_ctor_get(v_s_1133_, 10);
v_natCastFn_x3f_1145_ = lean_ctor_get(v_s_1133_, 12);
v_natSMulFn_x3f_1146_ = lean_ctor_get(v_s_1133_, 13);
v_intSMulFn_x3f_1147_ = lean_ctor_get(v_s_1133_, 14);
v_one_x3f_1148_ = lean_ctor_get(v_s_1133_, 15);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_s_1133_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v_s_1133_, 11);
lean_dec(v_unused_1157_);
v___x_1150_ = v_s_1133_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_one_x3f_1148_);
lean_inc(v_intSMulFn_x3f_1147_);
lean_inc(v_natSMulFn_x3f_1146_);
lean_inc(v_natCastFn_x3f_1145_);
lean_inc(v_powFn_x3f_1144_);
lean_inc(v_negFn_x3f_1143_);
lean_inc(v_subFn_x3f_1142_);
lean_inc(v_mulFn_x3f_1141_);
lean_inc(v_addFn_x3f_1140_);
lean_inc(v_charInst_x3f_1139_);
lean_inc(v_semiringInst_1138_);
lean_inc(v_ringInst_1137_);
lean_inc(v_u_1136_);
lean_inc(v_type_1135_);
lean_inc(v_id_1134_);
lean_dec(v_s_1133_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_intCastFn_1132_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 11, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_id_1134_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_type_1135_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_u_1136_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_ringInst_1137_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_semiringInst_1138_);
lean_ctor_set(v_reuseFailAlloc_1155_, 5, v_charInst_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1155_, 6, v_addFn_x3f_1140_);
lean_ctor_set(v_reuseFailAlloc_1155_, 7, v_mulFn_x3f_1141_);
lean_ctor_set(v_reuseFailAlloc_1155_, 8, v_subFn_x3f_1142_);
lean_ctor_set(v_reuseFailAlloc_1155_, 9, v_negFn_x3f_1143_);
lean_ctor_set(v_reuseFailAlloc_1155_, 10, v_powFn_x3f_1144_);
lean_ctor_set(v_reuseFailAlloc_1155_, 11, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1155_, 12, v_natCastFn_x3f_1145_);
lean_ctor_set(v_reuseFailAlloc_1155_, 13, v_natSMulFn_x3f_1146_);
lean_ctor_set(v_reuseFailAlloc_1155_, 14, v_intSMulFn_x3f_1147_);
lean_ctor_set(v_reuseFailAlloc_1155_, 15, v_one_x3f_1148_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_1158_, lean_object* v_intCastFn_1159_, lean_object* v_____r_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_apply_2(v_toPure_1158_, lean_box(0), v_intCastFn_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_1162_, lean_object* v_modifyRing_1163_, lean_object* v_toBind_1164_, lean_object* v_intCastFn_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_inc_ref(v_intCastFn_1165_);
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1166_, 0, v_intCastFn_1165_);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1167_, 0, v_toPure_1162_);
lean_closure_set(v___f_1167_, 1, v_intCastFn_1165_);
v___x_1168_ = lean_apply_1(v_modifyRing_1163_, v___f_1166_);
v___x_1169_ = lean_apply_4(v_toBind_1164_, lean_box(0), lean_box(0), v___x_1168_, v___f_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_1170_, lean_object* v___x_1171_, lean_object* v___x_1172_, lean_object* v_type_1173_, lean_object* v_canonExpr_1174_, lean_object* v_toBind_1175_, lean_object* v___f_1176_, lean_object* v_inst_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1178_ = l_Lean_Name_mkStr2(v___x_1170_, v___x_1171_);
v___x_1179_ = l_Lean_mkConst(v___x_1178_, v___x_1172_);
v___x_1180_ = l_Lean_mkAppB(v___x_1179_, v_type_1173_, v_inst_1177_);
v___x_1181_ = lean_apply_1(v_canonExpr_1174_, v___x_1180_);
v___x_1182_ = lean_apply_4(v_toBind_1175_, lean_box(0), lean_box(0), v___x_1181_, v___f_1176_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_1188_, lean_object* v_inst_x27_1189_, lean_object* v_toBind_1190_, lean_object* v___f_1191_, lean_object* v___f_1192_, lean_object* v_inst_1193_, lean_object* v_____do__lift_1194_){
_start:
{
if (lean_obj_tag(v_____do__lift_1194_) == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v_inst_1193_);
lean_dec(v___f_1192_);
v___x_1195_ = lean_apply_2(v_toPure_1188_, lean_box(0), v_inst_x27_1189_);
v___x_1196_ = lean_apply_4(v_toBind_1190_, lean_box(0), lean_box(0), v___x_1195_, v___f_1191_);
return v___x_1196_;
}
else
{
lean_object* v_val_1197_; lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v___f_1191_);
v_val_1197_ = lean_ctor_get(v_____do__lift_1194_, 0);
lean_inc_n(v_val_1197_, 2);
lean_dec_ref_known(v_____do__lift_1194_, 1);
lean_inc(v_toBind_1190_);
v___f_1198_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1198_, 0, v_toPure_1188_);
lean_closure_set(v___f_1198_, 1, v_val_1197_);
lean_closure_set(v___f_1198_, 2, v_toBind_1190_);
lean_closure_set(v___f_1198_, 3, v___f_1192_);
v___x_1199_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_1200_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_1200_, 0, v___x_1199_);
lean_closure_set(v___x_1200_, 1, v_val_1197_);
lean_closure_set(v___x_1200_, 2, v_inst_x27_1189_);
v___x_1201_ = lean_apply_2(v_inst_1193_, lean_box(0), v___x_1200_);
v___x_1202_ = lean_apply_4(v_toBind_1190_, lean_box(0), lean_box(0), v___x_1201_, v___f_1198_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_1212_, lean_object* v_inst_1213_, lean_object* v_toBind_1214_, lean_object* v___f_1215_, lean_object* v_inst_1216_, lean_object* v_ring_1217_){
_start:
{
lean_object* v_intCastFn_x3f_1218_; 
v_intCastFn_x3f_1218_ = lean_ctor_get(v_ring_1217_, 11);
if (lean_obj_tag(v_intCastFn_x3f_1218_) == 1)
{
lean_object* v_val_1219_; lean_object* v___x_1220_; 
lean_inc_ref(v_intCastFn_x3f_1218_);
lean_dec_ref(v_ring_1217_);
lean_dec(v_inst_1216_);
lean_dec(v___f_1215_);
lean_dec(v_toBind_1214_);
lean_dec_ref(v_inst_1213_);
v_val_1219_ = lean_ctor_get(v_intCastFn_x3f_1218_, 0);
lean_inc(v_val_1219_);
lean_dec_ref_known(v_intCastFn_x3f_1218_, 1);
v___x_1220_ = lean_apply_2(v_toPure_1212_, lean_box(0), v_val_1219_);
return v___x_1220_;
}
else
{
lean_object* v_type_1221_; lean_object* v_u_1222_; lean_object* v_ringInst_1223_; lean_object* v_canonExpr_1224_; lean_object* v_synthInstance_x3f_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1246_; 
v_type_1221_ = lean_ctor_get(v_ring_1217_, 1);
lean_inc_ref(v_type_1221_);
v_u_1222_ = lean_ctor_get(v_ring_1217_, 2);
lean_inc(v_u_1222_);
v_ringInst_1223_ = lean_ctor_get(v_ring_1217_, 3);
lean_inc_ref(v_ringInst_1223_);
lean_dec_ref(v_ring_1217_);
v_canonExpr_1224_ = lean_ctor_get(v_inst_1213_, 0);
v_synthInstance_x3f_1225_ = lean_ctor_get(v_inst_1213_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_inst_1213_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1227_ = v_inst_1213_;
v_isShared_1228_ = v_isSharedCheck_1246_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_synthInstance_x3f_1225_);
lean_inc(v_canonExpr_1224_);
lean_dec(v_inst_1213_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1246_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1229_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_1230_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_1231_ = lean_box(0);
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 1);
lean_ctor_set(v___x_1227_, 1, v___x_1231_);
lean_ctor_set(v___x_1227_, 0, v_u_1222_);
v___x_1233_ = v___x_1227_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_u_1222_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; lean_object* v_inst_x27_1235_; lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_instType_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_inc_ref_n(v___x_1233_, 2);
v___x_1234_ = l_Lean_mkConst(v___x_1230_, v___x_1233_);
lean_inc_ref_n(v_type_1221_, 2);
v_inst_x27_1235_ = l_Lean_mkAppB(v___x_1234_, v_type_1221_, v_ringInst_1223_);
v___x_1236_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_1214_, 2);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1237_, 0, v___x_1236_);
lean_closure_set(v___f_1237_, 1, v___x_1229_);
lean_closure_set(v___f_1237_, 2, v___x_1233_);
lean_closure_set(v___f_1237_, 3, v_type_1221_);
lean_closure_set(v___f_1237_, 4, v_canonExpr_1224_);
lean_closure_set(v___f_1237_, 5, v_toBind_1214_);
lean_closure_set(v___f_1237_, 6, v___f_1215_);
v___f_1238_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1238_, 0, v___f_1237_);
lean_inc_ref(v___f_1238_);
v___f_1239_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_1239_, 0, v_toPure_1212_);
lean_closure_set(v___f_1239_, 1, v_inst_x27_1235_);
lean_closure_set(v___f_1239_, 2, v_toBind_1214_);
lean_closure_set(v___f_1239_, 3, v___f_1238_);
lean_closure_set(v___f_1239_, 4, v___f_1238_);
lean_closure_set(v___f_1239_, 5, v_inst_1216_);
v___x_1240_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_1241_ = l_Lean_mkConst(v___x_1240_, v___x_1233_);
v_instType_1242_ = l_Lean_Expr_app___override(v___x_1241_, v_type_1221_);
v___x_1243_ = lean_apply_1(v_synthInstance_x3f_1225_, v_instType_1242_);
v___x_1244_ = lean_apply_4(v_toBind_1214_, lean_box(0), lean_box(0), v___x_1243_, v___f_1239_);
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_){
_start:
{
lean_object* v_toApplicative_1251_; lean_object* v_toBind_1252_; lean_object* v_getRing_1253_; lean_object* v_modifyRing_1254_; lean_object* v_toPure_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; 
v_toApplicative_1251_ = lean_ctor_get(v_inst_1248_, 0);
lean_inc_ref(v_toApplicative_1251_);
v_toBind_1252_ = lean_ctor_get(v_inst_1248_, 1);
lean_inc_n(v_toBind_1252_, 3);
lean_dec_ref(v_inst_1248_);
v_getRing_1253_ = lean_ctor_get(v_inst_1250_, 0);
lean_inc(v_getRing_1253_);
v_modifyRing_1254_ = lean_ctor_get(v_inst_1250_, 1);
lean_inc(v_modifyRing_1254_);
lean_dec_ref(v_inst_1250_);
v_toPure_1255_ = lean_ctor_get(v_toApplicative_1251_, 1);
lean_inc_n(v_toPure_1255_, 2);
lean_dec_ref(v_toApplicative_1251_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1256_, 0, v_toPure_1255_);
lean_closure_set(v___f_1256_, 1, v_modifyRing_1254_);
lean_closure_set(v___f_1256_, 2, v_toBind_1252_);
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_1257_, 0, v_toPure_1255_);
lean_closure_set(v___f_1257_, 1, v_inst_1249_);
lean_closure_set(v___f_1257_, 2, v_toBind_1252_);
lean_closure_set(v___f_1257_, 3, v___f_1256_);
lean_closure_set(v___f_1257_, 4, v_inst_1247_);
v___x_1258_ = lean_apply_4(v_toBind_1252_, lean_box(0), lean_box(0), v_getRing_1253_, v___f_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_1260_, v_inst_1261_, v_inst_1262_, v_inst_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_1265_, lean_object* v_s_1266_){
_start:
{
lean_object* v_id_1267_; lean_object* v_type_1268_; lean_object* v_u_1269_; lean_object* v_ringInst_1270_; lean_object* v_semiringInst_1271_; lean_object* v_charInst_x3f_1272_; lean_object* v_addFn_x3f_1273_; lean_object* v_mulFn_x3f_1274_; lean_object* v_subFn_x3f_1275_; lean_object* v_negFn_x3f_1276_; lean_object* v_powFn_x3f_1277_; lean_object* v_intCastFn_x3f_1278_; lean_object* v_natSMulFn_x3f_1279_; lean_object* v_intSMulFn_x3f_1280_; lean_object* v_one_x3f_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
v_id_1267_ = lean_ctor_get(v_s_1266_, 0);
v_type_1268_ = lean_ctor_get(v_s_1266_, 1);
v_u_1269_ = lean_ctor_get(v_s_1266_, 2);
v_ringInst_1270_ = lean_ctor_get(v_s_1266_, 3);
v_semiringInst_1271_ = lean_ctor_get(v_s_1266_, 4);
v_charInst_x3f_1272_ = lean_ctor_get(v_s_1266_, 5);
v_addFn_x3f_1273_ = lean_ctor_get(v_s_1266_, 6);
v_mulFn_x3f_1274_ = lean_ctor_get(v_s_1266_, 7);
v_subFn_x3f_1275_ = lean_ctor_get(v_s_1266_, 8);
v_negFn_x3f_1276_ = lean_ctor_get(v_s_1266_, 9);
v_powFn_x3f_1277_ = lean_ctor_get(v_s_1266_, 10);
v_intCastFn_x3f_1278_ = lean_ctor_get(v_s_1266_, 11);
v_natSMulFn_x3f_1279_ = lean_ctor_get(v_s_1266_, 13);
v_intSMulFn_x3f_1280_ = lean_ctor_get(v_s_1266_, 14);
v_one_x3f_1281_ = lean_ctor_get(v_s_1266_, 15);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_s_1266_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_s_1266_, 12);
lean_dec(v_unused_1290_);
v___x_1283_ = v_s_1266_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_one_x3f_1281_);
lean_inc(v_intSMulFn_x3f_1280_);
lean_inc(v_natSMulFn_x3f_1279_);
lean_inc(v_intCastFn_x3f_1278_);
lean_inc(v_powFn_x3f_1277_);
lean_inc(v_negFn_x3f_1276_);
lean_inc(v_subFn_x3f_1275_);
lean_inc(v_mulFn_x3f_1274_);
lean_inc(v_addFn_x3f_1273_);
lean_inc(v_charInst_x3f_1272_);
lean_inc(v_semiringInst_1271_);
lean_inc(v_ringInst_1270_);
lean_inc(v_u_1269_);
lean_inc(v_type_1268_);
lean_inc(v_id_1267_);
lean_dec(v_s_1266_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_natCastFn_1265_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 12, v___x_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_id_1267_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_type_1268_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_u_1269_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_ringInst_1270_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v_semiringInst_1271_);
lean_ctor_set(v_reuseFailAlloc_1288_, 5, v_charInst_x3f_1272_);
lean_ctor_set(v_reuseFailAlloc_1288_, 6, v_addFn_x3f_1273_);
lean_ctor_set(v_reuseFailAlloc_1288_, 7, v_mulFn_x3f_1274_);
lean_ctor_set(v_reuseFailAlloc_1288_, 8, v_subFn_x3f_1275_);
lean_ctor_set(v_reuseFailAlloc_1288_, 9, v_negFn_x3f_1276_);
lean_ctor_set(v_reuseFailAlloc_1288_, 10, v_powFn_x3f_1277_);
lean_ctor_set(v_reuseFailAlloc_1288_, 11, v_intCastFn_x3f_1278_);
lean_ctor_set(v_reuseFailAlloc_1288_, 12, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1288_, 13, v_natSMulFn_x3f_1279_);
lean_ctor_set(v_reuseFailAlloc_1288_, 14, v_intSMulFn_x3f_1280_);
lean_ctor_set(v_reuseFailAlloc_1288_, 15, v_one_x3f_1281_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1291_, lean_object* v_natCastFn_1292_, lean_object* v_____r_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_apply_2(v_toPure_1291_, lean_box(0), v_natCastFn_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1295_, lean_object* v_modifyRing_1296_, lean_object* v_toBind_1297_, lean_object* v_natCastFn_1298_){
_start:
{
lean_object* v___f_1299_; lean_object* v___f_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_inc_ref(v_natCastFn_1298_);
v___f_1299_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1299_, 0, v_natCastFn_1298_);
v___f_1300_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1300_, 0, v_toPure_1295_);
lean_closure_set(v___f_1300_, 1, v_natCastFn_1298_);
v___x_1301_ = lean_apply_1(v_modifyRing_1296_, v___f_1299_);
v___x_1302_ = lean_apply_4(v_toBind_1297_, lean_box(0), lean_box(0), v___x_1301_, v___f_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_toBind_1307_, lean_object* v___f_1308_, lean_object* v_ring_1309_){
_start:
{
lean_object* v_natCastFn_x3f_1310_; 
v_natCastFn_x3f_1310_ = lean_ctor_get(v_ring_1309_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1310_) == 1)
{
lean_object* v_val_1311_; lean_object* v___x_1312_; 
lean_inc_ref(v_natCastFn_x3f_1310_);
lean_dec_ref(v_ring_1309_);
lean_dec(v___f_1308_);
lean_dec(v_toBind_1307_);
lean_dec_ref(v_inst_1306_);
lean_dec_ref(v_inst_1305_);
lean_dec(v_inst_1304_);
v_val_1311_ = lean_ctor_get(v_natCastFn_x3f_1310_, 0);
lean_inc(v_val_1311_);
lean_dec_ref_known(v_natCastFn_x3f_1310_, 1);
v___x_1312_ = lean_apply_2(v_toPure_1303_, lean_box(0), v_val_1311_);
return v___x_1312_;
}
else
{
lean_object* v_type_1313_; lean_object* v_u_1314_; lean_object* v_semiringInst_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v_toPure_1303_);
v_type_1313_ = lean_ctor_get(v_ring_1309_, 1);
lean_inc_ref(v_type_1313_);
v_u_1314_ = lean_ctor_get(v_ring_1309_, 2);
lean_inc(v_u_1314_);
v_semiringInst_1315_ = lean_ctor_get(v_ring_1309_, 4);
lean_inc_ref(v_semiringInst_1315_);
lean_dec_ref(v_ring_1309_);
v___x_1316_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1304_, v_inst_1305_, v_inst_1306_, v_u_1314_, v_type_1313_, v_semiringInst_1315_);
v___x_1317_ = lean_apply_4(v_toBind_1307_, lean_box(0), lean_box(0), v___x_1316_, v___f_1308_);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_){
_start:
{
lean_object* v_toApplicative_1322_; lean_object* v_toBind_1323_; lean_object* v_getRing_1324_; lean_object* v_modifyRing_1325_; lean_object* v_toPure_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; 
v_toApplicative_1322_ = lean_ctor_get(v_inst_1319_, 0);
v_toBind_1323_ = lean_ctor_get(v_inst_1319_, 1);
lean_inc_n(v_toBind_1323_, 3);
v_getRing_1324_ = lean_ctor_get(v_inst_1321_, 0);
lean_inc(v_getRing_1324_);
v_modifyRing_1325_ = lean_ctor_get(v_inst_1321_, 1);
lean_inc(v_modifyRing_1325_);
lean_dec_ref(v_inst_1321_);
v_toPure_1326_ = lean_ctor_get(v_toApplicative_1322_, 1);
lean_inc_n(v_toPure_1326_, 2);
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1327_, 0, v_toPure_1326_);
lean_closure_set(v___f_1327_, 1, v_modifyRing_1325_);
lean_closure_set(v___f_1327_, 2, v_toBind_1323_);
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1328_, 0, v_toPure_1326_);
lean_closure_set(v___f_1328_, 1, v_inst_1318_);
lean_closure_set(v___f_1328_, 2, v_inst_1319_);
lean_closure_set(v___f_1328_, 3, v_inst_1320_);
lean_closure_set(v___f_1328_, 4, v_toBind_1323_);
lean_closure_set(v___f_1328_, 5, v___f_1327_);
v___x_1329_ = lean_apply_4(v_toBind_1323_, lean_box(0), lean_box(0), v_getRing_1324_, v___f_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1331_, v_inst_1332_, v_inst_1333_, v_inst_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1336_, lean_object* v_s_1337_){
_start:
{
lean_object* v_toRing_1338_; lean_object* v_divFn_x3f_1339_; lean_object* v_semiringId_x3f_1340_; lean_object* v_commSemiringInst_1341_; lean_object* v_commRingInst_1342_; lean_object* v_noZeroDivInst_x3f_1343_; lean_object* v_fieldInst_x3f_1344_; lean_object* v_powIdentityInst_x3f_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1353_; 
v_toRing_1338_ = lean_ctor_get(v_s_1337_, 0);
v_divFn_x3f_1339_ = lean_ctor_get(v_s_1337_, 2);
v_semiringId_x3f_1340_ = lean_ctor_get(v_s_1337_, 3);
v_commSemiringInst_1341_ = lean_ctor_get(v_s_1337_, 4);
v_commRingInst_1342_ = lean_ctor_get(v_s_1337_, 5);
v_noZeroDivInst_x3f_1343_ = lean_ctor_get(v_s_1337_, 6);
v_fieldInst_x3f_1344_ = lean_ctor_get(v_s_1337_, 7);
v_powIdentityInst_x3f_1345_ = lean_ctor_get(v_s_1337_, 8);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_s_1337_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; 
v_unused_1354_ = lean_ctor_get(v_s_1337_, 1);
lean_dec(v_unused_1354_);
v___x_1347_ = v_s_1337_;
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1345_);
lean_inc(v_fieldInst_x3f_1344_);
lean_inc(v_noZeroDivInst_x3f_1343_);
lean_inc(v_commRingInst_1342_);
lean_inc(v_commSemiringInst_1341_);
lean_inc(v_semiringId_x3f_1340_);
lean_inc(v_divFn_x3f_1339_);
lean_inc(v_toRing_1338_);
lean_dec(v_s_1337_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_invFn_1336_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_toRing_1338_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_divFn_x3f_1339_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_semiringId_x3f_1340_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v_commSemiringInst_1341_);
lean_ctor_set(v_reuseFailAlloc_1352_, 5, v_commRingInst_1342_);
lean_ctor_set(v_reuseFailAlloc_1352_, 6, v_noZeroDivInst_x3f_1343_);
lean_ctor_set(v_reuseFailAlloc_1352_, 7, v_fieldInst_x3f_1344_);
lean_ctor_set(v_reuseFailAlloc_1352_, 8, v_powIdentityInst_x3f_1345_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1355_, lean_object* v_invFn_1356_, lean_object* v_____r_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_apply_2(v_toPure_1355_, lean_box(0), v_invFn_1356_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1359_, lean_object* v_modifyCommRing_1360_, lean_object* v_toBind_1361_, lean_object* v_invFn_1362_){
_start:
{
lean_object* v___f_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_inc_ref(v_invFn_1362_);
v___f_1363_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1363_, 0, v_invFn_1362_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1364_, 0, v_toPure_1359_);
lean_closure_set(v___f_1364_, 1, v_invFn_1362_);
v___x_1365_ = lean_apply_1(v_modifyCommRing_1360_, v___f_1363_);
v___x_1366_ = lean_apply_4(v_toBind_1361_, lean_box(0), lean_box(0), v___x_1365_, v___f_1364_);
return v___x_1366_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_toBind_1389_, lean_object* v___f_1390_, lean_object* v_ring_1391_){
_start:
{
lean_object* v_fieldInst_x3f_1392_; 
v_fieldInst_x3f_1392_ = lean_ctor_get(v_ring_1391_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1392_) == 1)
{
lean_object* v_invFn_x3f_1393_; 
lean_inc_ref(v_fieldInst_x3f_1392_);
v_invFn_x3f_1393_ = lean_ctor_get(v_ring_1391_, 1);
if (lean_obj_tag(v_invFn_x3f_1393_) == 1)
{
lean_object* v_val_1394_; lean_object* v___x_1395_; 
lean_inc_ref(v_invFn_x3f_1393_);
lean_dec_ref_known(v_fieldInst_x3f_1392_, 1);
lean_dec_ref(v_ring_1391_);
lean_dec(v___f_1390_);
lean_dec(v_toBind_1389_);
lean_dec_ref(v_inst_1388_);
lean_dec_ref(v_inst_1387_);
lean_dec_ref(v_inst_1386_);
lean_dec(v_inst_1385_);
v_val_1394_ = lean_ctor_get(v_invFn_x3f_1393_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v_invFn_x3f_1393_, 1);
v___x_1395_ = lean_apply_2(v_toPure_1384_, lean_box(0), v_val_1394_);
return v___x_1395_;
}
else
{
lean_object* v_toRing_1396_; lean_object* v_val_1397_; lean_object* v_type_1398_; lean_object* v_u_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_expectedInst_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec(v_toPure_1384_);
v_toRing_1396_ = lean_ctor_get(v_ring_1391_, 0);
lean_inc_ref(v_toRing_1396_);
lean_dec_ref(v_ring_1391_);
v_val_1397_ = lean_ctor_get(v_fieldInst_x3f_1392_, 0);
lean_inc(v_val_1397_);
lean_dec_ref_known(v_fieldInst_x3f_1392_, 1);
v_type_1398_ = lean_ctor_get(v_toRing_1396_, 1);
lean_inc_ref_n(v_type_1398_, 2);
v_u_1399_ = lean_ctor_get(v_toRing_1396_, 2);
lean_inc_n(v_u_1399_, 2);
lean_dec_ref(v_toRing_1396_);
v___x_1400_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_u_1399_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = l_Lean_mkConst(v___x_1400_, v___x_1402_);
v_expectedInst_1404_ = l_Lean_mkAppB(v___x_1403_, v_type_1398_, v_val_1397_);
v___x_1405_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1406_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1407_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1385_, v_inst_1386_, v_inst_1387_, v_inst_1388_, v_type_1398_, v_u_1399_, v___x_1405_, v___x_1406_, v_expectedInst_1404_);
v___x_1408_ = lean_apply_4(v_toBind_1389_, lean_box(0), lean_box(0), v___x_1407_, v___f_1390_);
return v___x_1408_;
}
}
else
{
lean_object* v_toRing_1409_; lean_object* v_type_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec(v___f_1390_);
lean_dec(v_toBind_1389_);
lean_dec_ref(v_inst_1388_);
lean_dec(v_inst_1385_);
lean_dec(v_toPure_1384_);
v_toRing_1409_ = lean_ctor_get(v_ring_1391_, 0);
lean_inc_ref(v_toRing_1409_);
lean_dec_ref(v_ring_1391_);
v_type_1410_ = lean_ctor_get(v_toRing_1409_, 1);
lean_inc_ref(v_type_1410_);
lean_dec_ref(v_toRing_1409_);
v___x_1411_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1412_ = l_Lean_indentExpr(v_type_1410_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_throwError___redArg(v_inst_1387_, v_inst_1386_, v___x_1413_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_){
_start:
{
lean_object* v_toApplicative_1420_; lean_object* v_toBind_1421_; lean_object* v_getCommRing_1422_; lean_object* v_modifyCommRing_1423_; lean_object* v_toPure_1424_; lean_object* v___f_1425_; lean_object* v___f_1426_; lean_object* v___x_1427_; 
v_toApplicative_1420_ = lean_ctor_get(v_inst_1417_, 0);
v_toBind_1421_ = lean_ctor_get(v_inst_1417_, 1);
lean_inc_n(v_toBind_1421_, 3);
v_getCommRing_1422_ = lean_ctor_get(v_inst_1419_, 0);
lean_inc(v_getCommRing_1422_);
v_modifyCommRing_1423_ = lean_ctor_get(v_inst_1419_, 1);
lean_inc(v_modifyCommRing_1423_);
lean_dec_ref(v_inst_1419_);
v_toPure_1424_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc_n(v_toPure_1424_, 2);
v___f_1425_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1425_, 0, v_toPure_1424_);
lean_closure_set(v___f_1425_, 1, v_modifyCommRing_1423_);
lean_closure_set(v___f_1425_, 2, v_toBind_1421_);
v___f_1426_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1426_, 0, v_toPure_1424_);
lean_closure_set(v___f_1426_, 1, v_inst_1415_);
lean_closure_set(v___f_1426_, 2, v_inst_1416_);
lean_closure_set(v___f_1426_, 3, v_inst_1417_);
lean_closure_set(v___f_1426_, 4, v_inst_1418_);
lean_closure_set(v___f_1426_, 5, v_toBind_1421_);
lean_closure_set(v___f_1426_, 6, v___f_1425_);
v___x_1427_ = lean_apply_4(v_toBind_1421_, lean_box(0), lean_box(0), v_getCommRing_1422_, v___f_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1429_, v_inst_1430_, v_inst_1431_, v_inst_1432_, v_inst_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0(lean_object* v_divFn_1435_, lean_object* v_s_1436_){
_start:
{
lean_object* v_toRing_1437_; lean_object* v_invFn_x3f_1438_; lean_object* v_semiringId_x3f_1439_; lean_object* v_commSemiringInst_1440_; lean_object* v_commRingInst_1441_; lean_object* v_noZeroDivInst_x3f_1442_; lean_object* v_fieldInst_x3f_1443_; lean_object* v_powIdentityInst_x3f_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
v_toRing_1437_ = lean_ctor_get(v_s_1436_, 0);
v_invFn_x3f_1438_ = lean_ctor_get(v_s_1436_, 1);
v_semiringId_x3f_1439_ = lean_ctor_get(v_s_1436_, 3);
v_commSemiringInst_1440_ = lean_ctor_get(v_s_1436_, 4);
v_commRingInst_1441_ = lean_ctor_get(v_s_1436_, 5);
v_noZeroDivInst_x3f_1442_ = lean_ctor_get(v_s_1436_, 6);
v_fieldInst_x3f_1443_ = lean_ctor_get(v_s_1436_, 7);
v_powIdentityInst_x3f_1444_ = lean_ctor_get(v_s_1436_, 8);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_s_1436_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_s_1436_, 2);
lean_dec(v_unused_1453_);
v___x_1446_ = v_s_1436_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1444_);
lean_inc(v_fieldInst_x3f_1443_);
lean_inc(v_noZeroDivInst_x3f_1442_);
lean_inc(v_commRingInst_1441_);
lean_inc(v_commSemiringInst_1440_);
lean_inc(v_semiringId_x3f_1439_);
lean_inc(v_invFn_x3f_1438_);
lean_inc(v_toRing_1437_);
lean_dec(v_s_1436_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_divFn_1435_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 2, v___x_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_toRing_1437_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_invFn_x3f_1438_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_semiringId_x3f_1439_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v_commSemiringInst_1440_);
lean_ctor_set(v_reuseFailAlloc_1451_, 5, v_commRingInst_1441_);
lean_ctor_set(v_reuseFailAlloc_1451_, 6, v_noZeroDivInst_x3f_1442_);
lean_ctor_set(v_reuseFailAlloc_1451_, 7, v_fieldInst_x3f_1443_);
lean_ctor_set(v_reuseFailAlloc_1451_, 8, v_powIdentityInst_x3f_1444_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1(lean_object* v_toPure_1454_, lean_object* v_divFn_1455_, lean_object* v_____r_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_apply_2(v_toPure_1454_, lean_box(0), v_divFn_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2(lean_object* v_toPure_1458_, lean_object* v_modifyCommRing_1459_, lean_object* v_toBind_1460_, lean_object* v_divFn_1461_){
_start:
{
lean_object* v___f_1462_; lean_object* v___f_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_inc_ref(v_divFn_1461_);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1462_, 0, v_divFn_1461_);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1463_, 0, v_toPure_1458_);
lean_closure_set(v___f_1463_, 1, v_divFn_1461_);
v___x_1464_ = lean_apply_1(v_modifyCommRing_1459_, v___f_1462_);
v___x_1465_ = lean_apply_4(v_toBind_1460_, lean_box(0), lean_box(0), v___x_1464_, v___f_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3(lean_object* v_toPure_1482_, lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_toBind_1487_, lean_object* v___f_1488_, lean_object* v_ring_1489_){
_start:
{
lean_object* v_fieldInst_x3f_1490_; 
v_fieldInst_x3f_1490_ = lean_ctor_get(v_ring_1489_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1490_) == 1)
{
lean_object* v_divFn_x3f_1491_; 
lean_inc_ref(v_fieldInst_x3f_1490_);
v_divFn_x3f_1491_ = lean_ctor_get(v_ring_1489_, 2);
if (lean_obj_tag(v_divFn_x3f_1491_) == 1)
{
lean_object* v_val_1492_; lean_object* v___x_1493_; 
lean_inc_ref(v_divFn_x3f_1491_);
lean_dec_ref_known(v_fieldInst_x3f_1490_, 1);
lean_dec_ref(v_ring_1489_);
lean_dec(v___f_1488_);
lean_dec(v_toBind_1487_);
lean_dec_ref(v_inst_1486_);
lean_dec_ref(v_inst_1485_);
lean_dec_ref(v_inst_1484_);
lean_dec(v_inst_1483_);
v_val_1492_ = lean_ctor_get(v_divFn_x3f_1491_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_divFn_x3f_1491_, 1);
v___x_1493_ = lean_apply_2(v_toPure_1482_, lean_box(0), v_val_1492_);
return v___x_1493_;
}
else
{
lean_object* v_toRing_1494_; lean_object* v_val_1495_; lean_object* v_type_1496_; lean_object* v_u_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_expectedInst_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v_toPure_1482_);
v_toRing_1494_ = lean_ctor_get(v_ring_1489_, 0);
lean_inc_ref(v_toRing_1494_);
lean_dec_ref(v_ring_1489_);
v_val_1495_ = lean_ctor_get(v_fieldInst_x3f_1490_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v_fieldInst_x3f_1490_, 1);
v_type_1496_ = lean_ctor_get(v_toRing_1494_, 1);
lean_inc_ref_n(v_type_1496_, 3);
v_u_1497_ = lean_ctor_get(v_toRing_1494_, 2);
lean_inc_n(v_u_1497_, 2);
lean_dec_ref(v_toRing_1494_);
v___x_1498_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1));
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_u_1497_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
lean_inc_ref(v___x_1500_);
v___x_1501_ = l_Lean_mkConst(v___x_1498_, v___x_1500_);
v___x_1502_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3));
v___x_1503_ = l_Lean_mkConst(v___x_1502_, v___x_1500_);
v___x_1504_ = l_Lean_mkAppB(v___x_1503_, v_type_1496_, v_val_1495_);
v_expectedInst_1505_ = l_Lean_mkAppB(v___x_1501_, v_type_1496_, v___x_1504_);
v___x_1506_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5));
v___x_1507_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7));
v___x_1508_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1483_, v_inst_1484_, v_inst_1485_, v_inst_1486_, v_type_1496_, v_u_1497_, v___x_1506_, v___x_1507_, v_expectedInst_1505_);
v___x_1509_ = lean_apply_4(v_toBind_1487_, lean_box(0), lean_box(0), v___x_1508_, v___f_1488_);
return v___x_1509_;
}
}
else
{
lean_object* v_toRing_1510_; lean_object* v_type_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v___f_1488_);
lean_dec(v_toBind_1487_);
lean_dec_ref(v_inst_1486_);
lean_dec(v_inst_1483_);
lean_dec(v_toPure_1482_);
v_toRing_1510_ = lean_ctor_get(v_ring_1489_, 0);
lean_inc_ref(v_toRing_1510_);
lean_dec_ref(v_ring_1489_);
v_type_1511_ = lean_ctor_get(v_toRing_1510_, 1);
lean_inc_ref(v_type_1511_);
lean_dec_ref(v_toRing_1510_);
v___x_1512_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1513_ = l_Lean_indentExpr(v_type_1511_);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_throwError___redArg(v_inst_1485_, v_inst_1484_, v___x_1514_);
return v___x_1515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg(lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_){
_start:
{
lean_object* v_toApplicative_1521_; lean_object* v_toBind_1522_; lean_object* v_getCommRing_1523_; lean_object* v_modifyCommRing_1524_; lean_object* v_toPure_1525_; lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; 
v_toApplicative_1521_ = lean_ctor_get(v_inst_1518_, 0);
v_toBind_1522_ = lean_ctor_get(v_inst_1518_, 1);
lean_inc_n(v_toBind_1522_, 3);
v_getCommRing_1523_ = lean_ctor_get(v_inst_1520_, 0);
lean_inc(v_getCommRing_1523_);
v_modifyCommRing_1524_ = lean_ctor_get(v_inst_1520_, 1);
lean_inc(v_modifyCommRing_1524_);
lean_dec_ref(v_inst_1520_);
v_toPure_1525_ = lean_ctor_get(v_toApplicative_1521_, 1);
lean_inc_n(v_toPure_1525_, 2);
v___f_1526_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1526_, 0, v_toPure_1525_);
lean_closure_set(v___f_1526_, 1, v_modifyCommRing_1524_);
lean_closure_set(v___f_1526_, 2, v_toBind_1522_);
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1527_, 0, v_toPure_1525_);
lean_closure_set(v___f_1527_, 1, v_inst_1516_);
lean_closure_set(v___f_1527_, 2, v_inst_1517_);
lean_closure_set(v___f_1527_, 3, v_inst_1518_);
lean_closure_set(v___f_1527_, 4, v_inst_1519_);
lean_closure_set(v___f_1527_, 5, v_toBind_1522_);
lean_closure_set(v___f_1527_, 6, v___f_1526_);
v___x_1528_ = lean_apply_4(v_toBind_1522_, lean_box(0), lean_box(0), v_getCommRing_1523_, v___f_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn(lean_object* v_m_1529_, lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_inst_1533_, lean_object* v_inst_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Meta_Sym_Arith_getDivFn___redArg(v_inst_1530_, v_inst_1531_, v_inst_1532_, v_inst_1533_, v_inst_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0(lean_object* v_fn_1536_, lean_object* v_s_1537_){
_start:
{
lean_object* v_id_1538_; lean_object* v_type_1539_; lean_object* v_u_1540_; lean_object* v_semiringInst_1541_; lean_object* v_addFn_x3f_1542_; lean_object* v_mulFn_x3f_1543_; lean_object* v_powFn_x3f_1544_; lean_object* v_natCastFn_x3f_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1553_; 
v_id_1538_ = lean_ctor_get(v_s_1537_, 0);
v_type_1539_ = lean_ctor_get(v_s_1537_, 1);
v_u_1540_ = lean_ctor_get(v_s_1537_, 2);
v_semiringInst_1541_ = lean_ctor_get(v_s_1537_, 3);
v_addFn_x3f_1542_ = lean_ctor_get(v_s_1537_, 4);
v_mulFn_x3f_1543_ = lean_ctor_get(v_s_1537_, 5);
v_powFn_x3f_1544_ = lean_ctor_get(v_s_1537_, 6);
v_natCastFn_x3f_1545_ = lean_ctor_get(v_s_1537_, 7);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_s_1537_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_s_1537_, 8);
lean_dec(v_unused_1554_);
v___x_1547_ = v_s_1537_;
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_natCastFn_x3f_1545_);
lean_inc(v_powFn_x3f_1544_);
lean_inc(v_mulFn_x3f_1543_);
lean_inc(v_addFn_x3f_1542_);
lean_inc(v_semiringInst_1541_);
lean_inc(v_u_1540_);
lean_inc(v_type_1539_);
lean_inc(v_id_1538_);
lean_dec(v_s_1537_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_fn_1536_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 8, v___x_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_id_1538_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_type_1539_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_u_1540_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_semiringInst_1541_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_addFn_x3f_1542_);
lean_ctor_set(v_reuseFailAlloc_1552_, 5, v_mulFn_x3f_1543_);
lean_ctor_set(v_reuseFailAlloc_1552_, 6, v_powFn_x3f_1544_);
lean_ctor_set(v_reuseFailAlloc_1552_, 7, v_natCastFn_x3f_1545_);
lean_ctor_set(v_reuseFailAlloc_1552_, 8, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2(lean_object* v_toPure_1555_, lean_object* v_modifySemiring_1556_, lean_object* v_toBind_1557_, lean_object* v_fn_1558_){
_start:
{
lean_object* v___f_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_inc_ref(v_fn_1558_);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1559_, 0, v_fn_1558_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1560_, 0, v_toPure_1555_);
lean_closure_set(v___f_1560_, 1, v_fn_1558_);
v___x_1561_ = lean_apply_1(v_modifySemiring_1556_, v___f_1559_);
v___x_1562_ = lean_apply_4(v_toBind_1557_, lean_box(0), lean_box(0), v___x_1561_, v___f_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1(lean_object* v_toPure_1563_, lean_object* v_inst_1564_, lean_object* v_inst_1565_, lean_object* v_inst_1566_, lean_object* v_toBind_1567_, lean_object* v___f_1568_, lean_object* v_sr_1569_){
_start:
{
lean_object* v_natSMulFn_x3f_1570_; 
v_natSMulFn_x3f_1570_ = lean_ctor_get(v_sr_1569_, 8);
if (lean_obj_tag(v_natSMulFn_x3f_1570_) == 1)
{
lean_object* v_val_1571_; lean_object* v___x_1572_; 
lean_inc_ref(v_natSMulFn_x3f_1570_);
lean_dec_ref(v_sr_1569_);
lean_dec(v___f_1568_);
lean_dec(v_toBind_1567_);
lean_dec_ref(v_inst_1566_);
lean_dec_ref(v_inst_1565_);
lean_dec(v_inst_1564_);
v_val_1571_ = lean_ctor_get(v_natSMulFn_x3f_1570_, 0);
lean_inc(v_val_1571_);
lean_dec_ref_known(v_natSMulFn_x3f_1570_, 1);
v___x_1572_ = lean_apply_2(v_toPure_1563_, lean_box(0), v_val_1571_);
return v___x_1572_;
}
else
{
lean_object* v_type_1573_; lean_object* v_u_1574_; lean_object* v_semiringInst_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_toPure_1563_);
v_type_1573_ = lean_ctor_get(v_sr_1569_, 1);
lean_inc_ref_n(v_type_1573_, 2);
v_u_1574_ = lean_ctor_get(v_sr_1569_, 2);
lean_inc_n(v_u_1574_, 2);
v_semiringInst_1575_ = lean_ctor_get(v_sr_1569_, 3);
lean_inc_ref(v_semiringInst_1575_);
lean_dec_ref(v_sr_1569_);
v___x_1576_ = l_Lean_Nat_mkType;
v___x_1577_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_u_1574_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = l_Lean_mkConst(v___x_1577_, v___x_1579_);
v___x_1581_ = l_Lean_mkAppB(v___x_1580_, v_type_1573_, v_semiringInst_1575_);
v___x_1582_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_1564_, v_inst_1565_, v_inst_1566_, v_u_1574_, v_type_1573_, v___x_1576_, v___x_1581_);
v___x_1583_ = lean_apply_4(v_toBind_1567_, lean_box(0), lean_box(0), v___x_1582_, v___f_1568_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_){
_start:
{
lean_object* v_toApplicative_1588_; lean_object* v_toBind_1589_; lean_object* v_getSemiring_1590_; lean_object* v_modifySemiring_1591_; lean_object* v_toPure_1592_; lean_object* v___f_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; 
v_toApplicative_1588_ = lean_ctor_get(v_inst_1585_, 0);
v_toBind_1589_ = lean_ctor_get(v_inst_1585_, 1);
lean_inc_n(v_toBind_1589_, 3);
v_getSemiring_1590_ = lean_ctor_get(v_inst_1587_, 0);
lean_inc(v_getSemiring_1590_);
v_modifySemiring_1591_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc(v_modifySemiring_1591_);
lean_dec_ref(v_inst_1587_);
v_toPure_1592_ = lean_ctor_get(v_toApplicative_1588_, 1);
lean_inc_n(v_toPure_1592_, 2);
v___f_1593_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1593_, 0, v_toPure_1592_);
lean_closure_set(v___f_1593_, 1, v_modifySemiring_1591_);
lean_closure_set(v___f_1593_, 2, v_toBind_1589_);
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1594_, 0, v_toPure_1592_);
lean_closure_set(v___f_1594_, 1, v_inst_1584_);
lean_closure_set(v___f_1594_, 2, v_inst_1585_);
lean_closure_set(v___f_1594_, 3, v_inst_1586_);
lean_closure_set(v___f_1594_, 4, v_toBind_1589_);
lean_closure_set(v___f_1594_, 5, v___f_1593_);
v___x_1595_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v_getSemiring_1590_, v___f_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27(lean_object* v_m_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(v_inst_1597_, v_inst_1598_, v_inst_1599_, v_inst_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_1602_, lean_object* v_s_1603_){
_start:
{
lean_object* v_id_1604_; lean_object* v_type_1605_; lean_object* v_u_1606_; lean_object* v_semiringInst_1607_; lean_object* v_mulFn_x3f_1608_; lean_object* v_powFn_x3f_1609_; lean_object* v_natCastFn_x3f_1610_; lean_object* v_natSMulFn_x3f_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1619_; 
v_id_1604_ = lean_ctor_get(v_s_1603_, 0);
v_type_1605_ = lean_ctor_get(v_s_1603_, 1);
v_u_1606_ = lean_ctor_get(v_s_1603_, 2);
v_semiringInst_1607_ = lean_ctor_get(v_s_1603_, 3);
v_mulFn_x3f_1608_ = lean_ctor_get(v_s_1603_, 5);
v_powFn_x3f_1609_ = lean_ctor_get(v_s_1603_, 6);
v_natCastFn_x3f_1610_ = lean_ctor_get(v_s_1603_, 7);
v_natSMulFn_x3f_1611_ = lean_ctor_get(v_s_1603_, 8);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_s_1603_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; 
v_unused_1620_ = lean_ctor_get(v_s_1603_, 4);
lean_dec(v_unused_1620_);
v___x_1613_ = v_s_1603_;
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_natSMulFn_x3f_1611_);
lean_inc(v_natCastFn_x3f_1610_);
lean_inc(v_powFn_x3f_1609_);
lean_inc(v_mulFn_x3f_1608_);
lean_inc(v_semiringInst_1607_);
lean_inc(v_u_1606_);
lean_inc(v_type_1605_);
lean_inc(v_id_1604_);
lean_dec(v_s_1603_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_addFn_1602_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v___x_1615_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_id_1604_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_type_1605_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_u_1606_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_semiringInst_1607_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1618_, 5, v_mulFn_x3f_1608_);
lean_ctor_set(v_reuseFailAlloc_1618_, 6, v_powFn_x3f_1609_);
lean_ctor_set(v_reuseFailAlloc_1618_, 7, v_natCastFn_x3f_1610_);
lean_ctor_set(v_reuseFailAlloc_1618_, 8, v_natSMulFn_x3f_1611_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_1621_, lean_object* v_modifySemiring_1622_, lean_object* v_toBind_1623_, lean_object* v_addFn_1624_){
_start:
{
lean_object* v___f_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_inc_ref(v_addFn_1624_);
v___f_1625_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1625_, 0, v_addFn_1624_);
v___f_1626_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1626_, 0, v_toPure_1621_);
lean_closure_set(v___f_1626_, 1, v_addFn_1624_);
v___x_1627_ = lean_apply_1(v_modifySemiring_1622_, v___f_1625_);
v___x_1628_ = lean_apply_4(v_toBind_1623_, lean_box(0), lean_box(0), v___x_1627_, v___f_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_toBind_1634_, lean_object* v___f_1635_, lean_object* v_sr_1636_){
_start:
{
lean_object* v_addFn_x3f_1637_; 
v_addFn_x3f_1637_ = lean_ctor_get(v_sr_1636_, 4);
if (lean_obj_tag(v_addFn_x3f_1637_) == 1)
{
lean_object* v_val_1638_; lean_object* v___x_1639_; 
lean_inc_ref(v_addFn_x3f_1637_);
lean_dec_ref(v_sr_1636_);
lean_dec(v___f_1635_);
lean_dec(v_toBind_1634_);
lean_dec_ref(v_inst_1633_);
lean_dec_ref(v_inst_1632_);
lean_dec_ref(v_inst_1631_);
lean_dec(v_inst_1630_);
v_val_1638_ = lean_ctor_get(v_addFn_x3f_1637_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v_addFn_x3f_1637_, 1);
v___x_1639_ = lean_apply_2(v_toPure_1629_, lean_box(0), v_val_1638_);
return v___x_1639_;
}
else
{
lean_object* v_type_1640_; lean_object* v_u_1641_; lean_object* v_semiringInst_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_expectedInst_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec(v_toPure_1629_);
v_type_1640_ = lean_ctor_get(v_sr_1636_, 1);
lean_inc_ref_n(v_type_1640_, 3);
v_u_1641_ = lean_ctor_get(v_sr_1636_, 2);
lean_inc_n(v_u_1641_, 2);
v_semiringInst_1642_ = lean_ctor_get(v_sr_1636_, 3);
lean_inc_ref(v_semiringInst_1642_);
lean_dec_ref(v_sr_1636_);
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_u_1641_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
lean_inc_ref(v___x_1645_);
v___x_1646_ = l_Lean_mkConst(v___x_1643_, v___x_1645_);
v___x_1647_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1648_ = l_Lean_mkConst(v___x_1647_, v___x_1645_);
v___x_1649_ = l_Lean_mkAppB(v___x_1648_, v_type_1640_, v_semiringInst_1642_);
v_expectedInst_1650_ = l_Lean_mkAppB(v___x_1646_, v_type_1640_, v___x_1649_);
v___x_1651_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1652_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1653_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1630_, v_inst_1631_, v_inst_1632_, v_inst_1633_, v_type_1640_, v_u_1641_, v___x_1651_, v___x_1652_, v_expectedInst_1650_);
v___x_1654_ = lean_apply_4(v_toBind_1634_, lean_box(0), lean_box(0), v___x_1653_, v___f_1635_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_){
_start:
{
lean_object* v_toApplicative_1660_; lean_object* v_toBind_1661_; lean_object* v_getSemiring_1662_; lean_object* v_modifySemiring_1663_; lean_object* v_toPure_1664_; lean_object* v___f_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; 
v_toApplicative_1660_ = lean_ctor_get(v_inst_1657_, 0);
v_toBind_1661_ = lean_ctor_get(v_inst_1657_, 1);
lean_inc_n(v_toBind_1661_, 3);
v_getSemiring_1662_ = lean_ctor_get(v_inst_1659_, 0);
lean_inc(v_getSemiring_1662_);
v_modifySemiring_1663_ = lean_ctor_get(v_inst_1659_, 1);
lean_inc(v_modifySemiring_1663_);
lean_dec_ref(v_inst_1659_);
v_toPure_1664_ = lean_ctor_get(v_toApplicative_1660_, 1);
lean_inc_n(v_toPure_1664_, 2);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1665_, 0, v_toPure_1664_);
lean_closure_set(v___f_1665_, 1, v_modifySemiring_1663_);
lean_closure_set(v___f_1665_, 2, v_toBind_1661_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1666_, 0, v_toPure_1664_);
lean_closure_set(v___f_1666_, 1, v_inst_1655_);
lean_closure_set(v___f_1666_, 2, v_inst_1656_);
lean_closure_set(v___f_1666_, 3, v_inst_1657_);
lean_closure_set(v___f_1666_, 4, v_inst_1658_);
lean_closure_set(v___f_1666_, 5, v_toBind_1661_);
lean_closure_set(v___f_1666_, 6, v___f_1665_);
v___x_1667_ = lean_apply_4(v_toBind_1661_, lean_box(0), lean_box(0), v_getSemiring_1662_, v___f_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1669_, v_inst_1670_, v_inst_1671_, v_inst_1672_, v_inst_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_1675_, lean_object* v_s_1676_){
_start:
{
lean_object* v_id_1677_; lean_object* v_type_1678_; lean_object* v_u_1679_; lean_object* v_semiringInst_1680_; lean_object* v_addFn_x3f_1681_; lean_object* v_powFn_x3f_1682_; lean_object* v_natCastFn_x3f_1683_; lean_object* v_natSMulFn_x3f_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_id_1677_ = lean_ctor_get(v_s_1676_, 0);
v_type_1678_ = lean_ctor_get(v_s_1676_, 1);
v_u_1679_ = lean_ctor_get(v_s_1676_, 2);
v_semiringInst_1680_ = lean_ctor_get(v_s_1676_, 3);
v_addFn_x3f_1681_ = lean_ctor_get(v_s_1676_, 4);
v_powFn_x3f_1682_ = lean_ctor_get(v_s_1676_, 6);
v_natCastFn_x3f_1683_ = lean_ctor_get(v_s_1676_, 7);
v_natSMulFn_x3f_1684_ = lean_ctor_get(v_s_1676_, 8);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_s_1676_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v_s_1676_, 5);
lean_dec(v_unused_1693_);
v___x_1686_ = v_s_1676_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_natSMulFn_x3f_1684_);
lean_inc(v_natCastFn_x3f_1683_);
lean_inc(v_powFn_x3f_1682_);
lean_inc(v_addFn_x3f_1681_);
lean_inc(v_semiringInst_1680_);
lean_inc(v_u_1679_);
lean_inc(v_type_1678_);
lean_inc(v_id_1677_);
lean_dec(v_s_1676_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_mulFn_1675_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 5, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_id_1677_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_type_1678_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_u_1679_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_semiringInst_1680_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_addFn_x3f_1681_);
lean_ctor_set(v_reuseFailAlloc_1691_, 5, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1691_, 6, v_powFn_x3f_1682_);
lean_ctor_set(v_reuseFailAlloc_1691_, 7, v_natCastFn_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1691_, 8, v_natSMulFn_x3f_1684_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1694_, lean_object* v_modifySemiring_1695_, lean_object* v_toBind_1696_, lean_object* v_mulFn_1697_){
_start:
{
lean_object* v___f_1698_; lean_object* v___f_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_inc_ref(v_mulFn_1697_);
v___f_1698_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1698_, 0, v_mulFn_1697_);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1699_, 0, v_toPure_1694_);
lean_closure_set(v___f_1699_, 1, v_mulFn_1697_);
v___x_1700_ = lean_apply_1(v_modifySemiring_1695_, v___f_1698_);
v___x_1701_ = lean_apply_4(v_toBind_1696_, lean_box(0), lean_box(0), v___x_1700_, v___f_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_toBind_1707_, lean_object* v___f_1708_, lean_object* v_sr_1709_){
_start:
{
lean_object* v_mulFn_x3f_1710_; 
v_mulFn_x3f_1710_ = lean_ctor_get(v_sr_1709_, 5);
if (lean_obj_tag(v_mulFn_x3f_1710_) == 1)
{
lean_object* v_val_1711_; lean_object* v___x_1712_; 
lean_inc_ref(v_mulFn_x3f_1710_);
lean_dec_ref(v_sr_1709_);
lean_dec(v___f_1708_);
lean_dec(v_toBind_1707_);
lean_dec_ref(v_inst_1706_);
lean_dec_ref(v_inst_1705_);
lean_dec_ref(v_inst_1704_);
lean_dec(v_inst_1703_);
v_val_1711_ = lean_ctor_get(v_mulFn_x3f_1710_, 0);
lean_inc(v_val_1711_);
lean_dec_ref_known(v_mulFn_x3f_1710_, 1);
v___x_1712_ = lean_apply_2(v_toPure_1702_, lean_box(0), v_val_1711_);
return v___x_1712_;
}
else
{
lean_object* v_type_1713_; lean_object* v_u_1714_; lean_object* v_semiringInst_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_expectedInst_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec(v_toPure_1702_);
v_type_1713_ = lean_ctor_get(v_sr_1709_, 1);
lean_inc_ref_n(v_type_1713_, 3);
v_u_1714_ = lean_ctor_get(v_sr_1709_, 2);
lean_inc_n(v_u_1714_, 2);
v_semiringInst_1715_ = lean_ctor_get(v_sr_1709_, 3);
lean_inc_ref(v_semiringInst_1715_);
lean_dec_ref(v_sr_1709_);
v___x_1716_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1717_ = lean_box(0);
v___x_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_u_1714_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
lean_inc_ref(v___x_1718_);
v___x_1719_ = l_Lean_mkConst(v___x_1716_, v___x_1718_);
v___x_1720_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1721_ = l_Lean_mkConst(v___x_1720_, v___x_1718_);
v___x_1722_ = l_Lean_mkAppB(v___x_1721_, v_type_1713_, v_semiringInst_1715_);
v_expectedInst_1723_ = l_Lean_mkAppB(v___x_1719_, v_type_1713_, v___x_1722_);
v___x_1724_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1725_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1726_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1703_, v_inst_1704_, v_inst_1705_, v_inst_1706_, v_type_1713_, v_u_1714_, v___x_1724_, v___x_1725_, v_expectedInst_1723_);
v___x_1727_ = lean_apply_4(v_toBind_1707_, lean_box(0), lean_box(0), v___x_1726_, v___f_1708_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_){
_start:
{
lean_object* v_toApplicative_1733_; lean_object* v_toBind_1734_; lean_object* v_getSemiring_1735_; lean_object* v_modifySemiring_1736_; lean_object* v_toPure_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; 
v_toApplicative_1733_ = lean_ctor_get(v_inst_1730_, 0);
v_toBind_1734_ = lean_ctor_get(v_inst_1730_, 1);
lean_inc_n(v_toBind_1734_, 3);
v_getSemiring_1735_ = lean_ctor_get(v_inst_1732_, 0);
lean_inc(v_getSemiring_1735_);
v_modifySemiring_1736_ = lean_ctor_get(v_inst_1732_, 1);
lean_inc(v_modifySemiring_1736_);
lean_dec_ref(v_inst_1732_);
v_toPure_1737_ = lean_ctor_get(v_toApplicative_1733_, 1);
lean_inc_n(v_toPure_1737_, 2);
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1738_, 0, v_toPure_1737_);
lean_closure_set(v___f_1738_, 1, v_modifySemiring_1736_);
lean_closure_set(v___f_1738_, 2, v_toBind_1734_);
v___f_1739_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1739_, 0, v_toPure_1737_);
lean_closure_set(v___f_1739_, 1, v_inst_1728_);
lean_closure_set(v___f_1739_, 2, v_inst_1729_);
lean_closure_set(v___f_1739_, 3, v_inst_1730_);
lean_closure_set(v___f_1739_, 4, v_inst_1731_);
lean_closure_set(v___f_1739_, 5, v_toBind_1734_);
lean_closure_set(v___f_1739_, 6, v___f_1738_);
v___x_1740_ = lean_apply_4(v_toBind_1734_, lean_box(0), lean_box(0), v_getSemiring_1735_, v___f_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1742_, v_inst_1743_, v_inst_1744_, v_inst_1745_, v_inst_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1748_, lean_object* v_s_1749_){
_start:
{
lean_object* v_id_1750_; lean_object* v_type_1751_; lean_object* v_u_1752_; lean_object* v_semiringInst_1753_; lean_object* v_addFn_x3f_1754_; lean_object* v_mulFn_x3f_1755_; lean_object* v_natCastFn_x3f_1756_; lean_object* v_natSMulFn_x3f_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
v_id_1750_ = lean_ctor_get(v_s_1749_, 0);
v_type_1751_ = lean_ctor_get(v_s_1749_, 1);
v_u_1752_ = lean_ctor_get(v_s_1749_, 2);
v_semiringInst_1753_ = lean_ctor_get(v_s_1749_, 3);
v_addFn_x3f_1754_ = lean_ctor_get(v_s_1749_, 4);
v_mulFn_x3f_1755_ = lean_ctor_get(v_s_1749_, 5);
v_natCastFn_x3f_1756_ = lean_ctor_get(v_s_1749_, 7);
v_natSMulFn_x3f_1757_ = lean_ctor_get(v_s_1749_, 8);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_s_1749_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v_s_1749_, 6);
lean_dec(v_unused_1766_);
v___x_1759_ = v_s_1749_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_natSMulFn_x3f_1757_);
lean_inc(v_natCastFn_x3f_1756_);
lean_inc(v_mulFn_x3f_1755_);
lean_inc(v_addFn_x3f_1754_);
lean_inc(v_semiringInst_1753_);
lean_inc(v_u_1752_);
lean_inc(v_type_1751_);
lean_inc(v_id_1750_);
lean_dec(v_s_1749_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_powFn_1748_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 6, v___x_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_id_1750_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_type_1751_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_u_1752_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_semiringInst_1753_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_addFn_x3f_1754_);
lean_ctor_set(v_reuseFailAlloc_1764_, 5, v_mulFn_x3f_1755_);
lean_ctor_set(v_reuseFailAlloc_1764_, 6, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1764_, 7, v_natCastFn_x3f_1756_);
lean_ctor_set(v_reuseFailAlloc_1764_, 8, v_natSMulFn_x3f_1757_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1767_, lean_object* v_modifySemiring_1768_, lean_object* v_toBind_1769_, lean_object* v_powFn_1770_){
_start:
{
lean_object* v___f_1771_; lean_object* v___f_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_inc_ref(v_powFn_1770_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1771_, 0, v_powFn_1770_);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1772_, 0, v_toPure_1767_);
lean_closure_set(v___f_1772_, 1, v_powFn_1770_);
v___x_1773_ = lean_apply_1(v_modifySemiring_1768_, v___f_1771_);
v___x_1774_ = lean_apply_4(v_toBind_1769_, lean_box(0), lean_box(0), v___x_1773_, v___f_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_toBind_1780_, lean_object* v___f_1781_, lean_object* v_sr_1782_){
_start:
{
lean_object* v_powFn_x3f_1783_; 
v_powFn_x3f_1783_ = lean_ctor_get(v_sr_1782_, 6);
if (lean_obj_tag(v_powFn_x3f_1783_) == 1)
{
lean_object* v_val_1784_; lean_object* v___x_1785_; 
lean_inc_ref(v_powFn_x3f_1783_);
lean_dec_ref(v_sr_1782_);
lean_dec(v___f_1781_);
lean_dec(v_toBind_1780_);
lean_dec_ref(v_inst_1779_);
lean_dec_ref(v_inst_1778_);
lean_dec_ref(v_inst_1777_);
lean_dec(v_inst_1776_);
v_val_1784_ = lean_ctor_get(v_powFn_x3f_1783_, 0);
lean_inc(v_val_1784_);
lean_dec_ref_known(v_powFn_x3f_1783_, 1);
v___x_1785_ = lean_apply_2(v_toPure_1775_, lean_box(0), v_val_1784_);
return v___x_1785_;
}
else
{
lean_object* v_type_1786_; lean_object* v_u_1787_; lean_object* v_semiringInst_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v_toPure_1775_);
v_type_1786_ = lean_ctor_get(v_sr_1782_, 1);
lean_inc_ref(v_type_1786_);
v_u_1787_ = lean_ctor_get(v_sr_1782_, 2);
lean_inc(v_u_1787_);
v_semiringInst_1788_ = lean_ctor_get(v_sr_1782_, 3);
lean_inc_ref(v_semiringInst_1788_);
lean_dec_ref(v_sr_1782_);
v___x_1789_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1776_, v_inst_1777_, v_inst_1778_, v_inst_1779_, v_u_1787_, v_type_1786_, v_semiringInst_1788_);
v___x_1790_ = lean_apply_4(v_toBind_1780_, lean_box(0), lean_box(0), v___x_1789_, v___f_1781_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_){
_start:
{
lean_object* v_toApplicative_1796_; lean_object* v_toBind_1797_; lean_object* v_getSemiring_1798_; lean_object* v_modifySemiring_1799_; lean_object* v_toPure_1800_; lean_object* v___f_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; 
v_toApplicative_1796_ = lean_ctor_get(v_inst_1793_, 0);
v_toBind_1797_ = lean_ctor_get(v_inst_1793_, 1);
lean_inc_n(v_toBind_1797_, 3);
v_getSemiring_1798_ = lean_ctor_get(v_inst_1795_, 0);
lean_inc(v_getSemiring_1798_);
v_modifySemiring_1799_ = lean_ctor_get(v_inst_1795_, 1);
lean_inc(v_modifySemiring_1799_);
lean_dec_ref(v_inst_1795_);
v_toPure_1800_ = lean_ctor_get(v_toApplicative_1796_, 1);
lean_inc_n(v_toPure_1800_, 2);
v___f_1801_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1801_, 0, v_toPure_1800_);
lean_closure_set(v___f_1801_, 1, v_modifySemiring_1799_);
lean_closure_set(v___f_1801_, 2, v_toBind_1797_);
v___f_1802_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1802_, 0, v_toPure_1800_);
lean_closure_set(v___f_1802_, 1, v_inst_1791_);
lean_closure_set(v___f_1802_, 2, v_inst_1792_);
lean_closure_set(v___f_1802_, 3, v_inst_1793_);
lean_closure_set(v___f_1802_, 4, v_inst_1794_);
lean_closure_set(v___f_1802_, 5, v_toBind_1797_);
lean_closure_set(v___f_1802_, 6, v___f_1801_);
v___x_1803_ = lean_apply_4(v_toBind_1797_, lean_box(0), lean_box(0), v_getSemiring_1798_, v___f_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1805_, v_inst_1806_, v_inst_1807_, v_inst_1808_, v_inst_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1811_, lean_object* v_s_1812_){
_start:
{
lean_object* v_id_1813_; lean_object* v_type_1814_; lean_object* v_u_1815_; lean_object* v_semiringInst_1816_; lean_object* v_addFn_x3f_1817_; lean_object* v_mulFn_x3f_1818_; lean_object* v_powFn_x3f_1819_; lean_object* v_natSMulFn_x3f_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
v_id_1813_ = lean_ctor_get(v_s_1812_, 0);
v_type_1814_ = lean_ctor_get(v_s_1812_, 1);
v_u_1815_ = lean_ctor_get(v_s_1812_, 2);
v_semiringInst_1816_ = lean_ctor_get(v_s_1812_, 3);
v_addFn_x3f_1817_ = lean_ctor_get(v_s_1812_, 4);
v_mulFn_x3f_1818_ = lean_ctor_get(v_s_1812_, 5);
v_powFn_x3f_1819_ = lean_ctor_get(v_s_1812_, 6);
v_natSMulFn_x3f_1820_ = lean_ctor_get(v_s_1812_, 8);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_s_1812_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_s_1812_, 7);
lean_dec(v_unused_1829_);
v___x_1822_ = v_s_1812_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_natSMulFn_x3f_1820_);
lean_inc(v_powFn_x3f_1819_);
lean_inc(v_mulFn_x3f_1818_);
lean_inc(v_addFn_x3f_1817_);
lean_inc(v_semiringInst_1816_);
lean_inc(v_u_1815_);
lean_inc(v_type_1814_);
lean_inc(v_id_1813_);
lean_dec(v_s_1812_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_natCastFn_1811_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 7, v___x_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_id_1813_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_type_1814_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_u_1815_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_semiringInst_1816_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_addFn_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_mulFn_x3f_1818_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_powFn_x3f_1819_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v_natSMulFn_x3f_1820_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1830_, lean_object* v_modifySemiring_1831_, lean_object* v_toBind_1832_, lean_object* v_natCastFn_1833_){
_start:
{
lean_object* v___f_1834_; lean_object* v___f_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_inc_ref(v_natCastFn_1833_);
v___f_1834_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1834_, 0, v_natCastFn_1833_);
v___f_1835_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1835_, 0, v_toPure_1830_);
lean_closure_set(v___f_1835_, 1, v_natCastFn_1833_);
v___x_1836_ = lean_apply_1(v_modifySemiring_1831_, v___f_1834_);
v___x_1837_ = lean_apply_4(v_toBind_1832_, lean_box(0), lean_box(0), v___x_1836_, v___f_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_toBind_1842_, lean_object* v___f_1843_, lean_object* v_sr_1844_){
_start:
{
lean_object* v_natCastFn_x3f_1845_; 
v_natCastFn_x3f_1845_ = lean_ctor_get(v_sr_1844_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1845_) == 1)
{
lean_object* v_val_1846_; lean_object* v___x_1847_; 
lean_inc_ref(v_natCastFn_x3f_1845_);
lean_dec_ref(v_sr_1844_);
lean_dec(v___f_1843_);
lean_dec(v_toBind_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_inst_1840_);
lean_dec(v_inst_1839_);
v_val_1846_ = lean_ctor_get(v_natCastFn_x3f_1845_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v_natCastFn_x3f_1845_, 1);
v___x_1847_ = lean_apply_2(v_toPure_1838_, lean_box(0), v_val_1846_);
return v___x_1847_;
}
else
{
lean_object* v_type_1848_; lean_object* v_u_1849_; lean_object* v_semiringInst_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec(v_toPure_1838_);
v_type_1848_ = lean_ctor_get(v_sr_1844_, 1);
lean_inc_ref(v_type_1848_);
v_u_1849_ = lean_ctor_get(v_sr_1844_, 2);
lean_inc(v_u_1849_);
v_semiringInst_1850_ = lean_ctor_get(v_sr_1844_, 3);
lean_inc_ref(v_semiringInst_1850_);
lean_dec_ref(v_sr_1844_);
v___x_1851_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1839_, v_inst_1840_, v_inst_1841_, v_u_1849_, v_type_1848_, v_semiringInst_1850_);
v___x_1852_ = lean_apply_4(v_toBind_1842_, lean_box(0), lean_box(0), v___x_1851_, v___f_1843_);
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_){
_start:
{
lean_object* v_toApplicative_1857_; lean_object* v_toBind_1858_; lean_object* v_getSemiring_1859_; lean_object* v_modifySemiring_1860_; lean_object* v_toPure_1861_; lean_object* v___f_1862_; lean_object* v___f_1863_; lean_object* v___x_1864_; 
v_toApplicative_1857_ = lean_ctor_get(v_inst_1854_, 0);
v_toBind_1858_ = lean_ctor_get(v_inst_1854_, 1);
lean_inc_n(v_toBind_1858_, 3);
v_getSemiring_1859_ = lean_ctor_get(v_inst_1856_, 0);
lean_inc(v_getSemiring_1859_);
v_modifySemiring_1860_ = lean_ctor_get(v_inst_1856_, 1);
lean_inc(v_modifySemiring_1860_);
lean_dec_ref(v_inst_1856_);
v_toPure_1861_ = lean_ctor_get(v_toApplicative_1857_, 1);
lean_inc_n(v_toPure_1861_, 2);
v___f_1862_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1862_, 0, v_toPure_1861_);
lean_closure_set(v___f_1862_, 1, v_modifySemiring_1860_);
lean_closure_set(v___f_1862_, 2, v_toBind_1858_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1863_, 0, v_toPure_1861_);
lean_closure_set(v___f_1863_, 1, v_inst_1853_);
lean_closure_set(v___f_1863_, 2, v_inst_1854_);
lean_closure_set(v___f_1863_, 3, v_inst_1855_);
lean_closure_set(v___f_1863_, 4, v_toBind_1858_);
lean_closure_set(v___f_1863_, 5, v___f_1862_);
v___x_1864_ = lean_apply_4(v_toBind_1858_, lean_box(0), lean_box(0), v_getSemiring_1859_, v___f_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1866_, v_inst_1867_, v_inst_1868_, v_inst_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0(lean_object* v_toQFn_1871_, lean_object* v_s_1872_){
_start:
{
lean_object* v_toSemiring_1873_; lean_object* v_ringId_1874_; lean_object* v_commSemiringInst_1875_; lean_object* v_addRightCancelInst_x3f_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1884_; 
v_toSemiring_1873_ = lean_ctor_get(v_s_1872_, 0);
v_ringId_1874_ = lean_ctor_get(v_s_1872_, 1);
v_commSemiringInst_1875_ = lean_ctor_get(v_s_1872_, 2);
v_addRightCancelInst_x3f_1876_ = lean_ctor_get(v_s_1872_, 3);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_s_1872_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v_s_1872_, 4);
lean_dec(v_unused_1885_);
v___x_1878_ = v_s_1872_;
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_1876_);
lean_inc(v_commSemiringInst_1875_);
lean_inc(v_ringId_1874_);
lean_inc(v_toSemiring_1873_);
lean_dec(v_s_1872_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_toQFn_1871_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 4, v___x_1880_);
v___x_1882_ = v___x_1878_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_toSemiring_1873_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_ringId_1874_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_commSemiringInst_1875_);
lean_ctor_set(v_reuseFailAlloc_1883_, 3, v_addRightCancelInst_x3f_1876_);
lean_ctor_set(v_reuseFailAlloc_1883_, 4, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1(lean_object* v_toPure_1886_, lean_object* v_toQFn_1887_, lean_object* v_____r_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_apply_2(v_toPure_1886_, lean_box(0), v_toQFn_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2(lean_object* v_toPure_1890_, lean_object* v_modifyCommSemiring_1891_, lean_object* v_toBind_1892_, lean_object* v_toQFn_1893_){
_start:
{
lean_object* v___f_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_inc_ref(v_toQFn_1893_);
v___f_1894_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1894_, 0, v_toQFn_1893_);
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1895_, 0, v_toPure_1890_);
lean_closure_set(v___f_1895_, 1, v_toQFn_1893_);
v___x_1896_ = lean_apply_1(v_modifyCommSemiring_1891_, v___f_1894_);
v___x_1897_ = lean_apply_4(v_toBind_1892_, lean_box(0), lean_box(0), v___x_1896_, v___f_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3(lean_object* v_toPure_1906_, lean_object* v_inst_1907_, lean_object* v_toBind_1908_, lean_object* v___f_1909_, lean_object* v_s_1910_){
_start:
{
lean_object* v_toQFn_x3f_1911_; 
v_toQFn_x3f_1911_ = lean_ctor_get(v_s_1910_, 4);
if (lean_obj_tag(v_toQFn_x3f_1911_) == 1)
{
lean_object* v_val_1912_; lean_object* v___x_1913_; 
lean_inc_ref(v_toQFn_x3f_1911_);
lean_dec_ref(v_s_1910_);
lean_dec(v___f_1909_);
lean_dec(v_toBind_1908_);
lean_dec_ref(v_inst_1907_);
v_val_1912_ = lean_ctor_get(v_toQFn_x3f_1911_, 0);
lean_inc(v_val_1912_);
lean_dec_ref_known(v_toQFn_x3f_1911_, 1);
v___x_1913_ = lean_apply_2(v_toPure_1906_, lean_box(0), v_val_1912_);
return v___x_1913_;
}
else
{
lean_object* v_toSemiring_1914_; lean_object* v_canonExpr_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_toPure_1906_);
v_toSemiring_1914_ = lean_ctor_get(v_s_1910_, 0);
lean_inc_ref(v_toSemiring_1914_);
lean_dec_ref(v_s_1910_);
v_canonExpr_1915_ = lean_ctor_get(v_inst_1907_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_inst_1907_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_inst_1907_, 1);
lean_dec(v_unused_1932_);
v___x_1917_ = v_inst_1907_;
v_isShared_1918_ = v_isSharedCheck_1931_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_canonExpr_1915_);
lean_dec(v_inst_1907_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1931_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_type_1919_; lean_object* v_u_1920_; lean_object* v_semiringInst_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v_type_1919_ = lean_ctor_get(v_toSemiring_1914_, 1);
lean_inc_ref(v_type_1919_);
v_u_1920_ = lean_ctor_get(v_toSemiring_1914_, 2);
lean_inc(v_u_1920_);
v_semiringInst_1921_ = lean_ctor_get(v_toSemiring_1914_, 3);
lean_inc_ref(v_semiringInst_1921_);
lean_dec_ref(v_toSemiring_1914_);
v___x_1922_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2));
v___x_1923_ = lean_box(0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 1);
lean_ctor_set(v___x_1917_, 1, v___x_1923_);
lean_ctor_set(v___x_1917_, 0, v_u_1920_);
v___x_1925_ = v___x_1917_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_u_1920_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1926_ = l_Lean_mkConst(v___x_1922_, v___x_1925_);
v___x_1927_ = l_Lean_mkAppB(v___x_1926_, v_type_1919_, v_semiringInst_1921_);
v___x_1928_ = lean_apply_1(v_canonExpr_1915_, v___x_1927_);
v___x_1929_ = lean_apply_4(v_toBind_1908_, lean_box(0), lean_box(0), v___x_1928_, v___f_1909_);
return v___x_1929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg(lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_){
_start:
{
lean_object* v_toApplicative_1936_; lean_object* v_toBind_1937_; lean_object* v_getCommSemiring_1938_; lean_object* v_modifyCommSemiring_1939_; lean_object* v_toPure_1940_; lean_object* v___f_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; 
v_toApplicative_1936_ = lean_ctor_get(v_inst_1933_, 0);
lean_inc_ref(v_toApplicative_1936_);
v_toBind_1937_ = lean_ctor_get(v_inst_1933_, 1);
lean_inc_n(v_toBind_1937_, 3);
lean_dec_ref(v_inst_1933_);
v_getCommSemiring_1938_ = lean_ctor_get(v_inst_1935_, 0);
lean_inc(v_getCommSemiring_1938_);
v_modifyCommSemiring_1939_ = lean_ctor_get(v_inst_1935_, 1);
lean_inc(v_modifyCommSemiring_1939_);
lean_dec_ref(v_inst_1935_);
v_toPure_1940_ = lean_ctor_get(v_toApplicative_1936_, 1);
lean_inc_n(v_toPure_1940_, 2);
lean_dec_ref(v_toApplicative_1936_);
v___f_1941_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1941_, 0, v_toPure_1940_);
lean_closure_set(v___f_1941_, 1, v_modifyCommSemiring_1939_);
lean_closure_set(v___f_1941_, 2, v_toBind_1937_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1942_, 0, v_toPure_1940_);
lean_closure_set(v___f_1942_, 1, v_inst_1934_);
lean_closure_set(v___f_1942_, 2, v_toBind_1937_);
lean_closure_set(v___f_1942_, 3, v___f_1941_);
v___x_1943_ = lean_apply_4(v_toBind_1937_, lean_box(0), lean_box(0), v_getCommSemiring_1938_, v___f_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn(lean_object* v_m_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_, lean_object* v_inst_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_Meta_Sym_Arith_getToQFn___redArg(v_inst_1945_, v_inst_1946_, v_inst_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0(lean_object* v_addRightCancelInst_x3f_1949_, lean_object* v_s_1950_){
_start:
{
lean_object* v_toSemiring_1951_; lean_object* v_ringId_1952_; lean_object* v_commSemiringInst_1953_; lean_object* v_toQFn_x3f_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1962_; 
v_toSemiring_1951_ = lean_ctor_get(v_s_1950_, 0);
v_ringId_1952_ = lean_ctor_get(v_s_1950_, 1);
v_commSemiringInst_1953_ = lean_ctor_get(v_s_1950_, 2);
v_toQFn_x3f_1954_ = lean_ctor_get(v_s_1950_, 4);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_s_1950_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v_s_1950_, 3);
lean_dec(v_unused_1963_);
v___x_1956_ = v_s_1950_;
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_toQFn_x3f_1954_);
lean_inc(v_commSemiringInst_1953_);
lean_inc(v_ringId_1952_);
lean_inc(v_toSemiring_1951_);
lean_dec(v_s_1950_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_addRightCancelInst_x3f_1949_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 3, v___x_1958_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_toSemiring_1951_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_ringId_1952_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_commSemiringInst_1953_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v_toQFn_x3f_1954_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1(lean_object* v_toPure_1964_, lean_object* v_addRightCancelInst_x3f_1965_, lean_object* v_____r_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_apply_2(v_toPure_1964_, lean_box(0), v_addRightCancelInst_x3f_1965_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2(lean_object* v_toPure_1968_, lean_object* v_modifyCommSemiring_1969_, lean_object* v_toBind_1970_, lean_object* v_addRightCancelInst_x3f_1971_){
_start:
{
lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_inc(v_addRightCancelInst_x3f_1971_);
v___f_1972_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1972_, 0, v_addRightCancelInst_x3f_1971_);
v___f_1973_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1973_, 0, v_toPure_1968_);
lean_closure_set(v___f_1973_, 1, v_addRightCancelInst_x3f_1971_);
v___x_1974_ = lean_apply_1(v_modifyCommSemiring_1969_, v___f_1972_);
v___x_1975_ = lean_apply_4(v_toBind_1970_, lean_box(0), lean_box(0), v___x_1974_, v___f_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3(lean_object* v___f_1976_, lean_object* v_addRightCancelInst_x3f_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_apply_1(v___f_1976_, v_addRightCancelInst_x3f_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5(lean_object* v___x_1984_, lean_object* v_type_1985_, lean_object* v_synthInstance_x3f_1986_, lean_object* v_toBind_1987_, lean_object* v___f_1988_, lean_object* v_toPure_1989_, lean_object* v___f_1990_, lean_object* v_____x_1991_){
_start:
{
if (lean_obj_tag(v_____x_1991_) == 1)
{
lean_object* v_val_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v___f_1990_);
lean_dec(v_toPure_1989_);
v_val_1992_ = lean_ctor_get(v_____x_1991_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v_____x_1991_, 1);
v___x_1993_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1));
v___x_1994_ = l_Lean_mkConst(v___x_1993_, v___x_1984_);
v___x_1995_ = l_Lean_mkAppB(v___x_1994_, v_type_1985_, v_val_1992_);
v___x_1996_ = lean_apply_1(v_synthInstance_x3f_1986_, v___x_1995_);
v___x_1997_ = lean_apply_4(v_toBind_1987_, lean_box(0), lean_box(0), v___x_1996_, v___f_1988_);
return v___x_1997_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec(v_____x_1991_);
lean_dec(v___f_1988_);
lean_dec(v_synthInstance_x3f_1986_);
lean_dec_ref(v_type_1985_);
lean_dec(v___x_1984_);
v___x_1998_ = lean_box(0);
v___x_1999_ = lean_apply_2(v_toPure_1989_, lean_box(0), v___x_1998_);
v___x_2000_ = lean_apply_4(v_toBind_1987_, lean_box(0), lean_box(0), v___x_1999_, v___f_1990_);
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4(lean_object* v_toPure_2004_, lean_object* v_inst_2005_, lean_object* v_toBind_2006_, lean_object* v___f_2007_, lean_object* v___f_2008_, lean_object* v_s_2009_){
_start:
{
lean_object* v_addRightCancelInst_x3f_2010_; 
v_addRightCancelInst_x3f_2010_ = lean_ctor_get(v_s_2009_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_2010_) == 1)
{
lean_object* v_val_2011_; lean_object* v___x_2012_; 
lean_inc_ref(v_addRightCancelInst_x3f_2010_);
lean_dec_ref(v_s_2009_);
lean_dec(v___f_2008_);
lean_dec(v___f_2007_);
lean_dec(v_toBind_2006_);
lean_dec_ref(v_inst_2005_);
v_val_2011_ = lean_ctor_get(v_addRightCancelInst_x3f_2010_, 0);
lean_inc(v_val_2011_);
lean_dec_ref_known(v_addRightCancelInst_x3f_2010_, 1);
v___x_2012_ = lean_apply_2(v_toPure_2004_, lean_box(0), v_val_2011_);
return v___x_2012_;
}
else
{
lean_object* v_toSemiring_2013_; lean_object* v_synthInstance_x3f_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2030_; 
v_toSemiring_2013_ = lean_ctor_get(v_s_2009_, 0);
lean_inc_ref(v_toSemiring_2013_);
lean_dec_ref(v_s_2009_);
v_synthInstance_x3f_2014_ = lean_ctor_get(v_inst_2005_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_inst_2005_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_inst_2005_, 0);
lean_dec(v_unused_2031_);
v___x_2016_ = v_inst_2005_;
v_isShared_2017_ = v_isSharedCheck_2030_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_synthInstance_x3f_2014_);
lean_dec(v_inst_2005_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2030_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v_type_2018_; lean_object* v_u_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v_type_2018_ = lean_ctor_get(v_toSemiring_2013_, 1);
lean_inc_ref(v_type_2018_);
v_u_2019_ = lean_ctor_get(v_toSemiring_2013_, 2);
lean_inc(v_u_2019_);
lean_dec_ref(v_toSemiring_2013_);
v___x_2020_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1));
v___x_2021_ = lean_box(0);
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 1);
lean_ctor_set(v___x_2016_, 1, v___x_2021_);
lean_ctor_set(v___x_2016_, 0, v_u_2019_);
v___x_2023_ = v___x_2016_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_u_2019_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___f_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_inc(v_toBind_2006_);
lean_inc(v_synthInstance_x3f_2014_);
lean_inc_ref(v_type_2018_);
lean_inc_ref(v___x_2023_);
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_2024_, 0, v___x_2023_);
lean_closure_set(v___f_2024_, 1, v_type_2018_);
lean_closure_set(v___f_2024_, 2, v_synthInstance_x3f_2014_);
lean_closure_set(v___f_2024_, 3, v_toBind_2006_);
lean_closure_set(v___f_2024_, 4, v___f_2007_);
lean_closure_set(v___f_2024_, 5, v_toPure_2004_);
lean_closure_set(v___f_2024_, 6, v___f_2008_);
v___x_2025_ = l_Lean_mkConst(v___x_2020_, v___x_2023_);
v___x_2026_ = l_Lean_Expr_app___override(v___x_2025_, v_type_2018_);
v___x_2027_ = lean_apply_1(v_synthInstance_x3f_2014_, v___x_2026_);
v___x_2028_ = lean_apply_4(v_toBind_2006_, lean_box(0), lean_box(0), v___x_2027_, v___f_2024_);
return v___x_2028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_){
_start:
{
lean_object* v_toApplicative_2035_; lean_object* v_toBind_2036_; lean_object* v_getCommSemiring_2037_; lean_object* v_modifyCommSemiring_2038_; lean_object* v_toPure_2039_; lean_object* v___f_2040_; lean_object* v___f_2041_; lean_object* v___f_2042_; lean_object* v___x_2043_; 
v_toApplicative_2035_ = lean_ctor_get(v_inst_2032_, 0);
lean_inc_ref(v_toApplicative_2035_);
v_toBind_2036_ = lean_ctor_get(v_inst_2032_, 1);
lean_inc_n(v_toBind_2036_, 3);
lean_dec_ref(v_inst_2032_);
v_getCommSemiring_2037_ = lean_ctor_get(v_inst_2034_, 0);
lean_inc(v_getCommSemiring_2037_);
v_modifyCommSemiring_2038_ = lean_ctor_get(v_inst_2034_, 1);
lean_inc(v_modifyCommSemiring_2038_);
lean_dec_ref(v_inst_2034_);
v_toPure_2039_ = lean_ctor_get(v_toApplicative_2035_, 1);
lean_inc_n(v_toPure_2039_, 2);
lean_dec_ref(v_toApplicative_2035_);
v___f_2040_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2040_, 0, v_toPure_2039_);
lean_closure_set(v___f_2040_, 1, v_modifyCommSemiring_2038_);
lean_closure_set(v___f_2040_, 2, v_toBind_2036_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2041_, 0, v___f_2040_);
lean_inc_ref(v___f_2041_);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4), 6, 5);
lean_closure_set(v___f_2042_, 0, v_toPure_2039_);
lean_closure_set(v___f_2042_, 1, v_inst_2033_);
lean_closure_set(v___f_2042_, 2, v_toBind_2036_);
lean_closure_set(v___f_2042_, 3, v___f_2041_);
lean_closure_set(v___f_2042_, 4, v___f_2041_);
v___x_2043_ = lean_apply_4(v_toBind_2036_, lean_box(0), lean_box(0), v_getCommSemiring_2037_, v___f_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f(lean_object* v_m_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(v_inst_2045_, v_inst_2046_, v_inst_2047_);
return v___x_2048_;
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
