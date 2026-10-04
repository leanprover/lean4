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
lean_object* v_id_499_; lean_object* v_type_500_; lean_object* v_u_501_; lean_object* v_ringInst_502_; lean_object* v_semiringInst_503_; lean_object* v_charInst_x3f_504_; lean_object* v_addFn_x3f_505_; lean_object* v_mulFn_x3f_506_; lean_object* v_subFn_x3f_507_; lean_object* v_negFn_x3f_508_; lean_object* v_powFn_x3f_509_; lean_object* v_intCastFn_x3f_510_; lean_object* v_natCastFn_x3f_511_; lean_object* v_intSMulFn_x3f_512_; lean_object* v_one_x3f_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_id_499_ = lean_ctor_get(v_s_498_, 0);
v_type_500_ = lean_ctor_get(v_s_498_, 1);
v_u_501_ = lean_ctor_get(v_s_498_, 2);
v_ringInst_502_ = lean_ctor_get(v_s_498_, 3);
v_semiringInst_503_ = lean_ctor_get(v_s_498_, 4);
v_charInst_x3f_504_ = lean_ctor_get(v_s_498_, 5);
v_addFn_x3f_505_ = lean_ctor_get(v_s_498_, 6);
v_mulFn_x3f_506_ = lean_ctor_get(v_s_498_, 7);
v_subFn_x3f_507_ = lean_ctor_get(v_s_498_, 8);
v_negFn_x3f_508_ = lean_ctor_get(v_s_498_, 9);
v_powFn_x3f_509_ = lean_ctor_get(v_s_498_, 10);
v_intCastFn_x3f_510_ = lean_ctor_get(v_s_498_, 11);
v_natCastFn_x3f_511_ = lean_ctor_get(v_s_498_, 12);
v_intSMulFn_x3f_512_ = lean_ctor_get(v_s_498_, 14);
v_one_x3f_513_ = lean_ctor_get(v_s_498_, 15);
v_isSharedCheck_521_ = !lean_is_exclusive(v_s_498_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v_s_498_, 13);
lean_dec(v_unused_522_);
v___x_515_ = v_s_498_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_one_x3f_513_);
lean_inc(v_intSMulFn_x3f_512_);
lean_inc(v_natCastFn_x3f_511_);
lean_inc(v_intCastFn_x3f_510_);
lean_inc(v_powFn_x3f_509_);
lean_inc(v_negFn_x3f_508_);
lean_inc(v_subFn_x3f_507_);
lean_inc(v_mulFn_x3f_506_);
lean_inc(v_addFn_x3f_505_);
lean_inc(v_charInst_x3f_504_);
lean_inc(v_semiringInst_503_);
lean_inc(v_ringInst_502_);
lean_inc(v_u_501_);
lean_inc(v_type_500_);
lean_inc(v_id_499_);
lean_dec(v_s_498_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v_fn_497_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 13, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_id_499_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_type_500_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_u_501_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_ringInst_502_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v_semiringInst_503_);
lean_ctor_set(v_reuseFailAlloc_520_, 5, v_charInst_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_520_, 6, v_addFn_x3f_505_);
lean_ctor_set(v_reuseFailAlloc_520_, 7, v_mulFn_x3f_506_);
lean_ctor_set(v_reuseFailAlloc_520_, 8, v_subFn_x3f_507_);
lean_ctor_set(v_reuseFailAlloc_520_, 9, v_negFn_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_520_, 10, v_powFn_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_520_, 11, v_intCastFn_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_520_, 12, v_natCastFn_x3f_511_);
lean_ctor_set(v_reuseFailAlloc_520_, 13, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_520_, 14, v_intSMulFn_x3f_512_);
lean_ctor_set(v_reuseFailAlloc_520_, 15, v_one_x3f_513_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1(lean_object* v_toPure_523_, lean_object* v_fn_524_, lean_object* v_____r_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_apply_2(v_toPure_523_, lean_box(0), v_fn_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2(lean_object* v_toPure_527_, lean_object* v_modifyRing_528_, lean_object* v_toBind_529_, lean_object* v_fn_530_){
_start:
{
lean_object* v___f_531_; lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_inc_ref(v_fn_530_);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_531_, 0, v_fn_530_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_532_, 0, v_toPure_527_);
lean_closure_set(v___f_532_, 1, v_fn_530_);
v___x_533_ = lean_apply_1(v_modifyRing_528_, v___f_531_);
v___x_534_ = lean_apply_4(v_toBind_529_, lean_box(0), lean_box(0), v___x_533_, v___f_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3(lean_object* v_toPure_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_toBind_545_, lean_object* v___f_546_, lean_object* v_ring_547_){
_start:
{
lean_object* v_natSMulFn_x3f_548_; 
v_natSMulFn_x3f_548_ = lean_ctor_get(v_ring_547_, 13);
if (lean_obj_tag(v_natSMulFn_x3f_548_) == 1)
{
lean_object* v_val_549_; lean_object* v___x_550_; 
lean_inc_ref(v_natSMulFn_x3f_548_);
lean_dec_ref(v_ring_547_);
lean_dec(v___f_546_);
lean_dec(v_toBind_545_);
lean_dec_ref(v_inst_544_);
lean_dec_ref(v_inst_543_);
lean_dec(v_inst_542_);
v_val_549_ = lean_ctor_get(v_natSMulFn_x3f_548_, 0);
lean_inc(v_val_549_);
lean_dec_ref_known(v_natSMulFn_x3f_548_, 1);
v___x_550_ = lean_apply_2(v_toPure_541_, lean_box(0), v_val_549_);
return v___x_550_;
}
else
{
lean_object* v_type_551_; lean_object* v_u_552_; lean_object* v_semiringInst_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_toPure_541_);
v_type_551_ = lean_ctor_get(v_ring_547_, 1);
lean_inc_ref_n(v_type_551_, 2);
v_u_552_ = lean_ctor_get(v_ring_547_, 2);
lean_inc_n(v_u_552_, 2);
v_semiringInst_553_ = lean_ctor_get(v_ring_547_, 4);
lean_inc_ref(v_semiringInst_553_);
lean_dec_ref(v_ring_547_);
v___x_554_ = l_Lean_Nat_mkType;
v___x_555_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v_u_552_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_mkConst(v___x_555_, v___x_557_);
v___x_559_ = l_Lean_mkAppB(v___x_558_, v_type_551_, v_semiringInst_553_);
v___x_560_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_542_, v_inst_543_, v_inst_544_, v_u_552_, v_type_551_, v___x_554_, v___x_559_);
v___x_561_ = lean_apply_4(v_toBind_545_, lean_box(0), lean_box(0), v___x_560_, v___f_546_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_){
_start:
{
lean_object* v_toApplicative_566_; lean_object* v_toBind_567_; lean_object* v_getRing_568_; lean_object* v_modifyRing_569_; lean_object* v_toPure_570_; lean_object* v___f_571_; lean_object* v___f_572_; lean_object* v___x_573_; 
v_toApplicative_566_ = lean_ctor_get(v_inst_563_, 0);
v_toBind_567_ = lean_ctor_get(v_inst_563_, 1);
lean_inc_n(v_toBind_567_, 3);
v_getRing_568_ = lean_ctor_get(v_inst_565_, 0);
lean_inc(v_getRing_568_);
v_modifyRing_569_ = lean_ctor_get(v_inst_565_, 1);
lean_inc(v_modifyRing_569_);
lean_dec_ref(v_inst_565_);
v_toPure_570_ = lean_ctor_get(v_toApplicative_566_, 1);
lean_inc_n(v_toPure_570_, 2);
v___f_571_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_571_, 0, v_toPure_570_);
lean_closure_set(v___f_571_, 1, v_modifyRing_569_);
lean_closure_set(v___f_571_, 2, v_toBind_567_);
v___f_572_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_572_, 0, v_toPure_570_);
lean_closure_set(v___f_572_, 1, v_inst_562_);
lean_closure_set(v___f_572_, 2, v_inst_563_);
lean_closure_set(v___f_572_, 3, v_inst_564_);
lean_closure_set(v___f_572_, 4, v_toBind_567_);
lean_closure_set(v___f_572_, 5, v___f_571_);
v___x_573_ = lean_apply_4(v_toBind_567_, lean_box(0), lean_box(0), v_getRing_568_, v___f_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn(lean_object* v_m_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(v_inst_575_, v_inst_576_, v_inst_577_, v_inst_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0(lean_object* v_fn_580_, lean_object* v_s_581_){
_start:
{
lean_object* v_id_582_; lean_object* v_type_583_; lean_object* v_u_584_; lean_object* v_ringInst_585_; lean_object* v_semiringInst_586_; lean_object* v_charInst_x3f_587_; lean_object* v_addFn_x3f_588_; lean_object* v_mulFn_x3f_589_; lean_object* v_subFn_x3f_590_; lean_object* v_negFn_x3f_591_; lean_object* v_powFn_x3f_592_; lean_object* v_intCastFn_x3f_593_; lean_object* v_natCastFn_x3f_594_; lean_object* v_natSMulFn_x3f_595_; lean_object* v_one_x3f_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_id_582_ = lean_ctor_get(v_s_581_, 0);
v_type_583_ = lean_ctor_get(v_s_581_, 1);
v_u_584_ = lean_ctor_get(v_s_581_, 2);
v_ringInst_585_ = lean_ctor_get(v_s_581_, 3);
v_semiringInst_586_ = lean_ctor_get(v_s_581_, 4);
v_charInst_x3f_587_ = lean_ctor_get(v_s_581_, 5);
v_addFn_x3f_588_ = lean_ctor_get(v_s_581_, 6);
v_mulFn_x3f_589_ = lean_ctor_get(v_s_581_, 7);
v_subFn_x3f_590_ = lean_ctor_get(v_s_581_, 8);
v_negFn_x3f_591_ = lean_ctor_get(v_s_581_, 9);
v_powFn_x3f_592_ = lean_ctor_get(v_s_581_, 10);
v_intCastFn_x3f_593_ = lean_ctor_get(v_s_581_, 11);
v_natCastFn_x3f_594_ = lean_ctor_get(v_s_581_, 12);
v_natSMulFn_x3f_595_ = lean_ctor_get(v_s_581_, 13);
v_one_x3f_596_ = lean_ctor_get(v_s_581_, 15);
v_isSharedCheck_604_ = !lean_is_exclusive(v_s_581_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v_s_581_, 14);
lean_dec(v_unused_605_);
v___x_598_ = v_s_581_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_one_x3f_596_);
lean_inc(v_natSMulFn_x3f_595_);
lean_inc(v_natCastFn_x3f_594_);
lean_inc(v_intCastFn_x3f_593_);
lean_inc(v_powFn_x3f_592_);
lean_inc(v_negFn_x3f_591_);
lean_inc(v_subFn_x3f_590_);
lean_inc(v_mulFn_x3f_589_);
lean_inc(v_addFn_x3f_588_);
lean_inc(v_charInst_x3f_587_);
lean_inc(v_semiringInst_586_);
lean_inc(v_ringInst_585_);
lean_inc(v_u_584_);
lean_inc(v_type_583_);
lean_inc(v_id_582_);
lean_dec(v_s_581_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_fn_580_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 14, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_id_582_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_type_583_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_u_584_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_ringInst_585_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v_semiringInst_586_);
lean_ctor_set(v_reuseFailAlloc_603_, 5, v_charInst_x3f_587_);
lean_ctor_set(v_reuseFailAlloc_603_, 6, v_addFn_x3f_588_);
lean_ctor_set(v_reuseFailAlloc_603_, 7, v_mulFn_x3f_589_);
lean_ctor_set(v_reuseFailAlloc_603_, 8, v_subFn_x3f_590_);
lean_ctor_set(v_reuseFailAlloc_603_, 9, v_negFn_x3f_591_);
lean_ctor_set(v_reuseFailAlloc_603_, 10, v_powFn_x3f_592_);
lean_ctor_set(v_reuseFailAlloc_603_, 11, v_intCastFn_x3f_593_);
lean_ctor_set(v_reuseFailAlloc_603_, 12, v_natCastFn_x3f_594_);
lean_ctor_set(v_reuseFailAlloc_603_, 13, v_natSMulFn_x3f_595_);
lean_ctor_set(v_reuseFailAlloc_603_, 14, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 15, v_one_x3f_596_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2(lean_object* v_toPure_606_, lean_object* v_modifyRing_607_, lean_object* v_toBind_608_, lean_object* v_fn_609_){
_start:
{
lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_inc_ref(v_fn_609_);
v___f_610_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_610_, 0, v_fn_609_);
v___f_611_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_611_, 0, v_toPure_606_);
lean_closure_set(v___f_611_, 1, v_fn_609_);
v___x_612_ = lean_apply_1(v_modifyRing_607_, v___f_610_);
v___x_613_ = lean_apply_4(v_toBind_608_, lean_box(0), lean_box(0), v___x_612_, v___f_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1(lean_object* v_toPure_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_toBind_625_, lean_object* v___f_626_, lean_object* v_ring_627_){
_start:
{
lean_object* v_intSMulFn_x3f_628_; 
v_intSMulFn_x3f_628_ = lean_ctor_get(v_ring_627_, 14);
if (lean_obj_tag(v_intSMulFn_x3f_628_) == 1)
{
lean_object* v_val_629_; lean_object* v___x_630_; 
lean_inc_ref(v_intSMulFn_x3f_628_);
lean_dec_ref(v_ring_627_);
lean_dec(v___f_626_);
lean_dec(v_toBind_625_);
lean_dec_ref(v_inst_624_);
lean_dec_ref(v_inst_623_);
lean_dec(v_inst_622_);
v_val_629_ = lean_ctor_get(v_intSMulFn_x3f_628_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v_intSMulFn_x3f_628_, 1);
v___x_630_ = lean_apply_2(v_toPure_621_, lean_box(0), v_val_629_);
return v___x_630_;
}
else
{
lean_object* v_type_631_; lean_object* v_u_632_; lean_object* v_ringInst_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_toPure_621_);
v_type_631_ = lean_ctor_get(v_ring_627_, 1);
lean_inc_ref_n(v_type_631_, 2);
v_u_632_ = lean_ctor_get(v_ring_627_, 2);
lean_inc_n(v_u_632_, 2);
v_ringInst_633_ = lean_ctor_get(v_ring_627_, 3);
lean_inc_ref(v_ringInst_633_);
lean_dec_ref(v_ring_627_);
v___x_634_ = l_Lean_Int_mkType;
v___x_635_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2));
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v_u_632_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = l_Lean_mkConst(v___x_635_, v___x_637_);
v___x_639_ = l_Lean_mkAppB(v___x_638_, v_type_631_, v_ringInst_633_);
v___x_640_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_622_, v_inst_623_, v_inst_624_, v_u_632_, v_type_631_, v___x_634_, v___x_639_);
v___x_641_ = lean_apply_4(v_toBind_625_, lean_box(0), lean_box(0), v___x_640_, v___f_626_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_){
_start:
{
lean_object* v_toApplicative_646_; lean_object* v_toBind_647_; lean_object* v_getRing_648_; lean_object* v_modifyRing_649_; lean_object* v_toPure_650_; lean_object* v___f_651_; lean_object* v___f_652_; lean_object* v___x_653_; 
v_toApplicative_646_ = lean_ctor_get(v_inst_643_, 0);
v_toBind_647_ = lean_ctor_get(v_inst_643_, 1);
lean_inc_n(v_toBind_647_, 3);
v_getRing_648_ = lean_ctor_get(v_inst_645_, 0);
lean_inc(v_getRing_648_);
v_modifyRing_649_ = lean_ctor_get(v_inst_645_, 1);
lean_inc(v_modifyRing_649_);
lean_dec_ref(v_inst_645_);
v_toPure_650_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_inc_n(v_toPure_650_, 2);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_651_, 0, v_toPure_650_);
lean_closure_set(v___f_651_, 1, v_modifyRing_649_);
lean_closure_set(v___f_651_, 2, v_toBind_647_);
v___f_652_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1), 7, 6);
lean_closure_set(v___f_652_, 0, v_toPure_650_);
lean_closure_set(v___f_652_, 1, v_inst_642_);
lean_closure_set(v___f_652_, 2, v_inst_643_);
lean_closure_set(v___f_652_, 3, v_inst_644_);
lean_closure_set(v___f_652_, 4, v_toBind_647_);
lean_closure_set(v___f_652_, 5, v___f_651_);
v___x_653_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v_getRing_648_, v___f_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn(lean_object* v_m_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(v_inst_655_, v_inst_656_, v_inst_657_, v_inst_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_660_, lean_object* v_s_661_){
_start:
{
lean_object* v_id_662_; lean_object* v_type_663_; lean_object* v_u_664_; lean_object* v_ringInst_665_; lean_object* v_semiringInst_666_; lean_object* v_charInst_x3f_667_; lean_object* v_mulFn_x3f_668_; lean_object* v_subFn_x3f_669_; lean_object* v_negFn_x3f_670_; lean_object* v_powFn_x3f_671_; lean_object* v_intCastFn_x3f_672_; lean_object* v_natCastFn_x3f_673_; lean_object* v_natSMulFn_x3f_674_; lean_object* v_intSMulFn_x3f_675_; lean_object* v_one_x3f_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_id_662_ = lean_ctor_get(v_s_661_, 0);
v_type_663_ = lean_ctor_get(v_s_661_, 1);
v_u_664_ = lean_ctor_get(v_s_661_, 2);
v_ringInst_665_ = lean_ctor_get(v_s_661_, 3);
v_semiringInst_666_ = lean_ctor_get(v_s_661_, 4);
v_charInst_x3f_667_ = lean_ctor_get(v_s_661_, 5);
v_mulFn_x3f_668_ = lean_ctor_get(v_s_661_, 7);
v_subFn_x3f_669_ = lean_ctor_get(v_s_661_, 8);
v_negFn_x3f_670_ = lean_ctor_get(v_s_661_, 9);
v_powFn_x3f_671_ = lean_ctor_get(v_s_661_, 10);
v_intCastFn_x3f_672_ = lean_ctor_get(v_s_661_, 11);
v_natCastFn_x3f_673_ = lean_ctor_get(v_s_661_, 12);
v_natSMulFn_x3f_674_ = lean_ctor_get(v_s_661_, 13);
v_intSMulFn_x3f_675_ = lean_ctor_get(v_s_661_, 14);
v_one_x3f_676_ = lean_ctor_get(v_s_661_, 15);
v_isSharedCheck_684_ = !lean_is_exclusive(v_s_661_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_s_661_, 6);
lean_dec(v_unused_685_);
v___x_678_ = v_s_661_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_one_x3f_676_);
lean_inc(v_intSMulFn_x3f_675_);
lean_inc(v_natSMulFn_x3f_674_);
lean_inc(v_natCastFn_x3f_673_);
lean_inc(v_intCastFn_x3f_672_);
lean_inc(v_powFn_x3f_671_);
lean_inc(v_negFn_x3f_670_);
lean_inc(v_subFn_x3f_669_);
lean_inc(v_mulFn_x3f_668_);
lean_inc(v_charInst_x3f_667_);
lean_inc(v_semiringInst_666_);
lean_inc(v_ringInst_665_);
lean_inc(v_u_664_);
lean_inc(v_type_663_);
lean_inc(v_id_662_);
lean_dec(v_s_661_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v_addFn_660_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 6, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_id_662_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_type_663_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_u_664_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_ringInst_665_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_semiringInst_666_);
lean_ctor_set(v_reuseFailAlloc_683_, 5, v_charInst_x3f_667_);
lean_ctor_set(v_reuseFailAlloc_683_, 6, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_683_, 7, v_mulFn_x3f_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 8, v_subFn_x3f_669_);
lean_ctor_set(v_reuseFailAlloc_683_, 9, v_negFn_x3f_670_);
lean_ctor_set(v_reuseFailAlloc_683_, 10, v_powFn_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_683_, 11, v_intCastFn_x3f_672_);
lean_ctor_set(v_reuseFailAlloc_683_, 12, v_natCastFn_x3f_673_);
lean_ctor_set(v_reuseFailAlloc_683_, 13, v_natSMulFn_x3f_674_);
lean_ctor_set(v_reuseFailAlloc_683_, 14, v_intSMulFn_x3f_675_);
lean_ctor_set(v_reuseFailAlloc_683_, 15, v_one_x3f_676_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_686_, lean_object* v_addFn_687_, lean_object* v_____r_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_apply_2(v_toPure_686_, lean_box(0), v_addFn_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_690_, lean_object* v_modifyRing_691_, lean_object* v_toBind_692_, lean_object* v_addFn_693_){
_start:
{
lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_inc_ref(v_addFn_693_);
v___f_694_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_694_, 0, v_addFn_693_);
v___f_695_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_695_, 0, v_toPure_690_);
lean_closure_set(v___f_695_, 1, v_addFn_693_);
v___x_696_ = lean_apply_1(v_modifyRing_691_, v___f_694_);
v___x_697_ = lean_apply_4(v_toBind_692_, lean_box(0), lean_box(0), v___x_696_, v___f_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_toBind_719_, lean_object* v___f_720_, lean_object* v_ring_721_){
_start:
{
lean_object* v_addFn_x3f_722_; 
v_addFn_x3f_722_ = lean_ctor_get(v_ring_721_, 6);
if (lean_obj_tag(v_addFn_x3f_722_) == 1)
{
lean_object* v_val_723_; lean_object* v___x_724_; 
lean_inc_ref(v_addFn_x3f_722_);
lean_dec_ref(v_ring_721_);
lean_dec(v___f_720_);
lean_dec(v_toBind_719_);
lean_dec_ref(v_inst_718_);
lean_dec_ref(v_inst_717_);
lean_dec_ref(v_inst_716_);
lean_dec(v_inst_715_);
v_val_723_ = lean_ctor_get(v_addFn_x3f_722_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v_addFn_x3f_722_, 1);
v___x_724_ = lean_apply_2(v_toPure_714_, lean_box(0), v_val_723_);
return v___x_724_;
}
else
{
lean_object* v_type_725_; lean_object* v_u_726_; lean_object* v_semiringInst_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_expectedInst_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_toPure_714_);
v_type_725_ = lean_ctor_get(v_ring_721_, 1);
lean_inc_ref_n(v_type_725_, 3);
v_u_726_ = lean_ctor_get(v_ring_721_, 2);
lean_inc_n(v_u_726_, 2);
v_semiringInst_727_ = lean_ctor_get(v_ring_721_, 4);
lean_inc_ref(v_semiringInst_727_);
lean_dec_ref(v_ring_721_);
v___x_728_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_729_ = lean_box(0);
v___x_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_730_, 0, v_u_726_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
lean_inc_ref(v___x_730_);
v___x_731_ = l_Lean_mkConst(v___x_728_, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_733_ = l_Lean_mkConst(v___x_732_, v___x_730_);
v___x_734_ = l_Lean_mkAppB(v___x_733_, v_type_725_, v_semiringInst_727_);
v_expectedInst_735_ = l_Lean_mkAppB(v___x_731_, v_type_725_, v___x_734_);
v___x_736_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_737_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_738_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_715_, v_inst_716_, v_inst_717_, v_inst_718_, v_type_725_, v_u_726_, v___x_736_, v___x_737_, v_expectedInst_735_);
v___x_739_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_738_, v___f_720_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_){
_start:
{
lean_object* v_toApplicative_745_; lean_object* v_toBind_746_; lean_object* v_getRing_747_; lean_object* v_modifyRing_748_; lean_object* v_toPure_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; 
v_toApplicative_745_ = lean_ctor_get(v_inst_742_, 0);
v_toBind_746_ = lean_ctor_get(v_inst_742_, 1);
lean_inc_n(v_toBind_746_, 3);
v_getRing_747_ = lean_ctor_get(v_inst_744_, 0);
lean_inc(v_getRing_747_);
v_modifyRing_748_ = lean_ctor_get(v_inst_744_, 1);
lean_inc(v_modifyRing_748_);
lean_dec_ref(v_inst_744_);
v_toPure_749_ = lean_ctor_get(v_toApplicative_745_, 1);
lean_inc_n(v_toPure_749_, 2);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_750_, 0, v_toPure_749_);
lean_closure_set(v___f_750_, 1, v_modifyRing_748_);
lean_closure_set(v___f_750_, 2, v_toBind_746_);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_751_, 0, v_toPure_749_);
lean_closure_set(v___f_751_, 1, v_inst_740_);
lean_closure_set(v___f_751_, 2, v_inst_741_);
lean_closure_set(v___f_751_, 3, v_inst_742_);
lean_closure_set(v___f_751_, 4, v_inst_743_);
lean_closure_set(v___f_751_, 5, v_toBind_746_);
lean_closure_set(v___f_751_, 6, v___f_750_);
v___x_752_ = lean_apply_4(v_toBind_746_, lean_box(0), lean_box(0), v_getRing_747_, v___f_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_inst_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_754_, v_inst_755_, v_inst_756_, v_inst_757_, v_inst_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_760_, lean_object* v_s_761_){
_start:
{
lean_object* v_id_762_; lean_object* v_type_763_; lean_object* v_u_764_; lean_object* v_ringInst_765_; lean_object* v_semiringInst_766_; lean_object* v_charInst_x3f_767_; lean_object* v_addFn_x3f_768_; lean_object* v_subFn_x3f_769_; lean_object* v_negFn_x3f_770_; lean_object* v_powFn_x3f_771_; lean_object* v_intCastFn_x3f_772_; lean_object* v_natCastFn_x3f_773_; lean_object* v_natSMulFn_x3f_774_; lean_object* v_intSMulFn_x3f_775_; lean_object* v_one_x3f_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
v_id_762_ = lean_ctor_get(v_s_761_, 0);
v_type_763_ = lean_ctor_get(v_s_761_, 1);
v_u_764_ = lean_ctor_get(v_s_761_, 2);
v_ringInst_765_ = lean_ctor_get(v_s_761_, 3);
v_semiringInst_766_ = lean_ctor_get(v_s_761_, 4);
v_charInst_x3f_767_ = lean_ctor_get(v_s_761_, 5);
v_addFn_x3f_768_ = lean_ctor_get(v_s_761_, 6);
v_subFn_x3f_769_ = lean_ctor_get(v_s_761_, 8);
v_negFn_x3f_770_ = lean_ctor_get(v_s_761_, 9);
v_powFn_x3f_771_ = lean_ctor_get(v_s_761_, 10);
v_intCastFn_x3f_772_ = lean_ctor_get(v_s_761_, 11);
v_natCastFn_x3f_773_ = lean_ctor_get(v_s_761_, 12);
v_natSMulFn_x3f_774_ = lean_ctor_get(v_s_761_, 13);
v_intSMulFn_x3f_775_ = lean_ctor_get(v_s_761_, 14);
v_one_x3f_776_ = lean_ctor_get(v_s_761_, 15);
v_isSharedCheck_784_ = !lean_is_exclusive(v_s_761_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_s_761_, 7);
lean_dec(v_unused_785_);
v___x_778_ = v_s_761_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_one_x3f_776_);
lean_inc(v_intSMulFn_x3f_775_);
lean_inc(v_natSMulFn_x3f_774_);
lean_inc(v_natCastFn_x3f_773_);
lean_inc(v_intCastFn_x3f_772_);
lean_inc(v_powFn_x3f_771_);
lean_inc(v_negFn_x3f_770_);
lean_inc(v_subFn_x3f_769_);
lean_inc(v_addFn_x3f_768_);
lean_inc(v_charInst_x3f_767_);
lean_inc(v_semiringInst_766_);
lean_inc(v_ringInst_765_);
lean_inc(v_u_764_);
lean_inc(v_type_763_);
lean_inc(v_id_762_);
lean_dec(v_s_761_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_mulFn_760_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 7, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_id_762_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_type_763_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_u_764_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_ringInst_765_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_semiringInst_766_);
lean_ctor_set(v_reuseFailAlloc_783_, 5, v_charInst_x3f_767_);
lean_ctor_set(v_reuseFailAlloc_783_, 6, v_addFn_x3f_768_);
lean_ctor_set(v_reuseFailAlloc_783_, 7, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 8, v_subFn_x3f_769_);
lean_ctor_set(v_reuseFailAlloc_783_, 9, v_negFn_x3f_770_);
lean_ctor_set(v_reuseFailAlloc_783_, 10, v_powFn_x3f_771_);
lean_ctor_set(v_reuseFailAlloc_783_, 11, v_intCastFn_x3f_772_);
lean_ctor_set(v_reuseFailAlloc_783_, 12, v_natCastFn_x3f_773_);
lean_ctor_set(v_reuseFailAlloc_783_, 13, v_natSMulFn_x3f_774_);
lean_ctor_set(v_reuseFailAlloc_783_, 14, v_intSMulFn_x3f_775_);
lean_ctor_set(v_reuseFailAlloc_783_, 15, v_one_x3f_776_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object* v_toPure_786_, lean_object* v_mulFn_787_, lean_object* v_____r_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = lean_apply_2(v_toPure_786_, lean_box(0), v_mulFn_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object* v_toPure_790_, lean_object* v_modifyRing_791_, lean_object* v_toBind_792_, lean_object* v_mulFn_793_){
_start:
{
lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_inc_ref(v_mulFn_793_);
v___f_794_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_794_, 0, v_mulFn_793_);
v___f_795_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_795_, 0, v_toPure_790_);
lean_closure_set(v___f_795_, 1, v_mulFn_793_);
v___x_796_ = lean_apply_1(v_modifyRing_791_, v___f_794_);
v___x_797_ = lean_apply_4(v_toBind_792_, lean_box(0), lean_box(0), v___x_796_, v___f_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object* v_toPure_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_toBind_819_, lean_object* v___f_820_, lean_object* v_ring_821_){
_start:
{
lean_object* v_mulFn_x3f_822_; 
v_mulFn_x3f_822_ = lean_ctor_get(v_ring_821_, 7);
if (lean_obj_tag(v_mulFn_x3f_822_) == 1)
{
lean_object* v_val_823_; lean_object* v___x_824_; 
lean_inc_ref(v_mulFn_x3f_822_);
lean_dec_ref(v_ring_821_);
lean_dec(v___f_820_);
lean_dec(v_toBind_819_);
lean_dec_ref(v_inst_818_);
lean_dec_ref(v_inst_817_);
lean_dec_ref(v_inst_816_);
lean_dec(v_inst_815_);
v_val_823_ = lean_ctor_get(v_mulFn_x3f_822_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v_mulFn_x3f_822_, 1);
v___x_824_ = lean_apply_2(v_toPure_814_, lean_box(0), v_val_823_);
return v___x_824_;
}
else
{
lean_object* v_type_825_; lean_object* v_u_826_; lean_object* v_semiringInst_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_expectedInst_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_toPure_814_);
v_type_825_ = lean_ctor_get(v_ring_821_, 1);
lean_inc_ref_n(v_type_825_, 3);
v_u_826_ = lean_ctor_get(v_ring_821_, 2);
lean_inc_n(v_u_826_, 2);
v_semiringInst_827_ = lean_ctor_get(v_ring_821_, 4);
lean_inc_ref(v_semiringInst_827_);
lean_dec_ref(v_ring_821_);
v___x_828_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_829_ = lean_box(0);
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v_u_826_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
lean_inc_ref(v___x_830_);
v___x_831_ = l_Lean_mkConst(v___x_828_, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_833_ = l_Lean_mkConst(v___x_832_, v___x_830_);
v___x_834_ = l_Lean_mkAppB(v___x_833_, v_type_825_, v_semiringInst_827_);
v_expectedInst_835_ = l_Lean_mkAppB(v___x_831_, v_type_825_, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_837_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_838_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_815_, v_inst_816_, v_inst_817_, v_inst_818_, v_type_825_, v_u_826_, v___x_836_, v___x_837_, v_expectedInst_835_);
v___x_839_ = lean_apply_4(v_toBind_819_, lean_box(0), lean_box(0), v___x_838_, v___f_820_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_){
_start:
{
lean_object* v_toApplicative_845_; lean_object* v_toBind_846_; lean_object* v_getRing_847_; lean_object* v_modifyRing_848_; lean_object* v_toPure_849_; lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___x_852_; 
v_toApplicative_845_ = lean_ctor_get(v_inst_842_, 0);
v_toBind_846_ = lean_ctor_get(v_inst_842_, 1);
lean_inc_n(v_toBind_846_, 3);
v_getRing_847_ = lean_ctor_get(v_inst_844_, 0);
lean_inc(v_getRing_847_);
v_modifyRing_848_ = lean_ctor_get(v_inst_844_, 1);
lean_inc(v_modifyRing_848_);
lean_dec_ref(v_inst_844_);
v_toPure_849_ = lean_ctor_get(v_toApplicative_845_, 1);
lean_inc_n(v_toPure_849_, 2);
v___f_850_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_850_, 0, v_toPure_849_);
lean_closure_set(v___f_850_, 1, v_modifyRing_848_);
lean_closure_set(v___f_850_, 2, v_toBind_846_);
v___f_851_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_851_, 0, v_toPure_849_);
lean_closure_set(v___f_851_, 1, v_inst_840_);
lean_closure_set(v___f_851_, 2, v_inst_841_);
lean_closure_set(v___f_851_, 3, v_inst_842_);
lean_closure_set(v___f_851_, 4, v_inst_843_);
lean_closure_set(v___f_851_, 5, v_toBind_846_);
lean_closure_set(v___f_851_, 6, v___f_850_);
v___x_852_ = lean_apply_4(v_toBind_846_, lean_box(0), lean_box(0), v_getRing_847_, v___f_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object* v_m_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_854_, v_inst_855_, v_inst_856_, v_inst_857_, v_inst_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object* v_subFn_860_, lean_object* v_s_861_){
_start:
{
lean_object* v_id_862_; lean_object* v_type_863_; lean_object* v_u_864_; lean_object* v_ringInst_865_; lean_object* v_semiringInst_866_; lean_object* v_charInst_x3f_867_; lean_object* v_addFn_x3f_868_; lean_object* v_mulFn_x3f_869_; lean_object* v_negFn_x3f_870_; lean_object* v_powFn_x3f_871_; lean_object* v_intCastFn_x3f_872_; lean_object* v_natCastFn_x3f_873_; lean_object* v_natSMulFn_x3f_874_; lean_object* v_intSMulFn_x3f_875_; lean_object* v_one_x3f_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
v_id_862_ = lean_ctor_get(v_s_861_, 0);
v_type_863_ = lean_ctor_get(v_s_861_, 1);
v_u_864_ = lean_ctor_get(v_s_861_, 2);
v_ringInst_865_ = lean_ctor_get(v_s_861_, 3);
v_semiringInst_866_ = lean_ctor_get(v_s_861_, 4);
v_charInst_x3f_867_ = lean_ctor_get(v_s_861_, 5);
v_addFn_x3f_868_ = lean_ctor_get(v_s_861_, 6);
v_mulFn_x3f_869_ = lean_ctor_get(v_s_861_, 7);
v_negFn_x3f_870_ = lean_ctor_get(v_s_861_, 9);
v_powFn_x3f_871_ = lean_ctor_get(v_s_861_, 10);
v_intCastFn_x3f_872_ = lean_ctor_get(v_s_861_, 11);
v_natCastFn_x3f_873_ = lean_ctor_get(v_s_861_, 12);
v_natSMulFn_x3f_874_ = lean_ctor_get(v_s_861_, 13);
v_intSMulFn_x3f_875_ = lean_ctor_get(v_s_861_, 14);
v_one_x3f_876_ = lean_ctor_get(v_s_861_, 15);
v_isSharedCheck_884_ = !lean_is_exclusive(v_s_861_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_s_861_, 8);
lean_dec(v_unused_885_);
v___x_878_ = v_s_861_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_one_x3f_876_);
lean_inc(v_intSMulFn_x3f_875_);
lean_inc(v_natSMulFn_x3f_874_);
lean_inc(v_natCastFn_x3f_873_);
lean_inc(v_intCastFn_x3f_872_);
lean_inc(v_powFn_x3f_871_);
lean_inc(v_negFn_x3f_870_);
lean_inc(v_mulFn_x3f_869_);
lean_inc(v_addFn_x3f_868_);
lean_inc(v_charInst_x3f_867_);
lean_inc(v_semiringInst_866_);
lean_inc(v_ringInst_865_);
lean_inc(v_u_864_);
lean_inc(v_type_863_);
lean_inc(v_id_862_);
lean_dec(v_s_861_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_880_, 0, v_subFn_860_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 8, v___x_880_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_id_862_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_type_863_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_u_864_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_ringInst_865_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v_semiringInst_866_);
lean_ctor_set(v_reuseFailAlloc_883_, 5, v_charInst_x3f_867_);
lean_ctor_set(v_reuseFailAlloc_883_, 6, v_addFn_x3f_868_);
lean_ctor_set(v_reuseFailAlloc_883_, 7, v_mulFn_x3f_869_);
lean_ctor_set(v_reuseFailAlloc_883_, 8, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_883_, 9, v_negFn_x3f_870_);
lean_ctor_set(v_reuseFailAlloc_883_, 10, v_powFn_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_883_, 11, v_intCastFn_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_883_, 12, v_natCastFn_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_883_, 13, v_natSMulFn_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_883_, 14, v_intSMulFn_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_883_, 15, v_one_x3f_876_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_886_, lean_object* v_subFn_887_, lean_object* v_____r_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = lean_apply_2(v_toPure_886_, lean_box(0), v_subFn_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_890_, lean_object* v_modifyRing_891_, lean_object* v_toBind_892_, lean_object* v_subFn_893_){
_start:
{
lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_inc_ref(v_subFn_893_);
v___f_894_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_894_, 0, v_subFn_893_);
v___f_895_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_895_, 0, v_toPure_890_);
lean_closure_set(v___f_895_, 1, v_subFn_893_);
v___x_896_ = lean_apply_1(v_modifyRing_891_, v___f_894_);
v___x_897_ = lean_apply_4(v_toBind_892_, lean_box(0), lean_box(0), v___x_896_, v___f_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_toBind_919_, lean_object* v___f_920_, lean_object* v_ring_921_){
_start:
{
lean_object* v_subFn_x3f_922_; 
v_subFn_x3f_922_ = lean_ctor_get(v_ring_921_, 8);
if (lean_obj_tag(v_subFn_x3f_922_) == 1)
{
lean_object* v_val_923_; lean_object* v___x_924_; 
lean_inc_ref(v_subFn_x3f_922_);
lean_dec_ref(v_ring_921_);
lean_dec(v___f_920_);
lean_dec(v_toBind_919_);
lean_dec_ref(v_inst_918_);
lean_dec_ref(v_inst_917_);
lean_dec_ref(v_inst_916_);
lean_dec(v_inst_915_);
v_val_923_ = lean_ctor_get(v_subFn_x3f_922_, 0);
lean_inc(v_val_923_);
lean_dec_ref_known(v_subFn_x3f_922_, 1);
v___x_924_ = lean_apply_2(v_toPure_914_, lean_box(0), v_val_923_);
return v___x_924_;
}
else
{
lean_object* v_type_925_; lean_object* v_u_926_; lean_object* v_ringInst_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_expectedInst_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v_toPure_914_);
v_type_925_ = lean_ctor_get(v_ring_921_, 1);
lean_inc_ref_n(v_type_925_, 3);
v_u_926_ = lean_ctor_get(v_ring_921_, 2);
lean_inc_n(v_u_926_, 2);
v_ringInst_927_ = lean_ctor_get(v_ring_921_, 3);
lean_inc_ref(v_ringInst_927_);
lean_dec_ref(v_ring_921_);
v___x_928_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_929_ = lean_box(0);
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v_u_926_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
lean_inc_ref(v___x_930_);
v___x_931_ = l_Lean_mkConst(v___x_928_, v___x_930_);
v___x_932_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3));
v___x_933_ = l_Lean_mkConst(v___x_932_, v___x_930_);
v___x_934_ = l_Lean_mkAppB(v___x_933_, v_type_925_, v_ringInst_927_);
v_expectedInst_935_ = l_Lean_mkAppB(v___x_931_, v_type_925_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5));
v___x_937_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7));
v___x_938_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_915_, v_inst_916_, v_inst_917_, v_inst_918_, v_type_925_, v_u_926_, v___x_936_, v___x_937_, v_expectedInst_935_);
v___x_939_ = lean_apply_4(v_toBind_919_, lean_box(0), lean_box(0), v___x_938_, v___f_920_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_inst_944_){
_start:
{
lean_object* v_toApplicative_945_; lean_object* v_toBind_946_; lean_object* v_getRing_947_; lean_object* v_modifyRing_948_; lean_object* v_toPure_949_; lean_object* v___f_950_; lean_object* v___f_951_; lean_object* v___x_952_; 
v_toApplicative_945_ = lean_ctor_get(v_inst_942_, 0);
v_toBind_946_ = lean_ctor_get(v_inst_942_, 1);
lean_inc_n(v_toBind_946_, 3);
v_getRing_947_ = lean_ctor_get(v_inst_944_, 0);
lean_inc(v_getRing_947_);
v_modifyRing_948_ = lean_ctor_get(v_inst_944_, 1);
lean_inc(v_modifyRing_948_);
lean_dec_ref(v_inst_944_);
v_toPure_949_ = lean_ctor_get(v_toApplicative_945_, 1);
lean_inc_n(v_toPure_949_, 2);
v___f_950_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_950_, 0, v_toPure_949_);
lean_closure_set(v___f_950_, 1, v_modifyRing_948_);
lean_closure_set(v___f_950_, 2, v_toBind_946_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_951_, 0, v_toPure_949_);
lean_closure_set(v___f_951_, 1, v_inst_940_);
lean_closure_set(v___f_951_, 2, v_inst_941_);
lean_closure_set(v___f_951_, 3, v_inst_942_);
lean_closure_set(v___f_951_, 4, v_inst_943_);
lean_closure_set(v___f_951_, 5, v_toBind_946_);
lean_closure_set(v___f_951_, 6, v___f_950_);
v___x_952_ = lean_apply_4(v_toBind_946_, lean_box(0), lean_box(0), v_getRing_947_, v___f_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_953_, lean_object* v_inst_954_, lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_inst_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_954_, v_inst_955_, v_inst_956_, v_inst_957_, v_inst_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_960_, lean_object* v_s_961_){
_start:
{
lean_object* v_id_962_; lean_object* v_type_963_; lean_object* v_u_964_; lean_object* v_ringInst_965_; lean_object* v_semiringInst_966_; lean_object* v_charInst_x3f_967_; lean_object* v_addFn_x3f_968_; lean_object* v_mulFn_x3f_969_; lean_object* v_subFn_x3f_970_; lean_object* v_powFn_x3f_971_; lean_object* v_intCastFn_x3f_972_; lean_object* v_natCastFn_x3f_973_; lean_object* v_natSMulFn_x3f_974_; lean_object* v_intSMulFn_x3f_975_; lean_object* v_one_x3f_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_984_; 
v_id_962_ = lean_ctor_get(v_s_961_, 0);
v_type_963_ = lean_ctor_get(v_s_961_, 1);
v_u_964_ = lean_ctor_get(v_s_961_, 2);
v_ringInst_965_ = lean_ctor_get(v_s_961_, 3);
v_semiringInst_966_ = lean_ctor_get(v_s_961_, 4);
v_charInst_x3f_967_ = lean_ctor_get(v_s_961_, 5);
v_addFn_x3f_968_ = lean_ctor_get(v_s_961_, 6);
v_mulFn_x3f_969_ = lean_ctor_get(v_s_961_, 7);
v_subFn_x3f_970_ = lean_ctor_get(v_s_961_, 8);
v_powFn_x3f_971_ = lean_ctor_get(v_s_961_, 10);
v_intCastFn_x3f_972_ = lean_ctor_get(v_s_961_, 11);
v_natCastFn_x3f_973_ = lean_ctor_get(v_s_961_, 12);
v_natSMulFn_x3f_974_ = lean_ctor_get(v_s_961_, 13);
v_intSMulFn_x3f_975_ = lean_ctor_get(v_s_961_, 14);
v_one_x3f_976_ = lean_ctor_get(v_s_961_, 15);
v_isSharedCheck_984_ = !lean_is_exclusive(v_s_961_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; 
v_unused_985_ = lean_ctor_get(v_s_961_, 9);
lean_dec(v_unused_985_);
v___x_978_ = v_s_961_;
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_one_x3f_976_);
lean_inc(v_intSMulFn_x3f_975_);
lean_inc(v_natSMulFn_x3f_974_);
lean_inc(v_natCastFn_x3f_973_);
lean_inc(v_intCastFn_x3f_972_);
lean_inc(v_powFn_x3f_971_);
lean_inc(v_subFn_x3f_970_);
lean_inc(v_mulFn_x3f_969_);
lean_inc(v_addFn_x3f_968_);
lean_inc(v_charInst_x3f_967_);
lean_inc(v_semiringInst_966_);
lean_inc(v_ringInst_965_);
lean_inc(v_u_964_);
lean_inc(v_type_963_);
lean_inc(v_id_962_);
lean_dec(v_s_961_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v_negFn_960_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 9, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_id_962_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_type_963_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_u_964_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v_ringInst_965_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v_semiringInst_966_);
lean_ctor_set(v_reuseFailAlloc_983_, 5, v_charInst_x3f_967_);
lean_ctor_set(v_reuseFailAlloc_983_, 6, v_addFn_x3f_968_);
lean_ctor_set(v_reuseFailAlloc_983_, 7, v_mulFn_x3f_969_);
lean_ctor_set(v_reuseFailAlloc_983_, 8, v_subFn_x3f_970_);
lean_ctor_set(v_reuseFailAlloc_983_, 9, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_983_, 10, v_powFn_x3f_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 11, v_intCastFn_x3f_972_);
lean_ctor_set(v_reuseFailAlloc_983_, 12, v_natCastFn_x3f_973_);
lean_ctor_set(v_reuseFailAlloc_983_, 13, v_natSMulFn_x3f_974_);
lean_ctor_set(v_reuseFailAlloc_983_, 14, v_intSMulFn_x3f_975_);
lean_ctor_set(v_reuseFailAlloc_983_, 15, v_one_x3f_976_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_986_, lean_object* v_negFn_987_, lean_object* v_____r_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_apply_2(v_toPure_986_, lean_box(0), v_negFn_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_990_, lean_object* v_modifyRing_991_, lean_object* v_toBind_992_, lean_object* v_negFn_993_){
_start:
{
lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_inc_ref(v_negFn_993_);
v___f_994_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_994_, 0, v_negFn_993_);
v___f_995_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_995_, 0, v_toPure_990_);
lean_closure_set(v___f_995_, 1, v_negFn_993_);
v___x_996_ = lean_apply_1(v_modifyRing_991_, v___f_994_);
v___x_997_ = lean_apply_4(v_toBind_992_, lean_box(0), lean_box(0), v___x_996_, v___f_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_toBind_1016_, lean_object* v___f_1017_, lean_object* v_ring_1018_){
_start:
{
lean_object* v_negFn_x3f_1019_; 
v_negFn_x3f_1019_ = lean_ctor_get(v_ring_1018_, 9);
if (lean_obj_tag(v_negFn_x3f_1019_) == 1)
{
lean_object* v_val_1020_; lean_object* v___x_1021_; 
lean_inc_ref(v_negFn_x3f_1019_);
lean_dec_ref(v_ring_1018_);
lean_dec(v___f_1017_);
lean_dec(v_toBind_1016_);
lean_dec_ref(v_inst_1015_);
lean_dec_ref(v_inst_1014_);
lean_dec_ref(v_inst_1013_);
lean_dec(v_inst_1012_);
v_val_1020_ = lean_ctor_get(v_negFn_x3f_1019_, 0);
lean_inc(v_val_1020_);
lean_dec_ref_known(v_negFn_x3f_1019_, 1);
v___x_1021_ = lean_apply_2(v_toPure_1011_, lean_box(0), v_val_1020_);
return v___x_1021_;
}
else
{
lean_object* v_type_1022_; lean_object* v_u_1023_; lean_object* v_ringInst_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_expectedInst_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v_toPure_1011_);
v_type_1022_ = lean_ctor_get(v_ring_1018_, 1);
lean_inc_ref_n(v_type_1022_, 2);
v_u_1023_ = lean_ctor_get(v_ring_1018_, 2);
lean_inc_n(v_u_1023_, 2);
v_ringInst_1024_ = lean_ctor_get(v_ring_1018_, 3);
lean_inc_ref(v_ringInst_1024_);
lean_dec_ref(v_ring_1018_);
v___x_1025_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_u_1023_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_mkConst(v___x_1025_, v___x_1027_);
v_expectedInst_1029_ = l_Lean_mkAppB(v___x_1028_, v_type_1022_, v_ringInst_1024_);
v___x_1030_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_1031_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_1032_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1012_, v_inst_1013_, v_inst_1014_, v_inst_1015_, v_type_1022_, v_u_1023_, v___x_1030_, v___x_1031_, v_expectedInst_1029_);
v___x_1033_ = lean_apply_4(v_toBind_1016_, lean_box(0), lean_box(0), v___x_1032_, v___f_1017_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_){
_start:
{
lean_object* v_toApplicative_1039_; lean_object* v_toBind_1040_; lean_object* v_getRing_1041_; lean_object* v_modifyRing_1042_; lean_object* v_toPure_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; 
v_toApplicative_1039_ = lean_ctor_get(v_inst_1036_, 0);
v_toBind_1040_ = lean_ctor_get(v_inst_1036_, 1);
lean_inc_n(v_toBind_1040_, 3);
v_getRing_1041_ = lean_ctor_get(v_inst_1038_, 0);
lean_inc(v_getRing_1041_);
v_modifyRing_1042_ = lean_ctor_get(v_inst_1038_, 1);
lean_inc(v_modifyRing_1042_);
lean_dec_ref(v_inst_1038_);
v_toPure_1043_ = lean_ctor_get(v_toApplicative_1039_, 1);
lean_inc_n(v_toPure_1043_, 2);
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1044_, 0, v_toPure_1043_);
lean_closure_set(v___f_1044_, 1, v_modifyRing_1042_);
lean_closure_set(v___f_1044_, 2, v_toBind_1040_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1045_, 0, v_toPure_1043_);
lean_closure_set(v___f_1045_, 1, v_inst_1034_);
lean_closure_set(v___f_1045_, 2, v_inst_1035_);
lean_closure_set(v___f_1045_, 3, v_inst_1036_);
lean_closure_set(v___f_1045_, 4, v_inst_1037_);
lean_closure_set(v___f_1045_, 5, v_toBind_1040_);
lean_closure_set(v___f_1045_, 6, v___f_1044_);
v___x_1046_ = lean_apply_4(v_toBind_1040_, lean_box(0), lean_box(0), v_getRing_1041_, v___f_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_1048_, v_inst_1049_, v_inst_1050_, v_inst_1051_, v_inst_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_1054_, lean_object* v_s_1055_){
_start:
{
lean_object* v_id_1056_; lean_object* v_type_1057_; lean_object* v_u_1058_; lean_object* v_ringInst_1059_; lean_object* v_semiringInst_1060_; lean_object* v_charInst_x3f_1061_; lean_object* v_addFn_x3f_1062_; lean_object* v_mulFn_x3f_1063_; lean_object* v_subFn_x3f_1064_; lean_object* v_negFn_x3f_1065_; lean_object* v_intCastFn_x3f_1066_; lean_object* v_natCastFn_x3f_1067_; lean_object* v_natSMulFn_x3f_1068_; lean_object* v_intSMulFn_x3f_1069_; lean_object* v_one_x3f_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_id_1056_ = lean_ctor_get(v_s_1055_, 0);
v_type_1057_ = lean_ctor_get(v_s_1055_, 1);
v_u_1058_ = lean_ctor_get(v_s_1055_, 2);
v_ringInst_1059_ = lean_ctor_get(v_s_1055_, 3);
v_semiringInst_1060_ = lean_ctor_get(v_s_1055_, 4);
v_charInst_x3f_1061_ = lean_ctor_get(v_s_1055_, 5);
v_addFn_x3f_1062_ = lean_ctor_get(v_s_1055_, 6);
v_mulFn_x3f_1063_ = lean_ctor_get(v_s_1055_, 7);
v_subFn_x3f_1064_ = lean_ctor_get(v_s_1055_, 8);
v_negFn_x3f_1065_ = lean_ctor_get(v_s_1055_, 9);
v_intCastFn_x3f_1066_ = lean_ctor_get(v_s_1055_, 11);
v_natCastFn_x3f_1067_ = lean_ctor_get(v_s_1055_, 12);
v_natSMulFn_x3f_1068_ = lean_ctor_get(v_s_1055_, 13);
v_intSMulFn_x3f_1069_ = lean_ctor_get(v_s_1055_, 14);
v_one_x3f_1070_ = lean_ctor_get(v_s_1055_, 15);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_s_1055_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_s_1055_, 10);
lean_dec(v_unused_1079_);
v___x_1072_ = v_s_1055_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_one_x3f_1070_);
lean_inc(v_intSMulFn_x3f_1069_);
lean_inc(v_natSMulFn_x3f_1068_);
lean_inc(v_natCastFn_x3f_1067_);
lean_inc(v_intCastFn_x3f_1066_);
lean_inc(v_negFn_x3f_1065_);
lean_inc(v_subFn_x3f_1064_);
lean_inc(v_mulFn_x3f_1063_);
lean_inc(v_addFn_x3f_1062_);
lean_inc(v_charInst_x3f_1061_);
lean_inc(v_semiringInst_1060_);
lean_inc(v_ringInst_1059_);
lean_inc(v_u_1058_);
lean_inc(v_type_1057_);
lean_inc(v_id_1056_);
lean_dec(v_s_1055_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_powFn_1054_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 10, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_id_1056_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_type_1057_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_u_1058_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v_ringInst_1059_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_semiringInst_1060_);
lean_ctor_set(v_reuseFailAlloc_1077_, 5, v_charInst_x3f_1061_);
lean_ctor_set(v_reuseFailAlloc_1077_, 6, v_addFn_x3f_1062_);
lean_ctor_set(v_reuseFailAlloc_1077_, 7, v_mulFn_x3f_1063_);
lean_ctor_set(v_reuseFailAlloc_1077_, 8, v_subFn_x3f_1064_);
lean_ctor_set(v_reuseFailAlloc_1077_, 9, v_negFn_x3f_1065_);
lean_ctor_set(v_reuseFailAlloc_1077_, 10, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1077_, 11, v_intCastFn_x3f_1066_);
lean_ctor_set(v_reuseFailAlloc_1077_, 12, v_natCastFn_x3f_1067_);
lean_ctor_set(v_reuseFailAlloc_1077_, 13, v_natSMulFn_x3f_1068_);
lean_ctor_set(v_reuseFailAlloc_1077_, 14, v_intSMulFn_x3f_1069_);
lean_ctor_set(v_reuseFailAlloc_1077_, 15, v_one_x3f_1070_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_1080_, lean_object* v_powFn_1081_, lean_object* v_____r_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_apply_2(v_toPure_1080_, lean_box(0), v_powFn_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_1084_, lean_object* v_modifyRing_1085_, lean_object* v_toBind_1086_, lean_object* v_powFn_1087_){
_start:
{
lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_inc_ref(v_powFn_1087_);
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1088_, 0, v_powFn_1087_);
v___f_1089_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1089_, 0, v_toPure_1084_);
lean_closure_set(v___f_1089_, 1, v_powFn_1087_);
v___x_1090_ = lean_apply_1(v_modifyRing_1085_, v___f_1088_);
v___x_1091_ = lean_apply_4(v_toBind_1086_, lean_box(0), lean_box(0), v___x_1090_, v___f_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_toBind_1097_, lean_object* v___f_1098_, lean_object* v_ring_1099_){
_start:
{
lean_object* v_powFn_x3f_1100_; 
v_powFn_x3f_1100_ = lean_ctor_get(v_ring_1099_, 10);
if (lean_obj_tag(v_powFn_x3f_1100_) == 1)
{
lean_object* v_val_1101_; lean_object* v___x_1102_; 
lean_inc_ref(v_powFn_x3f_1100_);
lean_dec_ref(v_ring_1099_);
lean_dec(v___f_1098_);
lean_dec(v_toBind_1097_);
lean_dec_ref(v_inst_1096_);
lean_dec_ref(v_inst_1095_);
lean_dec_ref(v_inst_1094_);
lean_dec(v_inst_1093_);
v_val_1101_ = lean_ctor_get(v_powFn_x3f_1100_, 0);
lean_inc(v_val_1101_);
lean_dec_ref_known(v_powFn_x3f_1100_, 1);
v___x_1102_ = lean_apply_2(v_toPure_1092_, lean_box(0), v_val_1101_);
return v___x_1102_;
}
else
{
lean_object* v_type_1103_; lean_object* v_u_1104_; lean_object* v_semiringInst_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec(v_toPure_1092_);
v_type_1103_ = lean_ctor_get(v_ring_1099_, 1);
lean_inc_ref(v_type_1103_);
v_u_1104_ = lean_ctor_get(v_ring_1099_, 2);
lean_inc(v_u_1104_);
v_semiringInst_1105_ = lean_ctor_get(v_ring_1099_, 4);
lean_inc_ref(v_semiringInst_1105_);
lean_dec_ref(v_ring_1099_);
v___x_1106_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1093_, v_inst_1094_, v_inst_1095_, v_inst_1096_, v_u_1104_, v_type_1103_, v_semiringInst_1105_);
v___x_1107_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v___x_1106_, v___f_1098_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_){
_start:
{
lean_object* v_toApplicative_1113_; lean_object* v_toBind_1114_; lean_object* v_getRing_1115_; lean_object* v_modifyRing_1116_; lean_object* v_toPure_1117_; lean_object* v___f_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; 
v_toApplicative_1113_ = lean_ctor_get(v_inst_1110_, 0);
v_toBind_1114_ = lean_ctor_get(v_inst_1110_, 1);
lean_inc_n(v_toBind_1114_, 3);
v_getRing_1115_ = lean_ctor_get(v_inst_1112_, 0);
lean_inc(v_getRing_1115_);
v_modifyRing_1116_ = lean_ctor_get(v_inst_1112_, 1);
lean_inc(v_modifyRing_1116_);
lean_dec_ref(v_inst_1112_);
v_toPure_1117_ = lean_ctor_get(v_toApplicative_1113_, 1);
lean_inc_n(v_toPure_1117_, 2);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1118_, 0, v_toPure_1117_);
lean_closure_set(v___f_1118_, 1, v_modifyRing_1116_);
lean_closure_set(v___f_1118_, 2, v_toBind_1114_);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1119_, 0, v_toPure_1117_);
lean_closure_set(v___f_1119_, 1, v_inst_1108_);
lean_closure_set(v___f_1119_, 2, v_inst_1109_);
lean_closure_set(v___f_1119_, 3, v_inst_1110_);
lean_closure_set(v___f_1119_, 4, v_inst_1111_);
lean_closure_set(v___f_1119_, 5, v_toBind_1114_);
lean_closure_set(v___f_1119_, 6, v___f_1118_);
v___x_1120_ = lean_apply_4(v_toBind_1114_, lean_box(0), lean_box(0), v_getRing_1115_, v___f_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_1122_, v_inst_1123_, v_inst_1124_, v_inst_1125_, v_inst_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_1128_, lean_object* v_s_1129_){
_start:
{
lean_object* v_id_1130_; lean_object* v_type_1131_; lean_object* v_u_1132_; lean_object* v_ringInst_1133_; lean_object* v_semiringInst_1134_; lean_object* v_charInst_x3f_1135_; lean_object* v_addFn_x3f_1136_; lean_object* v_mulFn_x3f_1137_; lean_object* v_subFn_x3f_1138_; lean_object* v_negFn_x3f_1139_; lean_object* v_powFn_x3f_1140_; lean_object* v_natCastFn_x3f_1141_; lean_object* v_natSMulFn_x3f_1142_; lean_object* v_intSMulFn_x3f_1143_; lean_object* v_one_x3f_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
v_id_1130_ = lean_ctor_get(v_s_1129_, 0);
v_type_1131_ = lean_ctor_get(v_s_1129_, 1);
v_u_1132_ = lean_ctor_get(v_s_1129_, 2);
v_ringInst_1133_ = lean_ctor_get(v_s_1129_, 3);
v_semiringInst_1134_ = lean_ctor_get(v_s_1129_, 4);
v_charInst_x3f_1135_ = lean_ctor_get(v_s_1129_, 5);
v_addFn_x3f_1136_ = lean_ctor_get(v_s_1129_, 6);
v_mulFn_x3f_1137_ = lean_ctor_get(v_s_1129_, 7);
v_subFn_x3f_1138_ = lean_ctor_get(v_s_1129_, 8);
v_negFn_x3f_1139_ = lean_ctor_get(v_s_1129_, 9);
v_powFn_x3f_1140_ = lean_ctor_get(v_s_1129_, 10);
v_natCastFn_x3f_1141_ = lean_ctor_get(v_s_1129_, 12);
v_natSMulFn_x3f_1142_ = lean_ctor_get(v_s_1129_, 13);
v_intSMulFn_x3f_1143_ = lean_ctor_get(v_s_1129_, 14);
v_one_x3f_1144_ = lean_ctor_get(v_s_1129_, 15);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_s_1129_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v_s_1129_, 11);
lean_dec(v_unused_1153_);
v___x_1146_ = v_s_1129_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_one_x3f_1144_);
lean_inc(v_intSMulFn_x3f_1143_);
lean_inc(v_natSMulFn_x3f_1142_);
lean_inc(v_natCastFn_x3f_1141_);
lean_inc(v_powFn_x3f_1140_);
lean_inc(v_negFn_x3f_1139_);
lean_inc(v_subFn_x3f_1138_);
lean_inc(v_mulFn_x3f_1137_);
lean_inc(v_addFn_x3f_1136_);
lean_inc(v_charInst_x3f_1135_);
lean_inc(v_semiringInst_1134_);
lean_inc(v_ringInst_1133_);
lean_inc(v_u_1132_);
lean_inc(v_type_1131_);
lean_inc(v_id_1130_);
lean_dec(v_s_1129_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_intCastFn_1128_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 11, v___x_1148_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_id_1130_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_type_1131_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_u_1132_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_ringInst_1133_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_semiringInst_1134_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v_charInst_x3f_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 6, v_addFn_x3f_1136_);
lean_ctor_set(v_reuseFailAlloc_1151_, 7, v_mulFn_x3f_1137_);
lean_ctor_set(v_reuseFailAlloc_1151_, 8, v_subFn_x3f_1138_);
lean_ctor_set(v_reuseFailAlloc_1151_, 9, v_negFn_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1151_, 10, v_powFn_x3f_1140_);
lean_ctor_set(v_reuseFailAlloc_1151_, 11, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1151_, 12, v_natCastFn_x3f_1141_);
lean_ctor_set(v_reuseFailAlloc_1151_, 13, v_natSMulFn_x3f_1142_);
lean_ctor_set(v_reuseFailAlloc_1151_, 14, v_intSMulFn_x3f_1143_);
lean_ctor_set(v_reuseFailAlloc_1151_, 15, v_one_x3f_1144_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_1154_, lean_object* v_intCastFn_1155_, lean_object* v_____r_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_apply_2(v_toPure_1154_, lean_box(0), v_intCastFn_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_1158_, lean_object* v_modifyRing_1159_, lean_object* v_toBind_1160_, lean_object* v_intCastFn_1161_){
_start:
{
lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_inc_ref(v_intCastFn_1161_);
v___f_1162_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1162_, 0, v_intCastFn_1161_);
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1163_, 0, v_toPure_1158_);
lean_closure_set(v___f_1163_, 1, v_intCastFn_1161_);
v___x_1164_ = lean_apply_1(v_modifyRing_1159_, v___f_1162_);
v___x_1165_ = lean_apply_4(v_toBind_1160_, lean_box(0), lean_box(0), v___x_1164_, v___f_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_1166_, lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_type_1169_, lean_object* v_canonExpr_1170_, lean_object* v_toBind_1171_, lean_object* v___f_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1174_ = l_Lean_Name_mkStr2(v___x_1166_, v___x_1167_);
v___x_1175_ = l_Lean_mkConst(v___x_1174_, v___x_1168_);
v___x_1176_ = l_Lean_mkAppB(v___x_1175_, v_type_1169_, v_inst_1173_);
v___x_1177_ = lean_apply_1(v_canonExpr_1170_, v___x_1176_);
v___x_1178_ = lean_apply_4(v_toBind_1171_, lean_box(0), lean_box(0), v___x_1177_, v___f_1172_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_1184_, lean_object* v_inst_x27_1185_, lean_object* v_toBind_1186_, lean_object* v___f_1187_, lean_object* v___f_1188_, lean_object* v_inst_1189_, lean_object* v_____do__lift_1190_){
_start:
{
if (lean_obj_tag(v_____do__lift_1190_) == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v_inst_1189_);
lean_dec(v___f_1188_);
v___x_1191_ = lean_apply_2(v_toPure_1184_, lean_box(0), v_inst_x27_1185_);
v___x_1192_ = lean_apply_4(v_toBind_1186_, lean_box(0), lean_box(0), v___x_1191_, v___f_1187_);
return v___x_1192_;
}
else
{
lean_object* v_val_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec(v___f_1187_);
v_val_1193_ = lean_ctor_get(v_____do__lift_1190_, 0);
lean_inc_n(v_val_1193_, 2);
lean_dec_ref_known(v_____do__lift_1190_, 1);
lean_inc(v_toBind_1186_);
v___f_1194_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1194_, 0, v_toPure_1184_);
lean_closure_set(v___f_1194_, 1, v_val_1193_);
lean_closure_set(v___f_1194_, 2, v_toBind_1186_);
lean_closure_set(v___f_1194_, 3, v___f_1188_);
v___x_1195_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_1196_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_1196_, 0, v___x_1195_);
lean_closure_set(v___x_1196_, 1, v_val_1193_);
lean_closure_set(v___x_1196_, 2, v_inst_x27_1185_);
v___x_1197_ = lean_apply_2(v_inst_1189_, lean_box(0), v___x_1196_);
v___x_1198_ = lean_apply_4(v_toBind_1186_, lean_box(0), lean_box(0), v___x_1197_, v___f_1194_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_1208_, lean_object* v_inst_1209_, lean_object* v_toBind_1210_, lean_object* v___f_1211_, lean_object* v_inst_1212_, lean_object* v_ring_1213_){
_start:
{
lean_object* v_intCastFn_x3f_1214_; 
v_intCastFn_x3f_1214_ = lean_ctor_get(v_ring_1213_, 11);
if (lean_obj_tag(v_intCastFn_x3f_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1216_; 
lean_inc_ref(v_intCastFn_x3f_1214_);
lean_dec_ref(v_ring_1213_);
lean_dec(v_inst_1212_);
lean_dec(v___f_1211_);
lean_dec(v_toBind_1210_);
lean_dec_ref(v_inst_1209_);
v_val_1215_ = lean_ctor_get(v_intCastFn_x3f_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v_intCastFn_x3f_1214_, 1);
v___x_1216_ = lean_apply_2(v_toPure_1208_, lean_box(0), v_val_1215_);
return v___x_1216_;
}
else
{
lean_object* v_type_1217_; lean_object* v_u_1218_; lean_object* v_ringInst_1219_; lean_object* v_canonExpr_1220_; lean_object* v_synthInstance_x3f_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1242_; 
v_type_1217_ = lean_ctor_get(v_ring_1213_, 1);
lean_inc_ref(v_type_1217_);
v_u_1218_ = lean_ctor_get(v_ring_1213_, 2);
lean_inc(v_u_1218_);
v_ringInst_1219_ = lean_ctor_get(v_ring_1213_, 3);
lean_inc_ref(v_ringInst_1219_);
lean_dec_ref(v_ring_1213_);
v_canonExpr_1220_ = lean_ctor_get(v_inst_1209_, 0);
v_synthInstance_x3f_1221_ = lean_ctor_get(v_inst_1209_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_inst_1209_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1223_ = v_inst_1209_;
v_isShared_1224_ = v_isSharedCheck_1242_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_synthInstance_x3f_1221_);
lean_inc(v_canonExpr_1220_);
lean_dec(v_inst_1209_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1242_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1225_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_1226_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_1227_ = lean_box(0);
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 1);
lean_ctor_set(v___x_1223_, 1, v___x_1227_);
lean_ctor_set(v___x_1223_, 0, v_u_1218_);
v___x_1229_ = v___x_1223_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_u_1218_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v_inst_x27_1231_; lean_object* v___x_1232_; lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_instType_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_inc_ref_n(v___x_1229_, 2);
v___x_1230_ = l_Lean_mkConst(v___x_1226_, v___x_1229_);
lean_inc_ref_n(v_type_1217_, 2);
v_inst_x27_1231_ = l_Lean_mkAppB(v___x_1230_, v_type_1217_, v_ringInst_1219_);
v___x_1232_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_1210_, 2);
v___f_1233_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1233_, 0, v___x_1232_);
lean_closure_set(v___f_1233_, 1, v___x_1225_);
lean_closure_set(v___f_1233_, 2, v___x_1229_);
lean_closure_set(v___f_1233_, 3, v_type_1217_);
lean_closure_set(v___f_1233_, 4, v_canonExpr_1220_);
lean_closure_set(v___f_1233_, 5, v_toBind_1210_);
lean_closure_set(v___f_1233_, 6, v___f_1211_);
v___f_1234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1234_, 0, v___f_1233_);
lean_inc_ref(v___f_1234_);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_1235_, 0, v_toPure_1208_);
lean_closure_set(v___f_1235_, 1, v_inst_x27_1231_);
lean_closure_set(v___f_1235_, 2, v_toBind_1210_);
lean_closure_set(v___f_1235_, 3, v___f_1234_);
lean_closure_set(v___f_1235_, 4, v___f_1234_);
lean_closure_set(v___f_1235_, 5, v_inst_1212_);
v___x_1236_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_1237_ = l_Lean_mkConst(v___x_1236_, v___x_1229_);
v_instType_1238_ = l_Lean_Expr_app___override(v___x_1237_, v_type_1217_);
v___x_1239_ = lean_apply_1(v_synthInstance_x3f_1221_, v_instType_1238_);
v___x_1240_ = lean_apply_4(v_toBind_1210_, lean_box(0), lean_box(0), v___x_1239_, v___f_1235_);
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_){
_start:
{
lean_object* v_toApplicative_1247_; lean_object* v_toBind_1248_; lean_object* v_getRing_1249_; lean_object* v_modifyRing_1250_; lean_object* v_toPure_1251_; lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; 
v_toApplicative_1247_ = lean_ctor_get(v_inst_1244_, 0);
lean_inc_ref(v_toApplicative_1247_);
v_toBind_1248_ = lean_ctor_get(v_inst_1244_, 1);
lean_inc_n(v_toBind_1248_, 3);
lean_dec_ref(v_inst_1244_);
v_getRing_1249_ = lean_ctor_get(v_inst_1246_, 0);
lean_inc(v_getRing_1249_);
v_modifyRing_1250_ = lean_ctor_get(v_inst_1246_, 1);
lean_inc(v_modifyRing_1250_);
lean_dec_ref(v_inst_1246_);
v_toPure_1251_ = lean_ctor_get(v_toApplicative_1247_, 1);
lean_inc_n(v_toPure_1251_, 2);
lean_dec_ref(v_toApplicative_1247_);
v___f_1252_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1252_, 0, v_toPure_1251_);
lean_closure_set(v___f_1252_, 1, v_modifyRing_1250_);
lean_closure_set(v___f_1252_, 2, v_toBind_1248_);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_1253_, 0, v_toPure_1251_);
lean_closure_set(v___f_1253_, 1, v_inst_1245_);
lean_closure_set(v___f_1253_, 2, v_toBind_1248_);
lean_closure_set(v___f_1253_, 3, v___f_1252_);
lean_closure_set(v___f_1253_, 4, v_inst_1243_);
v___x_1254_ = lean_apply_4(v_toBind_1248_, lean_box(0), lean_box(0), v_getRing_1249_, v___f_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_1261_, lean_object* v_s_1262_){
_start:
{
lean_object* v_id_1263_; lean_object* v_type_1264_; lean_object* v_u_1265_; lean_object* v_ringInst_1266_; lean_object* v_semiringInst_1267_; lean_object* v_charInst_x3f_1268_; lean_object* v_addFn_x3f_1269_; lean_object* v_mulFn_x3f_1270_; lean_object* v_subFn_x3f_1271_; lean_object* v_negFn_x3f_1272_; lean_object* v_powFn_x3f_1273_; lean_object* v_intCastFn_x3f_1274_; lean_object* v_natSMulFn_x3f_1275_; lean_object* v_intSMulFn_x3f_1276_; lean_object* v_one_x3f_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
v_id_1263_ = lean_ctor_get(v_s_1262_, 0);
v_type_1264_ = lean_ctor_get(v_s_1262_, 1);
v_u_1265_ = lean_ctor_get(v_s_1262_, 2);
v_ringInst_1266_ = lean_ctor_get(v_s_1262_, 3);
v_semiringInst_1267_ = lean_ctor_get(v_s_1262_, 4);
v_charInst_x3f_1268_ = lean_ctor_get(v_s_1262_, 5);
v_addFn_x3f_1269_ = lean_ctor_get(v_s_1262_, 6);
v_mulFn_x3f_1270_ = lean_ctor_get(v_s_1262_, 7);
v_subFn_x3f_1271_ = lean_ctor_get(v_s_1262_, 8);
v_negFn_x3f_1272_ = lean_ctor_get(v_s_1262_, 9);
v_powFn_x3f_1273_ = lean_ctor_get(v_s_1262_, 10);
v_intCastFn_x3f_1274_ = lean_ctor_get(v_s_1262_, 11);
v_natSMulFn_x3f_1275_ = lean_ctor_get(v_s_1262_, 13);
v_intSMulFn_x3f_1276_ = lean_ctor_get(v_s_1262_, 14);
v_one_x3f_1277_ = lean_ctor_get(v_s_1262_, 15);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_s_1262_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v_s_1262_, 12);
lean_dec(v_unused_1286_);
v___x_1279_ = v_s_1262_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_one_x3f_1277_);
lean_inc(v_intSMulFn_x3f_1276_);
lean_inc(v_natSMulFn_x3f_1275_);
lean_inc(v_intCastFn_x3f_1274_);
lean_inc(v_powFn_x3f_1273_);
lean_inc(v_negFn_x3f_1272_);
lean_inc(v_subFn_x3f_1271_);
lean_inc(v_mulFn_x3f_1270_);
lean_inc(v_addFn_x3f_1269_);
lean_inc(v_charInst_x3f_1268_);
lean_inc(v_semiringInst_1267_);
lean_inc(v_ringInst_1266_);
lean_inc(v_u_1265_);
lean_inc(v_type_1264_);
lean_inc(v_id_1263_);
lean_dec(v_s_1262_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_natCastFn_1261_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 12, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_id_1263_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_type_1264_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_u_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_ringInst_1266_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_semiringInst_1267_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_charInst_x3f_1268_);
lean_ctor_set(v_reuseFailAlloc_1284_, 6, v_addFn_x3f_1269_);
lean_ctor_set(v_reuseFailAlloc_1284_, 7, v_mulFn_x3f_1270_);
lean_ctor_set(v_reuseFailAlloc_1284_, 8, v_subFn_x3f_1271_);
lean_ctor_set(v_reuseFailAlloc_1284_, 9, v_negFn_x3f_1272_);
lean_ctor_set(v_reuseFailAlloc_1284_, 10, v_powFn_x3f_1273_);
lean_ctor_set(v_reuseFailAlloc_1284_, 11, v_intCastFn_x3f_1274_);
lean_ctor_set(v_reuseFailAlloc_1284_, 12, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1284_, 13, v_natSMulFn_x3f_1275_);
lean_ctor_set(v_reuseFailAlloc_1284_, 14, v_intSMulFn_x3f_1276_);
lean_ctor_set(v_reuseFailAlloc_1284_, 15, v_one_x3f_1277_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1287_, lean_object* v_natCastFn_1288_, lean_object* v_____r_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_apply_2(v_toPure_1287_, lean_box(0), v_natCastFn_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1291_, lean_object* v_modifyRing_1292_, lean_object* v_toBind_1293_, lean_object* v_natCastFn_1294_){
_start:
{
lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_inc_ref(v_natCastFn_1294_);
v___f_1295_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1295_, 0, v_natCastFn_1294_);
v___f_1296_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1296_, 0, v_toPure_1291_);
lean_closure_set(v___f_1296_, 1, v_natCastFn_1294_);
v___x_1297_ = lean_apply_1(v_modifyRing_1292_, v___f_1295_);
v___x_1298_ = lean_apply_4(v_toBind_1293_, lean_box(0), lean_box(0), v___x_1297_, v___f_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_toBind_1303_, lean_object* v___f_1304_, lean_object* v_ring_1305_){
_start:
{
lean_object* v_natCastFn_x3f_1306_; 
v_natCastFn_x3f_1306_ = lean_ctor_get(v_ring_1305_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1306_) == 1)
{
lean_object* v_val_1307_; lean_object* v___x_1308_; 
lean_inc_ref(v_natCastFn_x3f_1306_);
lean_dec_ref(v_ring_1305_);
lean_dec(v___f_1304_);
lean_dec(v_toBind_1303_);
lean_dec_ref(v_inst_1302_);
lean_dec_ref(v_inst_1301_);
lean_dec(v_inst_1300_);
v_val_1307_ = lean_ctor_get(v_natCastFn_x3f_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v_natCastFn_x3f_1306_, 1);
v___x_1308_ = lean_apply_2(v_toPure_1299_, lean_box(0), v_val_1307_);
return v___x_1308_;
}
else
{
lean_object* v_type_1309_; lean_object* v_u_1310_; lean_object* v_semiringInst_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec(v_toPure_1299_);
v_type_1309_ = lean_ctor_get(v_ring_1305_, 1);
lean_inc_ref(v_type_1309_);
v_u_1310_ = lean_ctor_get(v_ring_1305_, 2);
lean_inc(v_u_1310_);
v_semiringInst_1311_ = lean_ctor_get(v_ring_1305_, 4);
lean_inc_ref(v_semiringInst_1311_);
lean_dec_ref(v_ring_1305_);
v___x_1312_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1300_, v_inst_1301_, v_inst_1302_, v_u_1310_, v_type_1309_, v_semiringInst_1311_);
v___x_1313_ = lean_apply_4(v_toBind_1303_, lean_box(0), lean_box(0), v___x_1312_, v___f_1304_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_){
_start:
{
lean_object* v_toApplicative_1318_; lean_object* v_toBind_1319_; lean_object* v_getRing_1320_; lean_object* v_modifyRing_1321_; lean_object* v_toPure_1322_; lean_object* v___f_1323_; lean_object* v___f_1324_; lean_object* v___x_1325_; 
v_toApplicative_1318_ = lean_ctor_get(v_inst_1315_, 0);
v_toBind_1319_ = lean_ctor_get(v_inst_1315_, 1);
lean_inc_n(v_toBind_1319_, 3);
v_getRing_1320_ = lean_ctor_get(v_inst_1317_, 0);
lean_inc(v_getRing_1320_);
v_modifyRing_1321_ = lean_ctor_get(v_inst_1317_, 1);
lean_inc(v_modifyRing_1321_);
lean_dec_ref(v_inst_1317_);
v_toPure_1322_ = lean_ctor_get(v_toApplicative_1318_, 1);
lean_inc_n(v_toPure_1322_, 2);
v___f_1323_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1323_, 0, v_toPure_1322_);
lean_closure_set(v___f_1323_, 1, v_modifyRing_1321_);
lean_closure_set(v___f_1323_, 2, v_toBind_1319_);
v___f_1324_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1324_, 0, v_toPure_1322_);
lean_closure_set(v___f_1324_, 1, v_inst_1314_);
lean_closure_set(v___f_1324_, 2, v_inst_1315_);
lean_closure_set(v___f_1324_, 3, v_inst_1316_);
lean_closure_set(v___f_1324_, 4, v_toBind_1319_);
lean_closure_set(v___f_1324_, 5, v___f_1323_);
v___x_1325_ = lean_apply_4(v_toBind_1319_, lean_box(0), lean_box(0), v_getRing_1320_, v___f_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1332_, lean_object* v_s_1333_){
_start:
{
lean_object* v_toRing_1334_; lean_object* v_divFn_x3f_1335_; lean_object* v_semiringId_x3f_1336_; lean_object* v_commSemiringInst_1337_; lean_object* v_commRingInst_1338_; lean_object* v_noZeroDivInst_x3f_1339_; lean_object* v_fieldInst_x3f_1340_; lean_object* v_powIdentityInst_x3f_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1349_; 
v_toRing_1334_ = lean_ctor_get(v_s_1333_, 0);
v_divFn_x3f_1335_ = lean_ctor_get(v_s_1333_, 2);
v_semiringId_x3f_1336_ = lean_ctor_get(v_s_1333_, 3);
v_commSemiringInst_1337_ = lean_ctor_get(v_s_1333_, 4);
v_commRingInst_1338_ = lean_ctor_get(v_s_1333_, 5);
v_noZeroDivInst_x3f_1339_ = lean_ctor_get(v_s_1333_, 6);
v_fieldInst_x3f_1340_ = lean_ctor_get(v_s_1333_, 7);
v_powIdentityInst_x3f_1341_ = lean_ctor_get(v_s_1333_, 8);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_s_1333_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v_s_1333_, 1);
lean_dec(v_unused_1350_);
v___x_1343_ = v_s_1333_;
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1341_);
lean_inc(v_fieldInst_x3f_1340_);
lean_inc(v_noZeroDivInst_x3f_1339_);
lean_inc(v_commRingInst_1338_);
lean_inc(v_commSemiringInst_1337_);
lean_inc(v_semiringId_x3f_1336_);
lean_inc(v_divFn_x3f_1335_);
lean_inc(v_toRing_1334_);
lean_dec(v_s_1333_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_invFn_1332_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v___x_1345_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_toRing_1334_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_divFn_x3f_1335_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v_semiringId_x3f_1336_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v_commSemiringInst_1337_);
lean_ctor_set(v_reuseFailAlloc_1348_, 5, v_commRingInst_1338_);
lean_ctor_set(v_reuseFailAlloc_1348_, 6, v_noZeroDivInst_x3f_1339_);
lean_ctor_set(v_reuseFailAlloc_1348_, 7, v_fieldInst_x3f_1340_);
lean_ctor_set(v_reuseFailAlloc_1348_, 8, v_powIdentityInst_x3f_1341_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1351_, lean_object* v_invFn_1352_, lean_object* v_____r_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_apply_2(v_toPure_1351_, lean_box(0), v_invFn_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1355_, lean_object* v_modifyCommRing_1356_, lean_object* v_toBind_1357_, lean_object* v_invFn_1358_){
_start:
{
lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_inc_ref(v_invFn_1358_);
v___f_1359_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1359_, 0, v_invFn_1358_);
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1360_, 0, v_toPure_1355_);
lean_closure_set(v___f_1360_, 1, v_invFn_1358_);
v___x_1361_ = lean_apply_1(v_modifyCommRing_1356_, v___f_1359_);
v___x_1362_ = lean_apply_4(v_toBind_1357_, lean_box(0), lean_box(0), v___x_1361_, v___f_1360_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v_toBind_1385_, lean_object* v___f_1386_, lean_object* v_ring_1387_){
_start:
{
lean_object* v_fieldInst_x3f_1388_; 
v_fieldInst_x3f_1388_ = lean_ctor_get(v_ring_1387_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1388_) == 1)
{
lean_object* v_invFn_x3f_1389_; 
lean_inc_ref(v_fieldInst_x3f_1388_);
v_invFn_x3f_1389_ = lean_ctor_get(v_ring_1387_, 1);
if (lean_obj_tag(v_invFn_x3f_1389_) == 1)
{
lean_object* v_val_1390_; lean_object* v___x_1391_; 
lean_inc_ref(v_invFn_x3f_1389_);
lean_dec_ref_known(v_fieldInst_x3f_1388_, 1);
lean_dec_ref(v_ring_1387_);
lean_dec(v___f_1386_);
lean_dec(v_toBind_1385_);
lean_dec_ref(v_inst_1384_);
lean_dec_ref(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
lean_dec(v_inst_1381_);
v_val_1390_ = lean_ctor_get(v_invFn_x3f_1389_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v_invFn_x3f_1389_, 1);
v___x_1391_ = lean_apply_2(v_toPure_1380_, lean_box(0), v_val_1390_);
return v___x_1391_;
}
else
{
lean_object* v_toRing_1392_; lean_object* v_val_1393_; lean_object* v_type_1394_; lean_object* v_u_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_expectedInst_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_toPure_1380_);
v_toRing_1392_ = lean_ctor_get(v_ring_1387_, 0);
lean_inc_ref(v_toRing_1392_);
lean_dec_ref(v_ring_1387_);
v_val_1393_ = lean_ctor_get(v_fieldInst_x3f_1388_, 0);
lean_inc(v_val_1393_);
lean_dec_ref_known(v_fieldInst_x3f_1388_, 1);
v_type_1394_ = lean_ctor_get(v_toRing_1392_, 1);
lean_inc_ref_n(v_type_1394_, 2);
v_u_1395_ = lean_ctor_get(v_toRing_1392_, 2);
lean_inc_n(v_u_1395_, 2);
lean_dec_ref(v_toRing_1392_);
v___x_1396_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_u_1395_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = l_Lean_mkConst(v___x_1396_, v___x_1398_);
v_expectedInst_1400_ = l_Lean_mkAppB(v___x_1399_, v_type_1394_, v_val_1393_);
v___x_1401_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1402_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1403_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1381_, v_inst_1382_, v_inst_1383_, v_inst_1384_, v_type_1394_, v_u_1395_, v___x_1401_, v___x_1402_, v_expectedInst_1400_);
v___x_1404_ = lean_apply_4(v_toBind_1385_, lean_box(0), lean_box(0), v___x_1403_, v___f_1386_);
return v___x_1404_;
}
}
else
{
lean_object* v_toRing_1405_; lean_object* v_type_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_dec(v___f_1386_);
lean_dec(v_toBind_1385_);
lean_dec_ref(v_inst_1384_);
lean_dec(v_inst_1381_);
lean_dec(v_toPure_1380_);
v_toRing_1405_ = lean_ctor_get(v_ring_1387_, 0);
lean_inc_ref(v_toRing_1405_);
lean_dec_ref(v_ring_1387_);
v_type_1406_ = lean_ctor_get(v_toRing_1405_, 1);
lean_inc_ref(v_type_1406_);
lean_dec_ref(v_toRing_1405_);
v___x_1407_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1408_ = l_Lean_indentExpr(v_type_1406_);
v___x_1409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Lean_throwError___redArg(v_inst_1383_, v_inst_1382_, v___x_1409_);
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_){
_start:
{
lean_object* v_toApplicative_1416_; lean_object* v_toBind_1417_; lean_object* v_getCommRing_1418_; lean_object* v_modifyCommRing_1419_; lean_object* v_toPure_1420_; lean_object* v___f_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; 
v_toApplicative_1416_ = lean_ctor_get(v_inst_1413_, 0);
v_toBind_1417_ = lean_ctor_get(v_inst_1413_, 1);
lean_inc_n(v_toBind_1417_, 3);
v_getCommRing_1418_ = lean_ctor_get(v_inst_1415_, 0);
lean_inc(v_getCommRing_1418_);
v_modifyCommRing_1419_ = lean_ctor_get(v_inst_1415_, 1);
lean_inc(v_modifyCommRing_1419_);
lean_dec_ref(v_inst_1415_);
v_toPure_1420_ = lean_ctor_get(v_toApplicative_1416_, 1);
lean_inc_n(v_toPure_1420_, 2);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1421_, 0, v_toPure_1420_);
lean_closure_set(v___f_1421_, 1, v_modifyCommRing_1419_);
lean_closure_set(v___f_1421_, 2, v_toBind_1417_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1422_, 0, v_toPure_1420_);
lean_closure_set(v___f_1422_, 1, v_inst_1411_);
lean_closure_set(v___f_1422_, 2, v_inst_1412_);
lean_closure_set(v___f_1422_, 3, v_inst_1413_);
lean_closure_set(v___f_1422_, 4, v_inst_1414_);
lean_closure_set(v___f_1422_, 5, v_toBind_1417_);
lean_closure_set(v___f_1422_, 6, v___f_1421_);
v___x_1423_ = lean_apply_4(v_toBind_1417_, lean_box(0), lean_box(0), v_getCommRing_1418_, v___f_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1425_, v_inst_1426_, v_inst_1427_, v_inst_1428_, v_inst_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0(lean_object* v_divFn_1431_, lean_object* v_s_1432_){
_start:
{
lean_object* v_toRing_1433_; lean_object* v_invFn_x3f_1434_; lean_object* v_semiringId_x3f_1435_; lean_object* v_commSemiringInst_1436_; lean_object* v_commRingInst_1437_; lean_object* v_noZeroDivInst_x3f_1438_; lean_object* v_fieldInst_x3f_1439_; lean_object* v_powIdentityInst_x3f_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_toRing_1433_ = lean_ctor_get(v_s_1432_, 0);
v_invFn_x3f_1434_ = lean_ctor_get(v_s_1432_, 1);
v_semiringId_x3f_1435_ = lean_ctor_get(v_s_1432_, 3);
v_commSemiringInst_1436_ = lean_ctor_get(v_s_1432_, 4);
v_commRingInst_1437_ = lean_ctor_get(v_s_1432_, 5);
v_noZeroDivInst_x3f_1438_ = lean_ctor_get(v_s_1432_, 6);
v_fieldInst_x3f_1439_ = lean_ctor_get(v_s_1432_, 7);
v_powIdentityInst_x3f_1440_ = lean_ctor_get(v_s_1432_, 8);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_s_1432_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v_s_1432_, 2);
lean_dec(v_unused_1449_);
v___x_1442_ = v_s_1432_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1440_);
lean_inc(v_fieldInst_x3f_1439_);
lean_inc(v_noZeroDivInst_x3f_1438_);
lean_inc(v_commRingInst_1437_);
lean_inc(v_commSemiringInst_1436_);
lean_inc(v_semiringId_x3f_1435_);
lean_inc(v_invFn_x3f_1434_);
lean_inc(v_toRing_1433_);
lean_dec(v_s_1432_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_divFn_1431_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 2, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_toRing_1433_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_invFn_x3f_1434_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_semiringId_x3f_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_commSemiringInst_1436_);
lean_ctor_set(v_reuseFailAlloc_1447_, 5, v_commRingInst_1437_);
lean_ctor_set(v_reuseFailAlloc_1447_, 6, v_noZeroDivInst_x3f_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 7, v_fieldInst_x3f_1439_);
lean_ctor_set(v_reuseFailAlloc_1447_, 8, v_powIdentityInst_x3f_1440_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1(lean_object* v_toPure_1450_, lean_object* v_divFn_1451_, lean_object* v_____r_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_apply_2(v_toPure_1450_, lean_box(0), v_divFn_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2(lean_object* v_toPure_1454_, lean_object* v_modifyCommRing_1455_, lean_object* v_toBind_1456_, lean_object* v_divFn_1457_){
_start:
{
lean_object* v___f_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc_ref(v_divFn_1457_);
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1458_, 0, v_divFn_1457_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1459_, 0, v_toPure_1454_);
lean_closure_set(v___f_1459_, 1, v_divFn_1457_);
v___x_1460_ = lean_apply_1(v_modifyCommRing_1455_, v___f_1458_);
v___x_1461_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1460_, v___f_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3(lean_object* v_toPure_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_toBind_1483_, lean_object* v___f_1484_, lean_object* v_ring_1485_){
_start:
{
lean_object* v_fieldInst_x3f_1486_; 
v_fieldInst_x3f_1486_ = lean_ctor_get(v_ring_1485_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1486_) == 1)
{
lean_object* v_divFn_x3f_1487_; 
lean_inc_ref(v_fieldInst_x3f_1486_);
v_divFn_x3f_1487_ = lean_ctor_get(v_ring_1485_, 2);
if (lean_obj_tag(v_divFn_x3f_1487_) == 1)
{
lean_object* v_val_1488_; lean_object* v___x_1489_; 
lean_inc_ref(v_divFn_x3f_1487_);
lean_dec_ref_known(v_fieldInst_x3f_1486_, 1);
lean_dec_ref(v_ring_1485_);
lean_dec(v___f_1484_);
lean_dec(v_toBind_1483_);
lean_dec_ref(v_inst_1482_);
lean_dec_ref(v_inst_1481_);
lean_dec_ref(v_inst_1480_);
lean_dec(v_inst_1479_);
v_val_1488_ = lean_ctor_get(v_divFn_x3f_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v_divFn_x3f_1487_, 1);
v___x_1489_ = lean_apply_2(v_toPure_1478_, lean_box(0), v_val_1488_);
return v___x_1489_;
}
else
{
lean_object* v_toRing_1490_; lean_object* v_val_1491_; lean_object* v_type_1492_; lean_object* v_u_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v_expectedInst_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v_toPure_1478_);
v_toRing_1490_ = lean_ctor_get(v_ring_1485_, 0);
lean_inc_ref(v_toRing_1490_);
lean_dec_ref(v_ring_1485_);
v_val_1491_ = lean_ctor_get(v_fieldInst_x3f_1486_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v_fieldInst_x3f_1486_, 1);
v_type_1492_ = lean_ctor_get(v_toRing_1490_, 1);
lean_inc_ref_n(v_type_1492_, 3);
v_u_1493_ = lean_ctor_get(v_toRing_1490_, 2);
lean_inc_n(v_u_1493_, 2);
lean_dec_ref(v_toRing_1490_);
v___x_1494_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1));
v___x_1495_ = lean_box(0);
v___x_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_u_1493_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
lean_inc_ref(v___x_1496_);
v___x_1497_ = l_Lean_mkConst(v___x_1494_, v___x_1496_);
v___x_1498_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3));
v___x_1499_ = l_Lean_mkConst(v___x_1498_, v___x_1496_);
v___x_1500_ = l_Lean_mkAppB(v___x_1499_, v_type_1492_, v_val_1491_);
v_expectedInst_1501_ = l_Lean_mkAppB(v___x_1497_, v_type_1492_, v___x_1500_);
v___x_1502_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5));
v___x_1503_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7));
v___x_1504_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1479_, v_inst_1480_, v_inst_1481_, v_inst_1482_, v_type_1492_, v_u_1493_, v___x_1502_, v___x_1503_, v_expectedInst_1501_);
v___x_1505_ = lean_apply_4(v_toBind_1483_, lean_box(0), lean_box(0), v___x_1504_, v___f_1484_);
return v___x_1505_;
}
}
else
{
lean_object* v_toRing_1506_; lean_object* v_type_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec(v___f_1484_);
lean_dec(v_toBind_1483_);
lean_dec_ref(v_inst_1482_);
lean_dec(v_inst_1479_);
lean_dec(v_toPure_1478_);
v_toRing_1506_ = lean_ctor_get(v_ring_1485_, 0);
lean_inc_ref(v_toRing_1506_);
lean_dec_ref(v_ring_1485_);
v_type_1507_ = lean_ctor_get(v_toRing_1506_, 1);
lean_inc_ref(v_type_1507_);
lean_dec_ref(v_toRing_1506_);
v___x_1508_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1509_ = l_Lean_indentExpr(v_type_1507_);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = l_Lean_throwError___redArg(v_inst_1481_, v_inst_1480_, v___x_1510_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg(lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_inst_1516_){
_start:
{
lean_object* v_toApplicative_1517_; lean_object* v_toBind_1518_; lean_object* v_getCommRing_1519_; lean_object* v_modifyCommRing_1520_; lean_object* v_toPure_1521_; lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; 
v_toApplicative_1517_ = lean_ctor_get(v_inst_1514_, 0);
v_toBind_1518_ = lean_ctor_get(v_inst_1514_, 1);
lean_inc_n(v_toBind_1518_, 3);
v_getCommRing_1519_ = lean_ctor_get(v_inst_1516_, 0);
lean_inc(v_getCommRing_1519_);
v_modifyCommRing_1520_ = lean_ctor_get(v_inst_1516_, 1);
lean_inc(v_modifyCommRing_1520_);
lean_dec_ref(v_inst_1516_);
v_toPure_1521_ = lean_ctor_get(v_toApplicative_1517_, 1);
lean_inc_n(v_toPure_1521_, 2);
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1522_, 0, v_toPure_1521_);
lean_closure_set(v___f_1522_, 1, v_modifyCommRing_1520_);
lean_closure_set(v___f_1522_, 2, v_toBind_1518_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1523_, 0, v_toPure_1521_);
lean_closure_set(v___f_1523_, 1, v_inst_1512_);
lean_closure_set(v___f_1523_, 2, v_inst_1513_);
lean_closure_set(v___f_1523_, 3, v_inst_1514_);
lean_closure_set(v___f_1523_, 4, v_inst_1515_);
lean_closure_set(v___f_1523_, 5, v_toBind_1518_);
lean_closure_set(v___f_1523_, 6, v___f_1522_);
v___x_1524_ = lean_apply_4(v_toBind_1518_, lean_box(0), lean_box(0), v_getCommRing_1519_, v___f_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn(lean_object* v_m_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_inst_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_Meta_Sym_Arith_getDivFn___redArg(v_inst_1526_, v_inst_1527_, v_inst_1528_, v_inst_1529_, v_inst_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0(lean_object* v_fn_1532_, lean_object* v_s_1533_){
_start:
{
lean_object* v_id_1534_; lean_object* v_type_1535_; lean_object* v_u_1536_; lean_object* v_semiringInst_1537_; lean_object* v_addFn_x3f_1538_; lean_object* v_mulFn_x3f_1539_; lean_object* v_powFn_x3f_1540_; lean_object* v_natCastFn_x3f_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1549_; 
v_id_1534_ = lean_ctor_get(v_s_1533_, 0);
v_type_1535_ = lean_ctor_get(v_s_1533_, 1);
v_u_1536_ = lean_ctor_get(v_s_1533_, 2);
v_semiringInst_1537_ = lean_ctor_get(v_s_1533_, 3);
v_addFn_x3f_1538_ = lean_ctor_get(v_s_1533_, 4);
v_mulFn_x3f_1539_ = lean_ctor_get(v_s_1533_, 5);
v_powFn_x3f_1540_ = lean_ctor_get(v_s_1533_, 6);
v_natCastFn_x3f_1541_ = lean_ctor_get(v_s_1533_, 7);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_s_1533_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v_s_1533_, 8);
lean_dec(v_unused_1550_);
v___x_1543_ = v_s_1533_;
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_natCastFn_x3f_1541_);
lean_inc(v_powFn_x3f_1540_);
lean_inc(v_mulFn_x3f_1539_);
lean_inc(v_addFn_x3f_1538_);
lean_inc(v_semiringInst_1537_);
lean_inc(v_u_1536_);
lean_inc(v_type_1535_);
lean_inc(v_id_1534_);
lean_dec(v_s_1533_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_fn_1532_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 8, v___x_1545_);
v___x_1547_ = v___x_1543_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_id_1534_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_type_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_u_1536_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_semiringInst_1537_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_addFn_x3f_1538_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v_mulFn_x3f_1539_);
lean_ctor_set(v_reuseFailAlloc_1548_, 6, v_powFn_x3f_1540_);
lean_ctor_set(v_reuseFailAlloc_1548_, 7, v_natCastFn_x3f_1541_);
lean_ctor_set(v_reuseFailAlloc_1548_, 8, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2(lean_object* v_toPure_1551_, lean_object* v_modifySemiring_1552_, lean_object* v_toBind_1553_, lean_object* v_fn_1554_){
_start:
{
lean_object* v___f_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_inc_ref(v_fn_1554_);
v___f_1555_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1555_, 0, v_fn_1554_);
v___f_1556_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1556_, 0, v_toPure_1551_);
lean_closure_set(v___f_1556_, 1, v_fn_1554_);
v___x_1557_ = lean_apply_1(v_modifySemiring_1552_, v___f_1555_);
v___x_1558_ = lean_apply_4(v_toBind_1553_, lean_box(0), lean_box(0), v___x_1557_, v___f_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1(lean_object* v_toPure_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_toBind_1563_, lean_object* v___f_1564_, lean_object* v_sr_1565_){
_start:
{
lean_object* v_natSMulFn_x3f_1566_; 
v_natSMulFn_x3f_1566_ = lean_ctor_get(v_sr_1565_, 8);
if (lean_obj_tag(v_natSMulFn_x3f_1566_) == 1)
{
lean_object* v_val_1567_; lean_object* v___x_1568_; 
lean_inc_ref(v_natSMulFn_x3f_1566_);
lean_dec_ref(v_sr_1565_);
lean_dec(v___f_1564_);
lean_dec(v_toBind_1563_);
lean_dec_ref(v_inst_1562_);
lean_dec_ref(v_inst_1561_);
lean_dec(v_inst_1560_);
v_val_1567_ = lean_ctor_get(v_natSMulFn_x3f_1566_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v_natSMulFn_x3f_1566_, 1);
v___x_1568_ = lean_apply_2(v_toPure_1559_, lean_box(0), v_val_1567_);
return v___x_1568_;
}
else
{
lean_object* v_type_1569_; lean_object* v_u_1570_; lean_object* v_semiringInst_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v_toPure_1559_);
v_type_1569_ = lean_ctor_get(v_sr_1565_, 1);
lean_inc_ref_n(v_type_1569_, 2);
v_u_1570_ = lean_ctor_get(v_sr_1565_, 2);
lean_inc_n(v_u_1570_, 2);
v_semiringInst_1571_ = lean_ctor_get(v_sr_1565_, 3);
lean_inc_ref(v_semiringInst_1571_);
lean_dec_ref(v_sr_1565_);
v___x_1572_ = l_Lean_Nat_mkType;
v___x_1573_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1575_, 0, v_u_1570_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = l_Lean_mkConst(v___x_1573_, v___x_1575_);
v___x_1577_ = l_Lean_mkAppB(v___x_1576_, v_type_1569_, v_semiringInst_1571_);
v___x_1578_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_1560_, v_inst_1561_, v_inst_1562_, v_u_1570_, v_type_1569_, v___x_1572_, v___x_1577_);
v___x_1579_ = lean_apply_4(v_toBind_1563_, lean_box(0), lean_box(0), v___x_1578_, v___f_1564_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_){
_start:
{
lean_object* v_toApplicative_1584_; lean_object* v_toBind_1585_; lean_object* v_getSemiring_1586_; lean_object* v_modifySemiring_1587_; lean_object* v_toPure_1588_; lean_object* v___f_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; 
v_toApplicative_1584_ = lean_ctor_get(v_inst_1581_, 0);
v_toBind_1585_ = lean_ctor_get(v_inst_1581_, 1);
lean_inc_n(v_toBind_1585_, 3);
v_getSemiring_1586_ = lean_ctor_get(v_inst_1583_, 0);
lean_inc(v_getSemiring_1586_);
v_modifySemiring_1587_ = lean_ctor_get(v_inst_1583_, 1);
lean_inc(v_modifySemiring_1587_);
lean_dec_ref(v_inst_1583_);
v_toPure_1588_ = lean_ctor_get(v_toApplicative_1584_, 1);
lean_inc_n(v_toPure_1588_, 2);
v___f_1589_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1589_, 0, v_toPure_1588_);
lean_closure_set(v___f_1589_, 1, v_modifySemiring_1587_);
lean_closure_set(v___f_1589_, 2, v_toBind_1585_);
v___f_1590_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1590_, 0, v_toPure_1588_);
lean_closure_set(v___f_1590_, 1, v_inst_1580_);
lean_closure_set(v___f_1590_, 2, v_inst_1581_);
lean_closure_set(v___f_1590_, 3, v_inst_1582_);
lean_closure_set(v___f_1590_, 4, v_toBind_1585_);
lean_closure_set(v___f_1590_, 5, v___f_1589_);
v___x_1591_ = lean_apply_4(v_toBind_1585_, lean_box(0), lean_box(0), v_getSemiring_1586_, v___f_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27(lean_object* v_m_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(v_inst_1593_, v_inst_1594_, v_inst_1595_, v_inst_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_1598_, lean_object* v_s_1599_){
_start:
{
lean_object* v_id_1600_; lean_object* v_type_1601_; lean_object* v_u_1602_; lean_object* v_semiringInst_1603_; lean_object* v_mulFn_x3f_1604_; lean_object* v_powFn_x3f_1605_; lean_object* v_natCastFn_x3f_1606_; lean_object* v_natSMulFn_x3f_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1615_; 
v_id_1600_ = lean_ctor_get(v_s_1599_, 0);
v_type_1601_ = lean_ctor_get(v_s_1599_, 1);
v_u_1602_ = lean_ctor_get(v_s_1599_, 2);
v_semiringInst_1603_ = lean_ctor_get(v_s_1599_, 3);
v_mulFn_x3f_1604_ = lean_ctor_get(v_s_1599_, 5);
v_powFn_x3f_1605_ = lean_ctor_get(v_s_1599_, 6);
v_natCastFn_x3f_1606_ = lean_ctor_get(v_s_1599_, 7);
v_natSMulFn_x3f_1607_ = lean_ctor_get(v_s_1599_, 8);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_s_1599_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v_s_1599_, 4);
lean_dec(v_unused_1616_);
v___x_1609_ = v_s_1599_;
v_isShared_1610_ = v_isSharedCheck_1615_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_natSMulFn_x3f_1607_);
lean_inc(v_natCastFn_x3f_1606_);
lean_inc(v_powFn_x3f_1605_);
lean_inc(v_mulFn_x3f_1604_);
lean_inc(v_semiringInst_1603_);
lean_inc(v_u_1602_);
lean_inc(v_type_1601_);
lean_inc(v_id_1600_);
lean_dec(v_s_1599_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1615_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_addFn_1598_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 4, v___x_1611_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_id_1600_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_type_1601_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_u_1602_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_semiringInst_1603_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1614_, 5, v_mulFn_x3f_1604_);
lean_ctor_set(v_reuseFailAlloc_1614_, 6, v_powFn_x3f_1605_);
lean_ctor_set(v_reuseFailAlloc_1614_, 7, v_natCastFn_x3f_1606_);
lean_ctor_set(v_reuseFailAlloc_1614_, 8, v_natSMulFn_x3f_1607_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_1617_, lean_object* v_modifySemiring_1618_, lean_object* v_toBind_1619_, lean_object* v_addFn_1620_){
_start:
{
lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_inc_ref(v_addFn_1620_);
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1621_, 0, v_addFn_1620_);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1622_, 0, v_toPure_1617_);
lean_closure_set(v___f_1622_, 1, v_addFn_1620_);
v___x_1623_ = lean_apply_1(v_modifySemiring_1618_, v___f_1621_);
v___x_1624_ = lean_apply_4(v_toBind_1619_, lean_box(0), lean_box(0), v___x_1623_, v___f_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_toBind_1630_, lean_object* v___f_1631_, lean_object* v_sr_1632_){
_start:
{
lean_object* v_addFn_x3f_1633_; 
v_addFn_x3f_1633_ = lean_ctor_get(v_sr_1632_, 4);
if (lean_obj_tag(v_addFn_x3f_1633_) == 1)
{
lean_object* v_val_1634_; lean_object* v___x_1635_; 
lean_inc_ref(v_addFn_x3f_1633_);
lean_dec_ref(v_sr_1632_);
lean_dec(v___f_1631_);
lean_dec(v_toBind_1630_);
lean_dec_ref(v_inst_1629_);
lean_dec_ref(v_inst_1628_);
lean_dec_ref(v_inst_1627_);
lean_dec(v_inst_1626_);
v_val_1634_ = lean_ctor_get(v_addFn_x3f_1633_, 0);
lean_inc(v_val_1634_);
lean_dec_ref_known(v_addFn_x3f_1633_, 1);
v___x_1635_ = lean_apply_2(v_toPure_1625_, lean_box(0), v_val_1634_);
return v___x_1635_;
}
else
{
lean_object* v_type_1636_; lean_object* v_u_1637_; lean_object* v_semiringInst_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_expectedInst_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_toPure_1625_);
v_type_1636_ = lean_ctor_get(v_sr_1632_, 1);
lean_inc_ref_n(v_type_1636_, 3);
v_u_1637_ = lean_ctor_get(v_sr_1632_, 2);
lean_inc_n(v_u_1637_, 2);
v_semiringInst_1638_ = lean_ctor_get(v_sr_1632_, 3);
lean_inc_ref(v_semiringInst_1638_);
lean_dec_ref(v_sr_1632_);
v___x_1639_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1640_ = lean_box(0);
v___x_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_u_1637_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
lean_inc_ref(v___x_1641_);
v___x_1642_ = l_Lean_mkConst(v___x_1639_, v___x_1641_);
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1644_ = l_Lean_mkConst(v___x_1643_, v___x_1641_);
v___x_1645_ = l_Lean_mkAppB(v___x_1644_, v_type_1636_, v_semiringInst_1638_);
v_expectedInst_1646_ = l_Lean_mkAppB(v___x_1642_, v_type_1636_, v___x_1645_);
v___x_1647_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1648_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1649_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1626_, v_inst_1627_, v_inst_1628_, v_inst_1629_, v_type_1636_, v_u_1637_, v___x_1647_, v___x_1648_, v_expectedInst_1646_);
v___x_1650_ = lean_apply_4(v_toBind_1630_, lean_box(0), lean_box(0), v___x_1649_, v___f_1631_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_){
_start:
{
lean_object* v_toApplicative_1656_; lean_object* v_toBind_1657_; lean_object* v_getSemiring_1658_; lean_object* v_modifySemiring_1659_; lean_object* v_toPure_1660_; lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v___x_1663_; 
v_toApplicative_1656_ = lean_ctor_get(v_inst_1653_, 0);
v_toBind_1657_ = lean_ctor_get(v_inst_1653_, 1);
lean_inc_n(v_toBind_1657_, 3);
v_getSemiring_1658_ = lean_ctor_get(v_inst_1655_, 0);
lean_inc(v_getSemiring_1658_);
v_modifySemiring_1659_ = lean_ctor_get(v_inst_1655_, 1);
lean_inc(v_modifySemiring_1659_);
lean_dec_ref(v_inst_1655_);
v_toPure_1660_ = lean_ctor_get(v_toApplicative_1656_, 1);
lean_inc_n(v_toPure_1660_, 2);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1661_, 0, v_toPure_1660_);
lean_closure_set(v___f_1661_, 1, v_modifySemiring_1659_);
lean_closure_set(v___f_1661_, 2, v_toBind_1657_);
v___f_1662_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1662_, 0, v_toPure_1660_);
lean_closure_set(v___f_1662_, 1, v_inst_1651_);
lean_closure_set(v___f_1662_, 2, v_inst_1652_);
lean_closure_set(v___f_1662_, 3, v_inst_1653_);
lean_closure_set(v___f_1662_, 4, v_inst_1654_);
lean_closure_set(v___f_1662_, 5, v_toBind_1657_);
lean_closure_set(v___f_1662_, 6, v___f_1661_);
v___x_1663_ = lean_apply_4(v_toBind_1657_, lean_box(0), lean_box(0), v_getSemiring_1658_, v___f_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1665_, v_inst_1666_, v_inst_1667_, v_inst_1668_, v_inst_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_1671_, lean_object* v_s_1672_){
_start:
{
lean_object* v_id_1673_; lean_object* v_type_1674_; lean_object* v_u_1675_; lean_object* v_semiringInst_1676_; lean_object* v_addFn_x3f_1677_; lean_object* v_powFn_x3f_1678_; lean_object* v_natCastFn_x3f_1679_; lean_object* v_natSMulFn_x3f_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1688_; 
v_id_1673_ = lean_ctor_get(v_s_1672_, 0);
v_type_1674_ = lean_ctor_get(v_s_1672_, 1);
v_u_1675_ = lean_ctor_get(v_s_1672_, 2);
v_semiringInst_1676_ = lean_ctor_get(v_s_1672_, 3);
v_addFn_x3f_1677_ = lean_ctor_get(v_s_1672_, 4);
v_powFn_x3f_1678_ = lean_ctor_get(v_s_1672_, 6);
v_natCastFn_x3f_1679_ = lean_ctor_get(v_s_1672_, 7);
v_natSMulFn_x3f_1680_ = lean_ctor_get(v_s_1672_, 8);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_s_1672_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v_s_1672_, 5);
lean_dec(v_unused_1689_);
v___x_1682_ = v_s_1672_;
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_natSMulFn_x3f_1680_);
lean_inc(v_natCastFn_x3f_1679_);
lean_inc(v_powFn_x3f_1678_);
lean_inc(v_addFn_x3f_1677_);
lean_inc(v_semiringInst_1676_);
lean_inc(v_u_1675_);
lean_inc(v_type_1674_);
lean_inc(v_id_1673_);
lean_dec(v_s_1672_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_mulFn_1671_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 5, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_id_1673_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_type_1674_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_u_1675_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_semiringInst_1676_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_addFn_x3f_1677_);
lean_ctor_set(v_reuseFailAlloc_1687_, 5, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 6, v_powFn_x3f_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 7, v_natCastFn_x3f_1679_);
lean_ctor_set(v_reuseFailAlloc_1687_, 8, v_natSMulFn_x3f_1680_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1690_, lean_object* v_modifySemiring_1691_, lean_object* v_toBind_1692_, lean_object* v_mulFn_1693_){
_start:
{
lean_object* v___f_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_inc_ref(v_mulFn_1693_);
v___f_1694_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1694_, 0, v_mulFn_1693_);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1695_, 0, v_toPure_1690_);
lean_closure_set(v___f_1695_, 1, v_mulFn_1693_);
v___x_1696_ = lean_apply_1(v_modifySemiring_1691_, v___f_1694_);
v___x_1697_ = lean_apply_4(v_toBind_1692_, lean_box(0), lean_box(0), v___x_1696_, v___f_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_toBind_1703_, lean_object* v___f_1704_, lean_object* v_sr_1705_){
_start:
{
lean_object* v_mulFn_x3f_1706_; 
v_mulFn_x3f_1706_ = lean_ctor_get(v_sr_1705_, 5);
if (lean_obj_tag(v_mulFn_x3f_1706_) == 1)
{
lean_object* v_val_1707_; lean_object* v___x_1708_; 
lean_inc_ref(v_mulFn_x3f_1706_);
lean_dec_ref(v_sr_1705_);
lean_dec(v___f_1704_);
lean_dec(v_toBind_1703_);
lean_dec_ref(v_inst_1702_);
lean_dec_ref(v_inst_1701_);
lean_dec_ref(v_inst_1700_);
lean_dec(v_inst_1699_);
v_val_1707_ = lean_ctor_get(v_mulFn_x3f_1706_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v_mulFn_x3f_1706_, 1);
v___x_1708_ = lean_apply_2(v_toPure_1698_, lean_box(0), v_val_1707_);
return v___x_1708_;
}
else
{
lean_object* v_type_1709_; lean_object* v_u_1710_; lean_object* v_semiringInst_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_expectedInst_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_toPure_1698_);
v_type_1709_ = lean_ctor_get(v_sr_1705_, 1);
lean_inc_ref_n(v_type_1709_, 3);
v_u_1710_ = lean_ctor_get(v_sr_1705_, 2);
lean_inc_n(v_u_1710_, 2);
v_semiringInst_1711_ = lean_ctor_get(v_sr_1705_, 3);
lean_inc_ref(v_semiringInst_1711_);
lean_dec_ref(v_sr_1705_);
v___x_1712_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_u_1710_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
lean_inc_ref(v___x_1714_);
v___x_1715_ = l_Lean_mkConst(v___x_1712_, v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1717_ = l_Lean_mkConst(v___x_1716_, v___x_1714_);
v___x_1718_ = l_Lean_mkAppB(v___x_1717_, v_type_1709_, v_semiringInst_1711_);
v_expectedInst_1719_ = l_Lean_mkAppB(v___x_1715_, v_type_1709_, v___x_1718_);
v___x_1720_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1721_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1722_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1699_, v_inst_1700_, v_inst_1701_, v_inst_1702_, v_type_1709_, v_u_1710_, v___x_1720_, v___x_1721_, v_expectedInst_1719_);
v___x_1723_ = lean_apply_4(v_toBind_1703_, lean_box(0), lean_box(0), v___x_1722_, v___f_1704_);
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_){
_start:
{
lean_object* v_toApplicative_1729_; lean_object* v_toBind_1730_; lean_object* v_getSemiring_1731_; lean_object* v_modifySemiring_1732_; lean_object* v_toPure_1733_; lean_object* v___f_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; 
v_toApplicative_1729_ = lean_ctor_get(v_inst_1726_, 0);
v_toBind_1730_ = lean_ctor_get(v_inst_1726_, 1);
lean_inc_n(v_toBind_1730_, 3);
v_getSemiring_1731_ = lean_ctor_get(v_inst_1728_, 0);
lean_inc(v_getSemiring_1731_);
v_modifySemiring_1732_ = lean_ctor_get(v_inst_1728_, 1);
lean_inc(v_modifySemiring_1732_);
lean_dec_ref(v_inst_1728_);
v_toPure_1733_ = lean_ctor_get(v_toApplicative_1729_, 1);
lean_inc_n(v_toPure_1733_, 2);
v___f_1734_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1734_, 0, v_toPure_1733_);
lean_closure_set(v___f_1734_, 1, v_modifySemiring_1732_);
lean_closure_set(v___f_1734_, 2, v_toBind_1730_);
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1735_, 0, v_toPure_1733_);
lean_closure_set(v___f_1735_, 1, v_inst_1724_);
lean_closure_set(v___f_1735_, 2, v_inst_1725_);
lean_closure_set(v___f_1735_, 3, v_inst_1726_);
lean_closure_set(v___f_1735_, 4, v_inst_1727_);
lean_closure_set(v___f_1735_, 5, v_toBind_1730_);
lean_closure_set(v___f_1735_, 6, v___f_1734_);
v___x_1736_ = lean_apply_4(v_toBind_1730_, lean_box(0), lean_box(0), v_getSemiring_1731_, v___f_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1738_, v_inst_1739_, v_inst_1740_, v_inst_1741_, v_inst_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1744_, lean_object* v_s_1745_){
_start:
{
lean_object* v_id_1746_; lean_object* v_type_1747_; lean_object* v_u_1748_; lean_object* v_semiringInst_1749_; lean_object* v_addFn_x3f_1750_; lean_object* v_mulFn_x3f_1751_; lean_object* v_natCastFn_x3f_1752_; lean_object* v_natSMulFn_x3f_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1761_; 
v_id_1746_ = lean_ctor_get(v_s_1745_, 0);
v_type_1747_ = lean_ctor_get(v_s_1745_, 1);
v_u_1748_ = lean_ctor_get(v_s_1745_, 2);
v_semiringInst_1749_ = lean_ctor_get(v_s_1745_, 3);
v_addFn_x3f_1750_ = lean_ctor_get(v_s_1745_, 4);
v_mulFn_x3f_1751_ = lean_ctor_get(v_s_1745_, 5);
v_natCastFn_x3f_1752_ = lean_ctor_get(v_s_1745_, 7);
v_natSMulFn_x3f_1753_ = lean_ctor_get(v_s_1745_, 8);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_s_1745_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_s_1745_, 6);
lean_dec(v_unused_1762_);
v___x_1755_ = v_s_1745_;
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_natSMulFn_x3f_1753_);
lean_inc(v_natCastFn_x3f_1752_);
lean_inc(v_mulFn_x3f_1751_);
lean_inc(v_addFn_x3f_1750_);
lean_inc(v_semiringInst_1749_);
lean_inc(v_u_1748_);
lean_inc(v_type_1747_);
lean_inc(v_id_1746_);
lean_dec(v_s_1745_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_powFn_1744_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 6, v___x_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_id_1746_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_type_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_u_1748_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_semiringInst_1749_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_addFn_x3f_1750_);
lean_ctor_set(v_reuseFailAlloc_1760_, 5, v_mulFn_x3f_1751_);
lean_ctor_set(v_reuseFailAlloc_1760_, 6, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1760_, 7, v_natCastFn_x3f_1752_);
lean_ctor_set(v_reuseFailAlloc_1760_, 8, v_natSMulFn_x3f_1753_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1763_, lean_object* v_modifySemiring_1764_, lean_object* v_toBind_1765_, lean_object* v_powFn_1766_){
_start:
{
lean_object* v___f_1767_; lean_object* v___f_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_inc_ref(v_powFn_1766_);
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1767_, 0, v_powFn_1766_);
v___f_1768_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1768_, 0, v_toPure_1763_);
lean_closure_set(v___f_1768_, 1, v_powFn_1766_);
v___x_1769_ = lean_apply_1(v_modifySemiring_1764_, v___f_1767_);
v___x_1770_ = lean_apply_4(v_toBind_1765_, lean_box(0), lean_box(0), v___x_1769_, v___f_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_toBind_1776_, lean_object* v___f_1777_, lean_object* v_sr_1778_){
_start:
{
lean_object* v_powFn_x3f_1779_; 
v_powFn_x3f_1779_ = lean_ctor_get(v_sr_1778_, 6);
if (lean_obj_tag(v_powFn_x3f_1779_) == 1)
{
lean_object* v_val_1780_; lean_object* v___x_1781_; 
lean_inc_ref(v_powFn_x3f_1779_);
lean_dec_ref(v_sr_1778_);
lean_dec(v___f_1777_);
lean_dec(v_toBind_1776_);
lean_dec_ref(v_inst_1775_);
lean_dec_ref(v_inst_1774_);
lean_dec_ref(v_inst_1773_);
lean_dec(v_inst_1772_);
v_val_1780_ = lean_ctor_get(v_powFn_x3f_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v_powFn_x3f_1779_, 1);
v___x_1781_ = lean_apply_2(v_toPure_1771_, lean_box(0), v_val_1780_);
return v___x_1781_;
}
else
{
lean_object* v_type_1782_; lean_object* v_u_1783_; lean_object* v_semiringInst_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_dec(v_toPure_1771_);
v_type_1782_ = lean_ctor_get(v_sr_1778_, 1);
lean_inc_ref(v_type_1782_);
v_u_1783_ = lean_ctor_get(v_sr_1778_, 2);
lean_inc(v_u_1783_);
v_semiringInst_1784_ = lean_ctor_get(v_sr_1778_, 3);
lean_inc_ref(v_semiringInst_1784_);
lean_dec_ref(v_sr_1778_);
v___x_1785_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1772_, v_inst_1773_, v_inst_1774_, v_inst_1775_, v_u_1783_, v_type_1782_, v_semiringInst_1784_);
v___x_1786_ = lean_apply_4(v_toBind_1776_, lean_box(0), lean_box(0), v___x_1785_, v___f_1777_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_){
_start:
{
lean_object* v_toApplicative_1792_; lean_object* v_toBind_1793_; lean_object* v_getSemiring_1794_; lean_object* v_modifySemiring_1795_; lean_object* v_toPure_1796_; lean_object* v___f_1797_; lean_object* v___f_1798_; lean_object* v___x_1799_; 
v_toApplicative_1792_ = lean_ctor_get(v_inst_1789_, 0);
v_toBind_1793_ = lean_ctor_get(v_inst_1789_, 1);
lean_inc_n(v_toBind_1793_, 3);
v_getSemiring_1794_ = lean_ctor_get(v_inst_1791_, 0);
lean_inc(v_getSemiring_1794_);
v_modifySemiring_1795_ = lean_ctor_get(v_inst_1791_, 1);
lean_inc(v_modifySemiring_1795_);
lean_dec_ref(v_inst_1791_);
v_toPure_1796_ = lean_ctor_get(v_toApplicative_1792_, 1);
lean_inc_n(v_toPure_1796_, 2);
v___f_1797_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1797_, 0, v_toPure_1796_);
lean_closure_set(v___f_1797_, 1, v_modifySemiring_1795_);
lean_closure_set(v___f_1797_, 2, v_toBind_1793_);
v___f_1798_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1798_, 0, v_toPure_1796_);
lean_closure_set(v___f_1798_, 1, v_inst_1787_);
lean_closure_set(v___f_1798_, 2, v_inst_1788_);
lean_closure_set(v___f_1798_, 3, v_inst_1789_);
lean_closure_set(v___f_1798_, 4, v_inst_1790_);
lean_closure_set(v___f_1798_, 5, v_toBind_1793_);
lean_closure_set(v___f_1798_, 6, v___f_1797_);
v___x_1799_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v_getSemiring_1794_, v___f_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_inst_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1801_, v_inst_1802_, v_inst_1803_, v_inst_1804_, v_inst_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1807_, lean_object* v_s_1808_){
_start:
{
lean_object* v_id_1809_; lean_object* v_type_1810_; lean_object* v_u_1811_; lean_object* v_semiringInst_1812_; lean_object* v_addFn_x3f_1813_; lean_object* v_mulFn_x3f_1814_; lean_object* v_powFn_x3f_1815_; lean_object* v_natSMulFn_x3f_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1824_; 
v_id_1809_ = lean_ctor_get(v_s_1808_, 0);
v_type_1810_ = lean_ctor_get(v_s_1808_, 1);
v_u_1811_ = lean_ctor_get(v_s_1808_, 2);
v_semiringInst_1812_ = lean_ctor_get(v_s_1808_, 3);
v_addFn_x3f_1813_ = lean_ctor_get(v_s_1808_, 4);
v_mulFn_x3f_1814_ = lean_ctor_get(v_s_1808_, 5);
v_powFn_x3f_1815_ = lean_ctor_get(v_s_1808_, 6);
v_natSMulFn_x3f_1816_ = lean_ctor_get(v_s_1808_, 8);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_s_1808_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v_s_1808_, 7);
lean_dec(v_unused_1825_);
v___x_1818_ = v_s_1808_;
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_natSMulFn_x3f_1816_);
lean_inc(v_powFn_x3f_1815_);
lean_inc(v_mulFn_x3f_1814_);
lean_inc(v_addFn_x3f_1813_);
lean_inc(v_semiringInst_1812_);
lean_inc(v_u_1811_);
lean_inc(v_type_1810_);
lean_inc(v_id_1809_);
lean_dec(v_s_1808_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_natCastFn_1807_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 7, v___x_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_id_1809_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_type_1810_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_u_1811_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_semiringInst_1812_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_addFn_x3f_1813_);
lean_ctor_set(v_reuseFailAlloc_1823_, 5, v_mulFn_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1823_, 6, v_powFn_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1823_, 7, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1823_, 8, v_natSMulFn_x3f_1816_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1826_, lean_object* v_modifySemiring_1827_, lean_object* v_toBind_1828_, lean_object* v_natCastFn_1829_){
_start:
{
lean_object* v___f_1830_; lean_object* v___f_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_inc_ref(v_natCastFn_1829_);
v___f_1830_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1830_, 0, v_natCastFn_1829_);
v___f_1831_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1831_, 0, v_toPure_1826_);
lean_closure_set(v___f_1831_, 1, v_natCastFn_1829_);
v___x_1832_ = lean_apply_1(v_modifySemiring_1827_, v___f_1830_);
v___x_1833_ = lean_apply_4(v_toBind_1828_, lean_box(0), lean_box(0), v___x_1832_, v___f_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_toBind_1838_, lean_object* v___f_1839_, lean_object* v_sr_1840_){
_start:
{
lean_object* v_natCastFn_x3f_1841_; 
v_natCastFn_x3f_1841_ = lean_ctor_get(v_sr_1840_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1841_) == 1)
{
lean_object* v_val_1842_; lean_object* v___x_1843_; 
lean_inc_ref(v_natCastFn_x3f_1841_);
lean_dec_ref(v_sr_1840_);
lean_dec(v___f_1839_);
lean_dec(v_toBind_1838_);
lean_dec_ref(v_inst_1837_);
lean_dec_ref(v_inst_1836_);
lean_dec(v_inst_1835_);
v_val_1842_ = lean_ctor_get(v_natCastFn_x3f_1841_, 0);
lean_inc(v_val_1842_);
lean_dec_ref_known(v_natCastFn_x3f_1841_, 1);
v___x_1843_ = lean_apply_2(v_toPure_1834_, lean_box(0), v_val_1842_);
return v___x_1843_;
}
else
{
lean_object* v_type_1844_; lean_object* v_u_1845_; lean_object* v_semiringInst_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v_toPure_1834_);
v_type_1844_ = lean_ctor_get(v_sr_1840_, 1);
lean_inc_ref(v_type_1844_);
v_u_1845_ = lean_ctor_get(v_sr_1840_, 2);
lean_inc(v_u_1845_);
v_semiringInst_1846_ = lean_ctor_get(v_sr_1840_, 3);
lean_inc_ref(v_semiringInst_1846_);
lean_dec_ref(v_sr_1840_);
v___x_1847_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1835_, v_inst_1836_, v_inst_1837_, v_u_1845_, v_type_1844_, v_semiringInst_1846_);
v___x_1848_ = lean_apply_4(v_toBind_1838_, lean_box(0), lean_box(0), v___x_1847_, v___f_1839_);
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_){
_start:
{
lean_object* v_toApplicative_1853_; lean_object* v_toBind_1854_; lean_object* v_getSemiring_1855_; lean_object* v_modifySemiring_1856_; lean_object* v_toPure_1857_; lean_object* v___f_1858_; lean_object* v___f_1859_; lean_object* v___x_1860_; 
v_toApplicative_1853_ = lean_ctor_get(v_inst_1850_, 0);
v_toBind_1854_ = lean_ctor_get(v_inst_1850_, 1);
lean_inc_n(v_toBind_1854_, 3);
v_getSemiring_1855_ = lean_ctor_get(v_inst_1852_, 0);
lean_inc(v_getSemiring_1855_);
v_modifySemiring_1856_ = lean_ctor_get(v_inst_1852_, 1);
lean_inc(v_modifySemiring_1856_);
lean_dec_ref(v_inst_1852_);
v_toPure_1857_ = lean_ctor_get(v_toApplicative_1853_, 1);
lean_inc_n(v_toPure_1857_, 2);
v___f_1858_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1858_, 0, v_toPure_1857_);
lean_closure_set(v___f_1858_, 1, v_modifySemiring_1856_);
lean_closure_set(v___f_1858_, 2, v_toBind_1854_);
v___f_1859_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1859_, 0, v_toPure_1857_);
lean_closure_set(v___f_1859_, 1, v_inst_1849_);
lean_closure_set(v___f_1859_, 2, v_inst_1850_);
lean_closure_set(v___f_1859_, 3, v_inst_1851_);
lean_closure_set(v___f_1859_, 4, v_toBind_1854_);
lean_closure_set(v___f_1859_, 5, v___f_1858_);
v___x_1860_ = lean_apply_4(v_toBind_1854_, lean_box(0), lean_box(0), v_getSemiring_1855_, v___f_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_1861_, lean_object* v_inst_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1862_, v_inst_1863_, v_inst_1864_, v_inst_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0(lean_object* v_toQFn_1867_, lean_object* v_s_1868_){
_start:
{
lean_object* v_toSemiring_1869_; lean_object* v_ringId_1870_; lean_object* v_commSemiringInst_1871_; lean_object* v_addRightCancelInst_x3f_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
v_toSemiring_1869_ = lean_ctor_get(v_s_1868_, 0);
v_ringId_1870_ = lean_ctor_get(v_s_1868_, 1);
v_commSemiringInst_1871_ = lean_ctor_get(v_s_1868_, 2);
v_addRightCancelInst_x3f_1872_ = lean_ctor_get(v_s_1868_, 3);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_s_1868_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v_s_1868_, 4);
lean_dec(v_unused_1881_);
v___x_1874_ = v_s_1868_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_1872_);
lean_inc(v_commSemiringInst_1871_);
lean_inc(v_ringId_1870_);
lean_inc(v_toSemiring_1869_);
lean_dec(v_s_1868_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_toQFn_1867_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 4, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_toSemiring_1869_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_ringId_1870_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_commSemiringInst_1871_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_addRightCancelInst_x3f_1872_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1(lean_object* v_toPure_1882_, lean_object* v_toQFn_1883_, lean_object* v_____r_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_apply_2(v_toPure_1882_, lean_box(0), v_toQFn_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2(lean_object* v_toPure_1886_, lean_object* v_modifyCommSemiring_1887_, lean_object* v_toBind_1888_, lean_object* v_toQFn_1889_){
_start:
{
lean_object* v___f_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_inc_ref(v_toQFn_1889_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1890_, 0, v_toQFn_1889_);
v___f_1891_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1891_, 0, v_toPure_1886_);
lean_closure_set(v___f_1891_, 1, v_toQFn_1889_);
v___x_1892_ = lean_apply_1(v_modifyCommSemiring_1887_, v___f_1890_);
v___x_1893_ = lean_apply_4(v_toBind_1888_, lean_box(0), lean_box(0), v___x_1892_, v___f_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3(lean_object* v_toPure_1902_, lean_object* v_inst_1903_, lean_object* v_toBind_1904_, lean_object* v___f_1905_, lean_object* v_s_1906_){
_start:
{
lean_object* v_toQFn_x3f_1907_; 
v_toQFn_x3f_1907_ = lean_ctor_get(v_s_1906_, 4);
if (lean_obj_tag(v_toQFn_x3f_1907_) == 1)
{
lean_object* v_val_1908_; lean_object* v___x_1909_; 
lean_inc_ref(v_toQFn_x3f_1907_);
lean_dec_ref(v_s_1906_);
lean_dec(v___f_1905_);
lean_dec(v_toBind_1904_);
lean_dec_ref(v_inst_1903_);
v_val_1908_ = lean_ctor_get(v_toQFn_x3f_1907_, 0);
lean_inc(v_val_1908_);
lean_dec_ref_known(v_toQFn_x3f_1907_, 1);
v___x_1909_ = lean_apply_2(v_toPure_1902_, lean_box(0), v_val_1908_);
return v___x_1909_;
}
else
{
lean_object* v_toSemiring_1910_; lean_object* v_canonExpr_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_toPure_1902_);
v_toSemiring_1910_ = lean_ctor_get(v_s_1906_, 0);
lean_inc_ref(v_toSemiring_1910_);
lean_dec_ref(v_s_1906_);
v_canonExpr_1911_ = lean_ctor_get(v_inst_1903_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_inst_1903_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_inst_1903_, 1);
lean_dec(v_unused_1928_);
v___x_1913_ = v_inst_1903_;
v_isShared_1914_ = v_isSharedCheck_1927_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_canonExpr_1911_);
lean_dec(v_inst_1903_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1927_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_type_1915_; lean_object* v_u_1916_; lean_object* v_semiringInst_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v_type_1915_ = lean_ctor_get(v_toSemiring_1910_, 1);
lean_inc_ref(v_type_1915_);
v_u_1916_ = lean_ctor_get(v_toSemiring_1910_, 2);
lean_inc(v_u_1916_);
v_semiringInst_1917_ = lean_ctor_get(v_toSemiring_1910_, 3);
lean_inc_ref(v_semiringInst_1917_);
lean_dec_ref(v_toSemiring_1910_);
v___x_1918_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2));
v___x_1919_ = lean_box(0);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 1);
lean_ctor_set(v___x_1913_, 1, v___x_1919_);
lean_ctor_set(v___x_1913_, 0, v_u_1916_);
v___x_1921_ = v___x_1913_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_u_1916_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1922_ = l_Lean_mkConst(v___x_1918_, v___x_1921_);
v___x_1923_ = l_Lean_mkAppB(v___x_1922_, v_type_1915_, v_semiringInst_1917_);
v___x_1924_ = lean_apply_1(v_canonExpr_1911_, v___x_1923_);
v___x_1925_ = lean_apply_4(v_toBind_1904_, lean_box(0), lean_box(0), v___x_1924_, v___f_1905_);
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg(lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_inst_1931_){
_start:
{
lean_object* v_toApplicative_1932_; lean_object* v_toBind_1933_; lean_object* v_getCommSemiring_1934_; lean_object* v_modifyCommSemiring_1935_; lean_object* v_toPure_1936_; lean_object* v___f_1937_; lean_object* v___f_1938_; lean_object* v___x_1939_; 
v_toApplicative_1932_ = lean_ctor_get(v_inst_1929_, 0);
lean_inc_ref(v_toApplicative_1932_);
v_toBind_1933_ = lean_ctor_get(v_inst_1929_, 1);
lean_inc_n(v_toBind_1933_, 3);
lean_dec_ref(v_inst_1929_);
v_getCommSemiring_1934_ = lean_ctor_get(v_inst_1931_, 0);
lean_inc(v_getCommSemiring_1934_);
v_modifyCommSemiring_1935_ = lean_ctor_get(v_inst_1931_, 1);
lean_inc(v_modifyCommSemiring_1935_);
lean_dec_ref(v_inst_1931_);
v_toPure_1936_ = lean_ctor_get(v_toApplicative_1932_, 1);
lean_inc_n(v_toPure_1936_, 2);
lean_dec_ref(v_toApplicative_1932_);
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1937_, 0, v_toPure_1936_);
lean_closure_set(v___f_1937_, 1, v_modifyCommSemiring_1935_);
lean_closure_set(v___f_1937_, 2, v_toBind_1933_);
v___f_1938_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1938_, 0, v_toPure_1936_);
lean_closure_set(v___f_1938_, 1, v_inst_1930_);
lean_closure_set(v___f_1938_, 2, v_toBind_1933_);
lean_closure_set(v___f_1938_, 3, v___f_1937_);
v___x_1939_ = lean_apply_4(v_toBind_1933_, lean_box(0), lean_box(0), v_getCommSemiring_1934_, v___f_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn(lean_object* v_m_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Meta_Sym_Arith_getToQFn___redArg(v_inst_1941_, v_inst_1942_, v_inst_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0(lean_object* v_addRightCancelInst_x3f_1945_, lean_object* v_s_1946_){
_start:
{
lean_object* v_toSemiring_1947_; lean_object* v_ringId_1948_; lean_object* v_commSemiringInst_1949_; lean_object* v_toQFn_x3f_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1958_; 
v_toSemiring_1947_ = lean_ctor_get(v_s_1946_, 0);
v_ringId_1948_ = lean_ctor_get(v_s_1946_, 1);
v_commSemiringInst_1949_ = lean_ctor_get(v_s_1946_, 2);
v_toQFn_x3f_1950_ = lean_ctor_get(v_s_1946_, 4);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_s_1946_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v_s_1946_, 3);
lean_dec(v_unused_1959_);
v___x_1952_ = v_s_1946_;
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_toQFn_x3f_1950_);
lean_inc(v_commSemiringInst_1949_);
lean_inc(v_ringId_1948_);
lean_inc(v_toSemiring_1947_);
lean_dec(v_s_1946_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_addRightCancelInst_x3f_1945_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 3, v___x_1954_);
v___x_1956_ = v___x_1952_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_toSemiring_1947_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_ringId_1948_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_commSemiringInst_1949_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v_toQFn_x3f_1950_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1(lean_object* v_toPure_1960_, lean_object* v_addRightCancelInst_x3f_1961_, lean_object* v_____r_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_apply_2(v_toPure_1960_, lean_box(0), v_addRightCancelInst_x3f_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2(lean_object* v_toPure_1964_, lean_object* v_modifyCommSemiring_1965_, lean_object* v_toBind_1966_, lean_object* v_addRightCancelInst_x3f_1967_){
_start:
{
lean_object* v___f_1968_; lean_object* v___f_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_inc(v_addRightCancelInst_x3f_1967_);
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1968_, 0, v_addRightCancelInst_x3f_1967_);
v___f_1969_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1969_, 0, v_toPure_1964_);
lean_closure_set(v___f_1969_, 1, v_addRightCancelInst_x3f_1967_);
v___x_1970_ = lean_apply_1(v_modifyCommSemiring_1965_, v___f_1968_);
v___x_1971_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v___x_1970_, v___f_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3(lean_object* v___f_1972_, lean_object* v_addRightCancelInst_x3f_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_apply_1(v___f_1972_, v_addRightCancelInst_x3f_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5(lean_object* v___x_1980_, lean_object* v_type_1981_, lean_object* v_synthInstance_x3f_1982_, lean_object* v_toBind_1983_, lean_object* v___f_1984_, lean_object* v_toPure_1985_, lean_object* v___f_1986_, lean_object* v_____x_1987_){
_start:
{
if (lean_obj_tag(v_____x_1987_) == 1)
{
lean_object* v_val_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_dec(v___f_1986_);
lean_dec(v_toPure_1985_);
v_val_1988_ = lean_ctor_get(v_____x_1987_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v_____x_1987_, 1);
v___x_1989_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1));
v___x_1990_ = l_Lean_mkConst(v___x_1989_, v___x_1980_);
v___x_1991_ = l_Lean_mkAppB(v___x_1990_, v_type_1981_, v_val_1988_);
v___x_1992_ = lean_apply_1(v_synthInstance_x3f_1982_, v___x_1991_);
v___x_1993_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_1992_, v___f_1984_);
return v___x_1993_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec(v_____x_1987_);
lean_dec(v___f_1984_);
lean_dec(v_synthInstance_x3f_1982_);
lean_dec_ref(v_type_1981_);
lean_dec(v___x_1980_);
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_apply_2(v_toPure_1985_, lean_box(0), v___x_1994_);
v___x_1996_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_1995_, v___f_1986_);
return v___x_1996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4(lean_object* v_toPure_2000_, lean_object* v_inst_2001_, lean_object* v_toBind_2002_, lean_object* v___f_2003_, lean_object* v___f_2004_, lean_object* v_s_2005_){
_start:
{
lean_object* v_addRightCancelInst_x3f_2006_; 
v_addRightCancelInst_x3f_2006_ = lean_ctor_get(v_s_2005_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_2006_) == 1)
{
lean_object* v_val_2007_; lean_object* v___x_2008_; 
lean_inc_ref(v_addRightCancelInst_x3f_2006_);
lean_dec_ref(v_s_2005_);
lean_dec(v___f_2004_);
lean_dec(v___f_2003_);
lean_dec(v_toBind_2002_);
lean_dec_ref(v_inst_2001_);
v_val_2007_ = lean_ctor_get(v_addRightCancelInst_x3f_2006_, 0);
lean_inc(v_val_2007_);
lean_dec_ref_known(v_addRightCancelInst_x3f_2006_, 1);
v___x_2008_ = lean_apply_2(v_toPure_2000_, lean_box(0), v_val_2007_);
return v___x_2008_;
}
else
{
lean_object* v_toSemiring_2009_; lean_object* v_synthInstance_x3f_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2026_; 
v_toSemiring_2009_ = lean_ctor_get(v_s_2005_, 0);
lean_inc_ref(v_toSemiring_2009_);
lean_dec_ref(v_s_2005_);
v_synthInstance_x3f_2010_ = lean_ctor_get(v_inst_2001_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_inst_2001_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v_inst_2001_, 0);
lean_dec(v_unused_2027_);
v___x_2012_ = v_inst_2001_;
v_isShared_2013_ = v_isSharedCheck_2026_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_synthInstance_x3f_2010_);
lean_dec(v_inst_2001_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2026_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_type_2014_; lean_object* v_u_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v_type_2014_ = lean_ctor_get(v_toSemiring_2009_, 1);
lean_inc_ref(v_type_2014_);
v_u_2015_ = lean_ctor_get(v_toSemiring_2009_, 2);
lean_inc(v_u_2015_);
lean_dec_ref(v_toSemiring_2009_);
v___x_2016_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1));
v___x_2017_ = lean_box(0);
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 1);
lean_ctor_set(v___x_2012_, 1, v___x_2017_);
lean_ctor_set(v___x_2012_, 0, v_u_2015_);
v___x_2019_ = v___x_2012_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_u_2015_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___f_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_inc(v_toBind_2002_);
lean_inc(v_synthInstance_x3f_2010_);
lean_inc_ref(v_type_2014_);
lean_inc_ref(v___x_2019_);
v___f_2020_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_2020_, 0, v___x_2019_);
lean_closure_set(v___f_2020_, 1, v_type_2014_);
lean_closure_set(v___f_2020_, 2, v_synthInstance_x3f_2010_);
lean_closure_set(v___f_2020_, 3, v_toBind_2002_);
lean_closure_set(v___f_2020_, 4, v___f_2003_);
lean_closure_set(v___f_2020_, 5, v_toPure_2000_);
lean_closure_set(v___f_2020_, 6, v___f_2004_);
v___x_2021_ = l_Lean_mkConst(v___x_2016_, v___x_2019_);
v___x_2022_ = l_Lean_Expr_app___override(v___x_2021_, v_type_2014_);
v___x_2023_ = lean_apply_1(v_synthInstance_x3f_2010_, v___x_2022_);
v___x_2024_ = lean_apply_4(v_toBind_2002_, lean_box(0), lean_box(0), v___x_2023_, v___f_2020_);
return v___x_2024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_){
_start:
{
lean_object* v_toApplicative_2031_; lean_object* v_toBind_2032_; lean_object* v_getCommSemiring_2033_; lean_object* v_modifyCommSemiring_2034_; lean_object* v_toPure_2035_; lean_object* v___f_2036_; lean_object* v___f_2037_; lean_object* v___f_2038_; lean_object* v___x_2039_; 
v_toApplicative_2031_ = lean_ctor_get(v_inst_2028_, 0);
lean_inc_ref(v_toApplicative_2031_);
v_toBind_2032_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2032_, 3);
lean_dec_ref(v_inst_2028_);
v_getCommSemiring_2033_ = lean_ctor_get(v_inst_2030_, 0);
lean_inc(v_getCommSemiring_2033_);
v_modifyCommSemiring_2034_ = lean_ctor_get(v_inst_2030_, 1);
lean_inc(v_modifyCommSemiring_2034_);
lean_dec_ref(v_inst_2030_);
v_toPure_2035_ = lean_ctor_get(v_toApplicative_2031_, 1);
lean_inc_n(v_toPure_2035_, 2);
lean_dec_ref(v_toApplicative_2031_);
v___f_2036_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2036_, 0, v_toPure_2035_);
lean_closure_set(v___f_2036_, 1, v_modifyCommSemiring_2034_);
lean_closure_set(v___f_2036_, 2, v_toBind_2032_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2037_, 0, v___f_2036_);
lean_inc_ref(v___f_2037_);
v___f_2038_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4), 6, 5);
lean_closure_set(v___f_2038_, 0, v_toPure_2035_);
lean_closure_set(v___f_2038_, 1, v_inst_2029_);
lean_closure_set(v___f_2038_, 2, v_toBind_2032_);
lean_closure_set(v___f_2038_, 3, v___f_2037_);
lean_closure_set(v___f_2038_, 4, v___f_2037_);
v___x_2039_ = lean_apply_4(v_toBind_2032_, lean_box(0), lean_box(0), v_getCommSemiring_2033_, v___f_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f(lean_object* v_m_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(v_inst_2041_, v_inst_2042_, v_inst_2043_);
return v___x_2044_;
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
