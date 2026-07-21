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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
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
lean_object* v_keyedConfig_67_; uint8_t v_trackZetaDelta_68_; lean_object* v_zetaDeltaSet_69_; lean_object* v_lctx_70_; lean_object* v_localInstances_71_; lean_object* v_defEqCtx_x3f_72_; lean_object* v_synthPendingDepth_73_; lean_object* v_customCanUnfoldPredicate_x3f_74_; uint8_t v_univApprox_75_; uint8_t v_inTypeClassResolution_76_; uint8_t v_cacheInferType_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_keyedConfig_67_ = lean_ctor_get(v_a_62_, 0);
v_trackZetaDelta_68_ = lean_ctor_get_uint8(v_a_62_, sizeof(void*)*7);
v_zetaDeltaSet_69_ = lean_ctor_get(v_a_62_, 1);
v_lctx_70_ = lean_ctor_get(v_a_62_, 2);
v_localInstances_71_ = lean_ctor_get(v_a_62_, 3);
v_defEqCtx_x3f_72_ = lean_ctor_get(v_a_62_, 4);
v_synthPendingDepth_73_ = lean_ctor_get(v_a_62_, 5);
v_customCanUnfoldPredicate_x3f_74_ = lean_ctor_get(v_a_62_, 6);
v_univApprox_75_ = lean_ctor_get_uint8(v_a_62_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_76_ = lean_ctor_get_uint8(v_a_62_, sizeof(void*)*7 + 2);
v_cacheInferType_77_ = lean_ctor_get_uint8(v_a_62_, sizeof(void*)*7 + 3);
v___x_78_ = 3;
lean_inc_ref(v_keyedConfig_67_);
v___x_79_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_78_, v_keyedConfig_67_);
lean_inc(v_customCanUnfoldPredicate_x3f_74_);
lean_inc(v_synthPendingDepth_73_);
lean_inc(v_defEqCtx_x3f_72_);
lean_inc_ref(v_localInstances_71_);
lean_inc_ref(v_lctx_70_);
lean_inc(v_zetaDeltaSet_69_);
v___x_80_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_zetaDeltaSet_69_);
lean_ctor_set(v___x_80_, 2, v_lctx_70_);
lean_ctor_set(v___x_80_, 3, v_localInstances_71_);
lean_ctor_set(v___x_80_, 4, v_defEqCtx_x3f_72_);
lean_ctor_set(v___x_80_, 5, v_synthPendingDepth_73_);
lean_ctor_set(v___x_80_, 6, v_customCanUnfoldPredicate_x3f_74_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*7, v_trackZetaDelta_68_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*7 + 1, v_univApprox_75_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*7 + 2, v_inTypeClassResolution_76_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*7 + 3, v_cacheInferType_77_);
lean_inc_ref(v_inst_x27_61_);
lean_inc_ref(v_inst_60_);
v___x_81_ = l_Lean_Meta_isExprDefEq(v_inst_60_, v_inst_x27_61_, v___x_80_, v_a_63_, v_a_64_, v_a_65_);
lean_dec_ref_known(v___x_80_, 7);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_105_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_105_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_105_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_105_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
uint8_t v___x_86_; 
v___x_86_ = lean_unbox(v_a_82_);
lean_dec(v_a_82_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
lean_del_object(v___x_84_);
v___x_87_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1);
v___x_88_ = l_Lean_MessageData_ofName(v_declName_59_);
v___x_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3);
v___x_91_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_indentExpr(v_inst_60_);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5);
v___x_95_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = l_Lean_indentExpr(v_inst_x27_61_);
v___x_97_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7);
v___x_99_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_99_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_103_; 
lean_dec_ref(v_inst_x27_61_);
lean_dec_ref(v_inst_60_);
lean_dec(v_declName_59_);
v___x_101_ = lean_box(0);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_101_);
v___x_103_ = v___x_84_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
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
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec_ref(v_inst_x27_61_);
lean_dec_ref(v_inst_60_);
lean_dec(v_declName_59_);
v_a_106_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_81_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_81_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object* v_declName_114_, lean_object* v_inst_115_, lean_object* v_inst_x27_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_114_, v_inst_115_, v_inst_x27_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object* v_00_u03b1_123_, lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(lean_object* v_00_u03b1_131_, lean_object* v_msg_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(v_00_u03b1_131_, v_msg_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object* v_inst_139_, lean_object* v_declName_140_, lean_object* v___x_141_, lean_object* v_type_142_, lean_object* v_inst_143_, lean_object* v_____r_144_){
_start:
{
lean_object* v_canonExpr_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_canonExpr_145_ = lean_ctor_get(v_inst_139_, 0);
lean_inc(v_canonExpr_145_);
lean_dec_ref(v_inst_139_);
v___x_146_ = l_Lean_mkConst(v_declName_140_, v___x_141_);
v___x_147_ = l_Lean_mkAppB(v___x_146_, v_type_142_, v_inst_143_);
v___x_148_ = lean_apply_1(v_canonExpr_145_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object* v_inst_149_, lean_object* v_declName_150_, lean_object* v___x_151_, lean_object* v_type_152_, lean_object* v_expectedInst_153_, lean_object* v_inst_154_, lean_object* v_toBind_155_, lean_object* v_inst_156_){
_start:
{
lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
lean_inc_ref(v_inst_156_);
lean_inc(v_declName_150_);
v___f_157_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_157_, 0, v_inst_149_);
lean_closure_set(v___f_157_, 1, v_declName_150_);
lean_closure_set(v___f_157_, 2, v___x_151_);
lean_closure_set(v___f_157_, 3, v_type_152_);
lean_closure_set(v___f_157_, 4, v_inst_156_);
v___x_158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_158_, 0, v_declName_150_);
lean_closure_set(v___x_158_, 1, v_inst_156_);
lean_closure_set(v___x_158_, 2, v_expectedInst_153_);
v___x_159_ = lean_apply_2(v_inst_154_, lean_box(0), v___x_158_);
v___x_160_ = lean_apply_4(v_toBind_155_, lean_box(0), lean_box(0), v___x_159_, v___f_157_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_type_165_, lean_object* v_u_166_, lean_object* v_instDeclName_167_, lean_object* v_declName_168_, lean_object* v_expectedInst_169_){
_start:
{
lean_object* v_toBind_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_toBind_170_ = lean_ctor_get(v_inst_163_, 1);
lean_inc_n(v_toBind_170_, 2);
v___x_171_ = lean_box(0);
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v_u_166_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
lean_inc_ref(v_type_165_);
lean_inc_ref(v___x_172_);
lean_inc_ref(v_inst_164_);
v___f_173_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_173_, 0, v_inst_164_);
lean_closure_set(v___f_173_, 1, v_declName_168_);
lean_closure_set(v___f_173_, 2, v___x_172_);
lean_closure_set(v___f_173_, 3, v_type_165_);
lean_closure_set(v___f_173_, 4, v_expectedInst_169_);
lean_closure_set(v___f_173_, 5, v_inst_161_);
lean_closure_set(v___f_173_, 6, v_toBind_170_);
v___x_174_ = l_Lean_mkConst(v_instDeclName_167_, v___x_172_);
v___x_175_ = l_Lean_Expr_app___override(v___x_174_, v_type_165_);
v___x_176_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_163_, v_inst_162_, v_inst_164_, v___x_175_);
v___x_177_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v___x_176_, v___f_173_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object* v_m_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_type_183_, lean_object* v_u_184_, lean_object* v_instDeclName_185_, lean_object* v_declName_186_, lean_object* v_expectedInst_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_179_, v_inst_180_, v_inst_181_, v_inst_182_, v_type_183_, v_u_184_, v_instDeclName_185_, v_declName_186_, v_expectedInst_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_189_, lean_object* v_declName_190_, lean_object* v___x_191_, lean_object* v_type_192_, lean_object* v_inst_193_, lean_object* v_____r_194_){
_start:
{
lean_object* v_canonExpr_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_canonExpr_195_ = lean_ctor_get(v_inst_189_, 0);
lean_inc(v_canonExpr_195_);
lean_dec_ref(v_inst_189_);
v___x_196_ = l_Lean_mkConst(v_declName_190_, v___x_191_);
lean_inc_ref_n(v_type_192_, 2);
v___x_197_ = l_Lean_mkApp4(v___x_196_, v_type_192_, v_type_192_, v_type_192_, v_inst_193_);
v___x_198_ = lean_apply_1(v_canonExpr_195_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_199_, lean_object* v_declName_200_, lean_object* v___x_201_, lean_object* v_type_202_, lean_object* v_expectedInst_203_, lean_object* v_inst_204_, lean_object* v_toBind_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_inc_ref(v_inst_206_);
lean_inc(v_declName_200_);
v___f_207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_207_, 0, v_inst_199_);
lean_closure_set(v___f_207_, 1, v_declName_200_);
lean_closure_set(v___f_207_, 2, v___x_201_);
lean_closure_set(v___f_207_, 3, v_type_202_);
lean_closure_set(v___f_207_, 4, v_inst_206_);
v___x_208_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_208_, 0, v_declName_200_);
lean_closure_set(v___x_208_, 1, v_inst_206_);
lean_closure_set(v___x_208_, 2, v_expectedInst_203_);
v___x_209_ = lean_apply_2(v_inst_204_, lean_box(0), v___x_208_);
v___x_210_ = lean_apply_4(v_toBind_205_, lean_box(0), lean_box(0), v___x_209_, v___f_207_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_type_215_, lean_object* v_u_216_, lean_object* v_instDeclName_217_, lean_object* v_declName_218_, lean_object* v_expectedInst_219_){
_start:
{
lean_object* v_toBind_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_toBind_220_ = lean_ctor_get(v_inst_213_, 1);
lean_inc_n(v_toBind_220_, 2);
v___x_221_ = lean_box(0);
lean_inc_n(v_u_216_, 2);
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v_u_216_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v_u_216_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v_u_216_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
lean_inc_ref_n(v_type_215_, 3);
lean_inc_ref(v___x_224_);
lean_inc_ref(v_inst_214_);
v___f_225_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_225_, 0, v_inst_214_);
lean_closure_set(v___f_225_, 1, v_declName_218_);
lean_closure_set(v___f_225_, 2, v___x_224_);
lean_closure_set(v___f_225_, 3, v_type_215_);
lean_closure_set(v___f_225_, 4, v_expectedInst_219_);
lean_closure_set(v___f_225_, 5, v_inst_211_);
lean_closure_set(v___f_225_, 6, v_toBind_220_);
v___x_226_ = l_Lean_mkConst(v_instDeclName_217_, v___x_224_);
v___x_227_ = l_Lean_mkApp3(v___x_226_, v_type_215_, v_type_215_, v_type_215_);
v___x_228_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_213_, v_inst_212_, v_inst_214_, v___x_227_);
v___x_229_ = lean_apply_4(v_toBind_220_, lean_box(0), lean_box(0), v___x_228_, v___f_225_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object* v_m_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_type_235_, lean_object* v_u_236_, lean_object* v_instDeclName_237_, lean_object* v_declName_238_, lean_object* v_expectedInst_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_231_, v_inst_232_, v_inst_233_, v_inst_234_, v_type_235_, v_u_236_, v_instDeclName_237_, v_declName_238_, v_expectedInst_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object* v_inst_241_, lean_object* v___x_242_, lean_object* v___x_243_, lean_object* v_type_244_, lean_object* v___x_245_, lean_object* v_inst_246_, lean_object* v_____r_247_){
_start:
{
lean_object* v_canonExpr_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_canonExpr_248_ = lean_ctor_get(v_inst_241_, 0);
lean_inc(v_canonExpr_248_);
lean_dec_ref(v_inst_241_);
v___x_249_ = l_Lean_mkConst(v___x_242_, v___x_243_);
lean_inc_ref(v_type_244_);
v___x_250_ = l_Lean_mkApp4(v___x_249_, v_type_244_, v___x_245_, v_type_244_, v_inst_246_);
v___x_251_ = lean_apply_1(v_canonExpr_248_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object* v___x_262_, lean_object* v_type_263_, lean_object* v_semiringInst_264_, lean_object* v___x_265_, lean_object* v_inst_266_, lean_object* v___x_267_, lean_object* v___x_268_, lean_object* v_inst_269_, lean_object* v_toBind_270_, lean_object* v_inst_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_inst_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___f_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4));
v___x_273_ = l_Lean_mkConst(v___x_272_, v___x_262_);
lean_inc_ref(v_type_263_);
v_inst_x27_274_ = l_Lean_mkAppB(v___x_273_, v_type_263_, v_semiringInst_264_);
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5));
v___x_276_ = l_Lean_Name_mkStr2(v___x_265_, v___x_275_);
lean_inc_ref(v_inst_271_);
lean_inc(v___x_276_);
v___f_277_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_277_, 0, v_inst_266_);
lean_closure_set(v___f_277_, 1, v___x_276_);
lean_closure_set(v___f_277_, 2, v___x_267_);
lean_closure_set(v___f_277_, 3, v_type_263_);
lean_closure_set(v___f_277_, 4, v___x_268_);
lean_closure_set(v___f_277_, 5, v_inst_271_);
v___x_278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_278_, 0, v___x_276_);
lean_closure_set(v___x_278_, 1, v_inst_271_);
lean_closure_set(v___x_278_, 2, v_inst_x27_274_);
v___x_279_ = lean_apply_2(v_inst_269_, lean_box(0), v___x_278_);
v___x_280_ = lean_apply_4(v_toBind_270_, lean_box(0), lean_box(0), v___x_279_, v___f_277_);
return v___x_280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = l_Lean_Level_ofNat(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_u_290_, lean_object* v_type_291_, lean_object* v_semiringInst_292_){
_start:
{
lean_object* v_toBind_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___f_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_toBind_293_ = lean_ctor_get(v_inst_288_, 1);
lean_inc_n(v_toBind_293_, 2);
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0));
v___x_295_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1));
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_297_ = lean_box(0);
lean_inc(v_u_290_);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v_u_290_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_inc_ref(v___x_298_);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_296_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_300_, 0, v_u_290_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
lean_inc_ref(v___x_300_);
v___x_301_ = l_Lean_mkConst(v___x_295_, v___x_300_);
v___x_302_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_289_);
lean_inc_ref_n(v_type_291_, 2);
v___f_303_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_303_, 0, v___x_298_);
lean_closure_set(v___f_303_, 1, v_type_291_);
lean_closure_set(v___f_303_, 2, v_semiringInst_292_);
lean_closure_set(v___f_303_, 3, v___x_294_);
lean_closure_set(v___f_303_, 4, v_inst_289_);
lean_closure_set(v___f_303_, 5, v___x_300_);
lean_closure_set(v___f_303_, 6, v___x_302_);
lean_closure_set(v___f_303_, 7, v_inst_286_);
lean_closure_set(v___f_303_, 8, v_toBind_293_);
v___x_304_ = l_Lean_mkApp3(v___x_301_, v_type_291_, v___x_302_, v_type_291_);
v___x_305_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_288_, v_inst_287_, v_inst_289_, v___x_304_);
v___x_306_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v___x_305_, v___f_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object* v_m_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_u_312_, lean_object* v_type_313_, lean_object* v_semiringInst_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_308_, v_inst_309_, v_inst_310_, v_inst_311_, v_u_312_, v_type_313_, v_semiringInst_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object* v___x_316_, lean_object* v___x_317_, lean_object* v___x_318_, lean_object* v_type_319_, lean_object* v_canonExpr_320_, lean_object* v_inst_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_322_ = l_Lean_Name_mkStr2(v___x_316_, v___x_317_);
v___x_323_ = l_Lean_mkConst(v___x_322_, v___x_318_);
v___x_324_ = l_Lean_mkAppB(v___x_323_, v_type_319_, v_inst_321_);
v___x_325_ = lean_apply_1(v_canonExpr_320_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object* v___f_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_apply_1(v___f_326_, v_inst_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_329_, lean_object* v_val_330_, lean_object* v_toBind_331_, lean_object* v___f_332_, lean_object* v_____r_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_apply_2(v_toPure_329_, lean_box(0), v_val_330_);
v___x_335_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v___x_334_, v___f_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_336_, lean_object* v_inst_x27_337_, lean_object* v_toBind_338_, lean_object* v___f_339_, lean_object* v___f_340_, lean_object* v___x_341_, lean_object* v___x_342_, lean_object* v_inst_343_, lean_object* v_____do__lift_344_){
_start:
{
if (lean_obj_tag(v_____do__lift_344_) == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_inst_343_);
lean_dec_ref(v___x_342_);
lean_dec_ref(v___x_341_);
lean_dec(v___f_340_);
v___x_345_ = lean_apply_2(v_toPure_336_, lean_box(0), v_inst_x27_337_);
v___x_346_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_345_, v___f_339_);
return v___x_346_;
}
else
{
lean_object* v_val_347_; lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v___f_339_);
v_val_347_ = lean_ctor_get(v_____do__lift_344_, 0);
lean_inc_n(v_val_347_, 2);
lean_dec_ref_known(v_____do__lift_344_, 1);
lean_inc(v_toBind_338_);
v___f_348_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_348_, 0, v_toPure_336_);
lean_closure_set(v___f_348_, 1, v_val_347_);
lean_closure_set(v___f_348_, 2, v_toBind_338_);
lean_closure_set(v___f_348_, 3, v___f_340_);
v___x_349_ = l_Lean_Name_mkStr2(v___x_341_, v___x_342_);
v___x_350_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_350_, 0, v___x_349_);
lean_closure_set(v___x_350_, 1, v_val_347_);
lean_closure_set(v___x_350_, 2, v_inst_x27_337_);
v___x_351_ = lean_apply_2(v_inst_343_, lean_box(0), v___x_350_);
v___x_352_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_351_, v___f_348_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_u_365_, lean_object* v_type_366_, lean_object* v_semiringInst_367_){
_start:
{
lean_object* v_toApplicative_368_; lean_object* v_toBind_369_; lean_object* v_canonExpr_370_; lean_object* v_synthInstance_x3f_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_393_; 
v_toApplicative_368_ = lean_ctor_get(v_inst_363_, 0);
lean_inc_ref(v_toApplicative_368_);
v_toBind_369_ = lean_ctor_get(v_inst_363_, 1);
lean_inc(v_toBind_369_);
lean_dec_ref(v_inst_363_);
v_canonExpr_370_ = lean_ctor_get(v_inst_364_, 0);
v_synthInstance_x3f_371_ = lean_ctor_get(v_inst_364_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v_inst_364_);
if (v_isSharedCheck_393_ == 0)
{
v___x_373_ = v_inst_364_;
v_isShared_374_ = v_isSharedCheck_393_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_synthInstance_x3f_371_);
lean_inc(v_canonExpr_370_);
lean_dec(v_inst_364_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_393_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_toPure_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v_toPure_375_ = lean_ctor_get(v_toApplicative_368_, 1);
lean_inc(v_toPure_375_);
lean_dec_ref(v_toApplicative_368_);
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0));
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1));
v___x_378_ = lean_box(0);
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 1);
lean_ctor_set(v___x_373_, 1, v___x_378_);
lean_ctor_set(v___x_373_, 0, v_u_365_);
v___x_380_ = v___x_373_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_u_365_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_392_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v_inst_x27_382_; lean_object* v___x_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_instType_388_; lean_object* v___x_389_; lean_object* v___f_390_; lean_object* v___x_391_; 
lean_inc_ref_n(v___x_380_, 2);
v___x_381_ = l_Lean_mkConst(v___x_377_, v___x_380_);
lean_inc_ref_n(v_type_366_, 2);
v_inst_x27_382_ = l_Lean_mkAppB(v___x_381_, v_type_366_, v_semiringInst_367_);
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2));
v___f_384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_384_, 0, v___x_383_);
lean_closure_set(v___f_384_, 1, v___x_376_);
lean_closure_set(v___f_384_, 2, v___x_380_);
lean_closure_set(v___f_384_, 3, v_type_366_);
lean_closure_set(v___f_384_, 4, v_canonExpr_370_);
v___f_385_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_385_, 0, v___f_384_);
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3));
v___x_387_ = l_Lean_mkConst(v___x_386_, v___x_380_);
v_instType_388_ = l_Lean_Expr_app___override(v___x_387_, v_type_366_);
v___x_389_ = lean_apply_1(v_synthInstance_x3f_371_, v_instType_388_);
lean_inc_ref(v___f_385_);
lean_inc(v_toBind_369_);
v___f_390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_390_, 0, v_toPure_375_);
lean_closure_set(v___f_390_, 1, v_inst_x27_382_);
lean_closure_set(v___f_390_, 2, v_toBind_369_);
lean_closure_set(v___f_390_, 3, v___f_385_);
lean_closure_set(v___f_390_, 4, v___f_385_);
lean_closure_set(v___f_390_, 5, v___x_383_);
lean_closure_set(v___f_390_, 6, v___x_376_);
lean_closure_set(v___f_390_, 7, v_inst_362_);
v___x_391_ = lean_apply_4(v_toBind_369_, lean_box(0), lean_box(0), v___x_389_, v___f_390_);
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object* v_m_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_u_398_, lean_object* v_type_399_, lean_object* v_semiringInst_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_395_, v_inst_396_, v_inst_397_, v_u_398_, v_type_399_, v_semiringInst_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_402_, lean_object* v_s_403_){
_start:
{
lean_object* v_id_404_; lean_object* v_type_405_; lean_object* v_u_406_; lean_object* v_ringInst_407_; lean_object* v_semiringInst_408_; lean_object* v_charInst_x3f_409_; lean_object* v_mulFn_x3f_410_; lean_object* v_subFn_x3f_411_; lean_object* v_negFn_x3f_412_; lean_object* v_powFn_x3f_413_; lean_object* v_intCastFn_x3f_414_; lean_object* v_natCastFn_x3f_415_; lean_object* v_one_x3f_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_424_; 
v_id_404_ = lean_ctor_get(v_s_403_, 0);
v_type_405_ = lean_ctor_get(v_s_403_, 1);
v_u_406_ = lean_ctor_get(v_s_403_, 2);
v_ringInst_407_ = lean_ctor_get(v_s_403_, 3);
v_semiringInst_408_ = lean_ctor_get(v_s_403_, 4);
v_charInst_x3f_409_ = lean_ctor_get(v_s_403_, 5);
v_mulFn_x3f_410_ = lean_ctor_get(v_s_403_, 7);
v_subFn_x3f_411_ = lean_ctor_get(v_s_403_, 8);
v_negFn_x3f_412_ = lean_ctor_get(v_s_403_, 9);
v_powFn_x3f_413_ = lean_ctor_get(v_s_403_, 10);
v_intCastFn_x3f_414_ = lean_ctor_get(v_s_403_, 11);
v_natCastFn_x3f_415_ = lean_ctor_get(v_s_403_, 12);
v_one_x3f_416_ = lean_ctor_get(v_s_403_, 13);
v_isSharedCheck_424_ = !lean_is_exclusive(v_s_403_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_s_403_, 6);
lean_dec(v_unused_425_);
v___x_418_ = v_s_403_;
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_one_x3f_416_);
lean_inc(v_natCastFn_x3f_415_);
lean_inc(v_intCastFn_x3f_414_);
lean_inc(v_powFn_x3f_413_);
lean_inc(v_negFn_x3f_412_);
lean_inc(v_subFn_x3f_411_);
lean_inc(v_mulFn_x3f_410_);
lean_inc(v_charInst_x3f_409_);
lean_inc(v_semiringInst_408_);
lean_inc(v_ringInst_407_);
lean_inc(v_u_406_);
lean_inc(v_type_405_);
lean_inc(v_id_404_);
lean_dec(v_s_403_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v_addFn_402_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 6, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_id_404_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_type_405_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_u_406_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_ringInst_407_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_semiringInst_408_);
lean_ctor_set(v_reuseFailAlloc_423_, 5, v_charInst_x3f_409_);
lean_ctor_set(v_reuseFailAlloc_423_, 6, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 7, v_mulFn_x3f_410_);
lean_ctor_set(v_reuseFailAlloc_423_, 8, v_subFn_x3f_411_);
lean_ctor_set(v_reuseFailAlloc_423_, 9, v_negFn_x3f_412_);
lean_ctor_set(v_reuseFailAlloc_423_, 10, v_powFn_x3f_413_);
lean_ctor_set(v_reuseFailAlloc_423_, 11, v_intCastFn_x3f_414_);
lean_ctor_set(v_reuseFailAlloc_423_, 12, v_natCastFn_x3f_415_);
lean_ctor_set(v_reuseFailAlloc_423_, 13, v_one_x3f_416_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_426_, lean_object* v_addFn_427_, lean_object* v_____r_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_apply_2(v_toPure_426_, lean_box(0), v_addFn_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_430_, lean_object* v_modifyRing_431_, lean_object* v_toBind_432_, lean_object* v_addFn_433_){
_start:
{
lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_inc_ref(v_addFn_433_);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_434_, 0, v_addFn_433_);
v___f_435_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_435_, 0, v_toPure_430_);
lean_closure_set(v___f_435_, 1, v_addFn_433_);
v___x_436_ = lean_apply_1(v_modifyRing_431_, v___f_434_);
v___x_437_ = lean_apply_4(v_toBind_432_, lean_box(0), lean_box(0), v___x_436_, v___f_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_toBind_459_, lean_object* v___f_460_, lean_object* v_ring_461_){
_start:
{
lean_object* v_addFn_x3f_462_; 
v_addFn_x3f_462_ = lean_ctor_get(v_ring_461_, 6);
if (lean_obj_tag(v_addFn_x3f_462_) == 1)
{
lean_object* v_val_463_; lean_object* v___x_464_; 
lean_inc_ref(v_addFn_x3f_462_);
lean_dec_ref(v_ring_461_);
lean_dec(v___f_460_);
lean_dec(v_toBind_459_);
lean_dec_ref(v_inst_458_);
lean_dec_ref(v_inst_457_);
lean_dec_ref(v_inst_456_);
lean_dec(v_inst_455_);
v_val_463_ = lean_ctor_get(v_addFn_x3f_462_, 0);
lean_inc(v_val_463_);
lean_dec_ref_known(v_addFn_x3f_462_, 1);
v___x_464_ = lean_apply_2(v_toPure_454_, lean_box(0), v_val_463_);
return v___x_464_;
}
else
{
lean_object* v_type_465_; lean_object* v_u_466_; lean_object* v_semiringInst_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_expectedInst_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_toPure_454_);
v_type_465_ = lean_ctor_get(v_ring_461_, 1);
lean_inc_ref_n(v_type_465_, 3);
v_u_466_ = lean_ctor_get(v_ring_461_, 2);
lean_inc_n(v_u_466_, 2);
v_semiringInst_467_ = lean_ctor_get(v_ring_461_, 4);
lean_inc_ref(v_semiringInst_467_);
lean_dec_ref(v_ring_461_);
v___x_468_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_469_ = lean_box(0);
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v_u_466_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
lean_inc_ref(v___x_470_);
v___x_471_ = l_Lean_mkConst(v___x_468_, v___x_470_);
v___x_472_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_473_ = l_Lean_mkConst(v___x_472_, v___x_470_);
v___x_474_ = l_Lean_mkAppB(v___x_473_, v_type_465_, v_semiringInst_467_);
v_expectedInst_475_ = l_Lean_mkAppB(v___x_471_, v_type_465_, v___x_474_);
v___x_476_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_477_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_478_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_455_, v_inst_456_, v_inst_457_, v_inst_458_, v_type_465_, v_u_466_, v___x_476_, v___x_477_, v_expectedInst_475_);
v___x_479_ = lean_apply_4(v_toBind_459_, lean_box(0), lean_box(0), v___x_478_, v___f_460_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_){
_start:
{
lean_object* v_toApplicative_485_; lean_object* v_toBind_486_; lean_object* v_getRing_487_; lean_object* v_modifyRing_488_; lean_object* v_toPure_489_; lean_object* v___f_490_; lean_object* v___f_491_; lean_object* v___x_492_; 
v_toApplicative_485_ = lean_ctor_get(v_inst_482_, 0);
v_toBind_486_ = lean_ctor_get(v_inst_482_, 1);
lean_inc_n(v_toBind_486_, 3);
v_getRing_487_ = lean_ctor_get(v_inst_484_, 0);
lean_inc(v_getRing_487_);
v_modifyRing_488_ = lean_ctor_get(v_inst_484_, 1);
lean_inc(v_modifyRing_488_);
lean_dec_ref(v_inst_484_);
v_toPure_489_ = lean_ctor_get(v_toApplicative_485_, 1);
lean_inc_n(v_toPure_489_, 2);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_490_, 0, v_toPure_489_);
lean_closure_set(v___f_490_, 1, v_modifyRing_488_);
lean_closure_set(v___f_490_, 2, v_toBind_486_);
v___f_491_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_491_, 0, v_toPure_489_);
lean_closure_set(v___f_491_, 1, v_inst_480_);
lean_closure_set(v___f_491_, 2, v_inst_481_);
lean_closure_set(v___f_491_, 3, v_inst_482_);
lean_closure_set(v___f_491_, 4, v_inst_483_);
lean_closure_set(v___f_491_, 5, v_toBind_486_);
lean_closure_set(v___f_491_, 6, v___f_490_);
v___x_492_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v_getRing_487_, v___f_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_494_, v_inst_495_, v_inst_496_, v_inst_497_, v_inst_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_500_, lean_object* v_s_501_){
_start:
{
lean_object* v_id_502_; lean_object* v_type_503_; lean_object* v_u_504_; lean_object* v_ringInst_505_; lean_object* v_semiringInst_506_; lean_object* v_charInst_x3f_507_; lean_object* v_addFn_x3f_508_; lean_object* v_subFn_x3f_509_; lean_object* v_negFn_x3f_510_; lean_object* v_powFn_x3f_511_; lean_object* v_intCastFn_x3f_512_; lean_object* v_natCastFn_x3f_513_; lean_object* v_one_x3f_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_id_502_ = lean_ctor_get(v_s_501_, 0);
v_type_503_ = lean_ctor_get(v_s_501_, 1);
v_u_504_ = lean_ctor_get(v_s_501_, 2);
v_ringInst_505_ = lean_ctor_get(v_s_501_, 3);
v_semiringInst_506_ = lean_ctor_get(v_s_501_, 4);
v_charInst_x3f_507_ = lean_ctor_get(v_s_501_, 5);
v_addFn_x3f_508_ = lean_ctor_get(v_s_501_, 6);
v_subFn_x3f_509_ = lean_ctor_get(v_s_501_, 8);
v_negFn_x3f_510_ = lean_ctor_get(v_s_501_, 9);
v_powFn_x3f_511_ = lean_ctor_get(v_s_501_, 10);
v_intCastFn_x3f_512_ = lean_ctor_get(v_s_501_, 11);
v_natCastFn_x3f_513_ = lean_ctor_get(v_s_501_, 12);
v_one_x3f_514_ = lean_ctor_get(v_s_501_, 13);
v_isSharedCheck_522_ = !lean_is_exclusive(v_s_501_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_s_501_, 7);
lean_dec(v_unused_523_);
v___x_516_ = v_s_501_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_one_x3f_514_);
lean_inc(v_natCastFn_x3f_513_);
lean_inc(v_intCastFn_x3f_512_);
lean_inc(v_powFn_x3f_511_);
lean_inc(v_negFn_x3f_510_);
lean_inc(v_subFn_x3f_509_);
lean_inc(v_addFn_x3f_508_);
lean_inc(v_charInst_x3f_507_);
lean_inc(v_semiringInst_506_);
lean_inc(v_ringInst_505_);
lean_inc(v_u_504_);
lean_inc(v_type_503_);
lean_inc(v_id_502_);
lean_dec(v_s_501_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v_mulFn_500_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 7, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_id_502_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_type_503_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_u_504_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_ringInst_505_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v_semiringInst_506_);
lean_ctor_set(v_reuseFailAlloc_521_, 5, v_charInst_x3f_507_);
lean_ctor_set(v_reuseFailAlloc_521_, 6, v_addFn_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_521_, 7, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 8, v_subFn_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_521_, 9, v_negFn_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_521_, 10, v_powFn_x3f_511_);
lean_ctor_set(v_reuseFailAlloc_521_, 11, v_intCastFn_x3f_512_);
lean_ctor_set(v_reuseFailAlloc_521_, 12, v_natCastFn_x3f_513_);
lean_ctor_set(v_reuseFailAlloc_521_, 13, v_one_x3f_514_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object* v_toPure_524_, lean_object* v_mulFn_525_, lean_object* v_____r_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_apply_2(v_toPure_524_, lean_box(0), v_mulFn_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object* v_toPure_528_, lean_object* v_modifyRing_529_, lean_object* v_toBind_530_, lean_object* v_mulFn_531_){
_start:
{
lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
lean_inc_ref(v_mulFn_531_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_532_, 0, v_mulFn_531_);
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_533_, 0, v_toPure_528_);
lean_closure_set(v___f_533_, 1, v_mulFn_531_);
v___x_534_ = lean_apply_1(v_modifyRing_529_, v___f_532_);
v___x_535_ = lean_apply_4(v_toBind_530_, lean_box(0), lean_box(0), v___x_534_, v___f_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object* v_toPure_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_toBind_557_, lean_object* v___f_558_, lean_object* v_ring_559_){
_start:
{
lean_object* v_mulFn_x3f_560_; 
v_mulFn_x3f_560_ = lean_ctor_get(v_ring_559_, 7);
if (lean_obj_tag(v_mulFn_x3f_560_) == 1)
{
lean_object* v_val_561_; lean_object* v___x_562_; 
lean_inc_ref(v_mulFn_x3f_560_);
lean_dec_ref(v_ring_559_);
lean_dec(v___f_558_);
lean_dec(v_toBind_557_);
lean_dec_ref(v_inst_556_);
lean_dec_ref(v_inst_555_);
lean_dec_ref(v_inst_554_);
lean_dec(v_inst_553_);
v_val_561_ = lean_ctor_get(v_mulFn_x3f_560_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v_mulFn_x3f_560_, 1);
v___x_562_ = lean_apply_2(v_toPure_552_, lean_box(0), v_val_561_);
return v___x_562_;
}
else
{
lean_object* v_type_563_; lean_object* v_u_564_; lean_object* v_semiringInst_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_expectedInst_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_toPure_552_);
v_type_563_ = lean_ctor_get(v_ring_559_, 1);
lean_inc_ref_n(v_type_563_, 3);
v_u_564_ = lean_ctor_get(v_ring_559_, 2);
lean_inc_n(v_u_564_, 2);
v_semiringInst_565_ = lean_ctor_get(v_ring_559_, 4);
lean_inc_ref(v_semiringInst_565_);
lean_dec_ref(v_ring_559_);
v___x_566_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_568_, 0, v_u_564_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
lean_inc_ref(v___x_568_);
v___x_569_ = l_Lean_mkConst(v___x_566_, v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_571_ = l_Lean_mkConst(v___x_570_, v___x_568_);
v___x_572_ = l_Lean_mkAppB(v___x_571_, v_type_563_, v_semiringInst_565_);
v_expectedInst_573_ = l_Lean_mkAppB(v___x_569_, v_type_563_, v___x_572_);
v___x_574_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_575_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_576_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_553_, v_inst_554_, v_inst_555_, v_inst_556_, v_type_563_, v_u_564_, v___x_574_, v___x_575_, v_expectedInst_573_);
v___x_577_ = lean_apply_4(v_toBind_557_, lean_box(0), lean_box(0), v___x_576_, v___f_558_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_){
_start:
{
lean_object* v_toApplicative_583_; lean_object* v_toBind_584_; lean_object* v_getRing_585_; lean_object* v_modifyRing_586_; lean_object* v_toPure_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___x_590_; 
v_toApplicative_583_ = lean_ctor_get(v_inst_580_, 0);
v_toBind_584_ = lean_ctor_get(v_inst_580_, 1);
lean_inc_n(v_toBind_584_, 3);
v_getRing_585_ = lean_ctor_get(v_inst_582_, 0);
lean_inc(v_getRing_585_);
v_modifyRing_586_ = lean_ctor_get(v_inst_582_, 1);
lean_inc(v_modifyRing_586_);
lean_dec_ref(v_inst_582_);
v_toPure_587_ = lean_ctor_get(v_toApplicative_583_, 1);
lean_inc_n(v_toPure_587_, 2);
v___f_588_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_588_, 0, v_toPure_587_);
lean_closure_set(v___f_588_, 1, v_modifyRing_586_);
lean_closure_set(v___f_588_, 2, v_toBind_584_);
v___f_589_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_589_, 0, v_toPure_587_);
lean_closure_set(v___f_589_, 1, v_inst_578_);
lean_closure_set(v___f_589_, 2, v_inst_579_);
lean_closure_set(v___f_589_, 3, v_inst_580_);
lean_closure_set(v___f_589_, 4, v_inst_581_);
lean_closure_set(v___f_589_, 5, v_toBind_584_);
lean_closure_set(v___f_589_, 6, v___f_588_);
v___x_590_ = lean_apply_4(v_toBind_584_, lean_box(0), lean_box(0), v_getRing_585_, v___f_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object* v_m_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_inst_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object* v_subFn_598_, lean_object* v_s_599_){
_start:
{
lean_object* v_id_600_; lean_object* v_type_601_; lean_object* v_u_602_; lean_object* v_ringInst_603_; lean_object* v_semiringInst_604_; lean_object* v_charInst_x3f_605_; lean_object* v_addFn_x3f_606_; lean_object* v_mulFn_x3f_607_; lean_object* v_negFn_x3f_608_; lean_object* v_powFn_x3f_609_; lean_object* v_intCastFn_x3f_610_; lean_object* v_natCastFn_x3f_611_; lean_object* v_one_x3f_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
v_id_600_ = lean_ctor_get(v_s_599_, 0);
v_type_601_ = lean_ctor_get(v_s_599_, 1);
v_u_602_ = lean_ctor_get(v_s_599_, 2);
v_ringInst_603_ = lean_ctor_get(v_s_599_, 3);
v_semiringInst_604_ = lean_ctor_get(v_s_599_, 4);
v_charInst_x3f_605_ = lean_ctor_get(v_s_599_, 5);
v_addFn_x3f_606_ = lean_ctor_get(v_s_599_, 6);
v_mulFn_x3f_607_ = lean_ctor_get(v_s_599_, 7);
v_negFn_x3f_608_ = lean_ctor_get(v_s_599_, 9);
v_powFn_x3f_609_ = lean_ctor_get(v_s_599_, 10);
v_intCastFn_x3f_610_ = lean_ctor_get(v_s_599_, 11);
v_natCastFn_x3f_611_ = lean_ctor_get(v_s_599_, 12);
v_one_x3f_612_ = lean_ctor_get(v_s_599_, 13);
v_isSharedCheck_620_ = !lean_is_exclusive(v_s_599_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_s_599_, 8);
lean_dec(v_unused_621_);
v___x_614_ = v_s_599_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_one_x3f_612_);
lean_inc(v_natCastFn_x3f_611_);
lean_inc(v_intCastFn_x3f_610_);
lean_inc(v_powFn_x3f_609_);
lean_inc(v_negFn_x3f_608_);
lean_inc(v_mulFn_x3f_607_);
lean_inc(v_addFn_x3f_606_);
lean_inc(v_charInst_x3f_605_);
lean_inc(v_semiringInst_604_);
lean_inc(v_ringInst_603_);
lean_inc(v_u_602_);
lean_inc(v_type_601_);
lean_inc(v_id_600_);
lean_dec(v_s_599_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_subFn_598_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 8, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_id_600_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_type_601_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_u_602_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_ringInst_603_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_semiringInst_604_);
lean_ctor_set(v_reuseFailAlloc_619_, 5, v_charInst_x3f_605_);
lean_ctor_set(v_reuseFailAlloc_619_, 6, v_addFn_x3f_606_);
lean_ctor_set(v_reuseFailAlloc_619_, 7, v_mulFn_x3f_607_);
lean_ctor_set(v_reuseFailAlloc_619_, 8, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 9, v_negFn_x3f_608_);
lean_ctor_set(v_reuseFailAlloc_619_, 10, v_powFn_x3f_609_);
lean_ctor_set(v_reuseFailAlloc_619_, 11, v_intCastFn_x3f_610_);
lean_ctor_set(v_reuseFailAlloc_619_, 12, v_natCastFn_x3f_611_);
lean_ctor_set(v_reuseFailAlloc_619_, 13, v_one_x3f_612_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_622_, lean_object* v_subFn_623_, lean_object* v_____r_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_apply_2(v_toPure_622_, lean_box(0), v_subFn_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_626_, lean_object* v_modifyRing_627_, lean_object* v_toBind_628_, lean_object* v_subFn_629_){
_start:
{
lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_inc_ref(v_subFn_629_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_630_, 0, v_subFn_629_);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_631_, 0, v_toPure_626_);
lean_closure_set(v___f_631_, 1, v_subFn_629_);
v___x_632_ = lean_apply_1(v_modifyRing_627_, v___f_630_);
v___x_633_ = lean_apply_4(v_toBind_628_, lean_box(0), lean_box(0), v___x_632_, v___f_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_toBind_656_, lean_object* v___f_657_, lean_object* v_ring_658_){
_start:
{
lean_object* v_subFn_x3f_659_; 
v_subFn_x3f_659_ = lean_ctor_get(v_ring_658_, 8);
if (lean_obj_tag(v_subFn_x3f_659_) == 1)
{
lean_object* v_val_660_; lean_object* v___x_661_; 
lean_inc_ref(v_subFn_x3f_659_);
lean_dec_ref(v_ring_658_);
lean_dec(v___f_657_);
lean_dec(v_toBind_656_);
lean_dec_ref(v_inst_655_);
lean_dec_ref(v_inst_654_);
lean_dec_ref(v_inst_653_);
lean_dec(v_inst_652_);
v_val_660_ = lean_ctor_get(v_subFn_x3f_659_, 0);
lean_inc(v_val_660_);
lean_dec_ref_known(v_subFn_x3f_659_, 1);
v___x_661_ = lean_apply_2(v_toPure_651_, lean_box(0), v_val_660_);
return v___x_661_;
}
else
{
lean_object* v_type_662_; lean_object* v_u_663_; lean_object* v_ringInst_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_expectedInst_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_toPure_651_);
v_type_662_ = lean_ctor_get(v_ring_658_, 1);
lean_inc_ref_n(v_type_662_, 3);
v_u_663_ = lean_ctor_get(v_ring_658_, 2);
lean_inc_n(v_u_663_, 2);
v_ringInst_664_ = lean_ctor_get(v_ring_658_, 3);
lean_inc_ref(v_ringInst_664_);
lean_dec_ref(v_ring_658_);
v___x_665_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v_u_663_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc_ref(v___x_667_);
v___x_668_ = l_Lean_mkConst(v___x_665_, v___x_667_);
v___x_669_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4));
v___x_670_ = l_Lean_mkConst(v___x_669_, v___x_667_);
v___x_671_ = l_Lean_mkAppB(v___x_670_, v_type_662_, v_ringInst_664_);
v_expectedInst_672_ = l_Lean_mkAppB(v___x_668_, v_type_662_, v___x_671_);
v___x_673_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6));
v___x_674_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8));
v___x_675_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_652_, v_inst_653_, v_inst_654_, v_inst_655_, v_type_662_, v_u_663_, v___x_673_, v___x_674_, v_expectedInst_672_);
v___x_676_ = lean_apply_4(v_toBind_656_, lean_box(0), lean_box(0), v___x_675_, v___f_657_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_){
_start:
{
lean_object* v_toApplicative_682_; lean_object* v_toBind_683_; lean_object* v_getRing_684_; lean_object* v_modifyRing_685_; lean_object* v_toPure_686_; lean_object* v___f_687_; lean_object* v___f_688_; lean_object* v___x_689_; 
v_toApplicative_682_ = lean_ctor_get(v_inst_679_, 0);
v_toBind_683_ = lean_ctor_get(v_inst_679_, 1);
lean_inc_n(v_toBind_683_, 3);
v_getRing_684_ = lean_ctor_get(v_inst_681_, 0);
lean_inc(v_getRing_684_);
v_modifyRing_685_ = lean_ctor_get(v_inst_681_, 1);
lean_inc(v_modifyRing_685_);
lean_dec_ref(v_inst_681_);
v_toPure_686_ = lean_ctor_get(v_toApplicative_682_, 1);
lean_inc_n(v_toPure_686_, 2);
v___f_687_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_687_, 0, v_toPure_686_);
lean_closure_set(v___f_687_, 1, v_modifyRing_685_);
lean_closure_set(v___f_687_, 2, v_toBind_683_);
v___f_688_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_688_, 0, v_toPure_686_);
lean_closure_set(v___f_688_, 1, v_inst_677_);
lean_closure_set(v___f_688_, 2, v_inst_678_);
lean_closure_set(v___f_688_, 3, v_inst_679_);
lean_closure_set(v___f_688_, 4, v_inst_680_);
lean_closure_set(v___f_688_, 5, v_toBind_683_);
lean_closure_set(v___f_688_, 6, v___f_687_);
v___x_689_ = lean_apply_4(v_toBind_683_, lean_box(0), lean_box(0), v_getRing_684_, v___f_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_inst_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_691_, v_inst_692_, v_inst_693_, v_inst_694_, v_inst_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_697_, lean_object* v_s_698_){
_start:
{
lean_object* v_id_699_; lean_object* v_type_700_; lean_object* v_u_701_; lean_object* v_ringInst_702_; lean_object* v_semiringInst_703_; lean_object* v_charInst_x3f_704_; lean_object* v_addFn_x3f_705_; lean_object* v_mulFn_x3f_706_; lean_object* v_subFn_x3f_707_; lean_object* v_powFn_x3f_708_; lean_object* v_intCastFn_x3f_709_; lean_object* v_natCastFn_x3f_710_; lean_object* v_one_x3f_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_719_; 
v_id_699_ = lean_ctor_get(v_s_698_, 0);
v_type_700_ = lean_ctor_get(v_s_698_, 1);
v_u_701_ = lean_ctor_get(v_s_698_, 2);
v_ringInst_702_ = lean_ctor_get(v_s_698_, 3);
v_semiringInst_703_ = lean_ctor_get(v_s_698_, 4);
v_charInst_x3f_704_ = lean_ctor_get(v_s_698_, 5);
v_addFn_x3f_705_ = lean_ctor_get(v_s_698_, 6);
v_mulFn_x3f_706_ = lean_ctor_get(v_s_698_, 7);
v_subFn_x3f_707_ = lean_ctor_get(v_s_698_, 8);
v_powFn_x3f_708_ = lean_ctor_get(v_s_698_, 10);
v_intCastFn_x3f_709_ = lean_ctor_get(v_s_698_, 11);
v_natCastFn_x3f_710_ = lean_ctor_get(v_s_698_, 12);
v_one_x3f_711_ = lean_ctor_get(v_s_698_, 13);
v_isSharedCheck_719_ = !lean_is_exclusive(v_s_698_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v_s_698_, 9);
lean_dec(v_unused_720_);
v___x_713_ = v_s_698_;
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_one_x3f_711_);
lean_inc(v_natCastFn_x3f_710_);
lean_inc(v_intCastFn_x3f_709_);
lean_inc(v_powFn_x3f_708_);
lean_inc(v_subFn_x3f_707_);
lean_inc(v_mulFn_x3f_706_);
lean_inc(v_addFn_x3f_705_);
lean_inc(v_charInst_x3f_704_);
lean_inc(v_semiringInst_703_);
lean_inc(v_ringInst_702_);
lean_inc(v_u_701_);
lean_inc(v_type_700_);
lean_inc(v_id_699_);
lean_dec(v_s_698_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v_negFn_697_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 9, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_id_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_type_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_u_701_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_ringInst_702_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_semiringInst_703_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v_charInst_x3f_704_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v_addFn_x3f_705_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_mulFn_x3f_706_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_subFn_x3f_707_);
lean_ctor_set(v_reuseFailAlloc_718_, 9, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_718_, 10, v_powFn_x3f_708_);
lean_ctor_set(v_reuseFailAlloc_718_, 11, v_intCastFn_x3f_709_);
lean_ctor_set(v_reuseFailAlloc_718_, 12, v_natCastFn_x3f_710_);
lean_ctor_set(v_reuseFailAlloc_718_, 13, v_one_x3f_711_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_721_, lean_object* v_negFn_722_, lean_object* v_____r_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_apply_2(v_toPure_721_, lean_box(0), v_negFn_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_725_, lean_object* v_modifyRing_726_, lean_object* v_toBind_727_, lean_object* v_negFn_728_){
_start:
{
lean_object* v___f_729_; lean_object* v___f_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_inc_ref(v_negFn_728_);
v___f_729_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_729_, 0, v_negFn_728_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_730_, 0, v_toPure_725_);
lean_closure_set(v___f_730_, 1, v_negFn_728_);
v___x_731_ = lean_apply_1(v_modifyRing_726_, v___f_729_);
v___x_732_ = lean_apply_4(v_toBind_727_, lean_box(0), lean_box(0), v___x_731_, v___f_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_toBind_751_, lean_object* v___f_752_, lean_object* v_ring_753_){
_start:
{
lean_object* v_negFn_x3f_754_; 
v_negFn_x3f_754_ = lean_ctor_get(v_ring_753_, 9);
if (lean_obj_tag(v_negFn_x3f_754_) == 1)
{
lean_object* v_val_755_; lean_object* v___x_756_; 
lean_inc_ref(v_negFn_x3f_754_);
lean_dec_ref(v_ring_753_);
lean_dec(v___f_752_);
lean_dec(v_toBind_751_);
lean_dec_ref(v_inst_750_);
lean_dec_ref(v_inst_749_);
lean_dec_ref(v_inst_748_);
lean_dec(v_inst_747_);
v_val_755_ = lean_ctor_get(v_negFn_x3f_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v_negFn_x3f_754_, 1);
v___x_756_ = lean_apply_2(v_toPure_746_, lean_box(0), v_val_755_);
return v___x_756_;
}
else
{
lean_object* v_type_757_; lean_object* v_u_758_; lean_object* v_ringInst_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_expectedInst_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_toPure_746_);
v_type_757_ = lean_ctor_get(v_ring_753_, 1);
lean_inc_ref_n(v_type_757_, 2);
v_u_758_ = lean_ctor_get(v_ring_753_, 2);
lean_inc_n(v_u_758_, 2);
v_ringInst_759_ = lean_ctor_get(v_ring_753_, 3);
lean_inc_ref(v_ringInst_759_);
lean_dec_ref(v_ring_753_);
v___x_760_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_761_ = lean_box(0);
v___x_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_762_, 0, v_u_758_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_mkConst(v___x_760_, v___x_762_);
v_expectedInst_764_ = l_Lean_mkAppB(v___x_763_, v_type_757_, v_ringInst_759_);
v___x_765_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_766_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_767_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_747_, v_inst_748_, v_inst_749_, v_inst_750_, v_type_757_, v_u_758_, v___x_765_, v___x_766_, v_expectedInst_764_);
v___x_768_ = lean_apply_4(v_toBind_751_, lean_box(0), lean_box(0), v___x_767_, v___f_752_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_inst_773_){
_start:
{
lean_object* v_toApplicative_774_; lean_object* v_toBind_775_; lean_object* v_getRing_776_; lean_object* v_modifyRing_777_; lean_object* v_toPure_778_; lean_object* v___f_779_; lean_object* v___f_780_; lean_object* v___x_781_; 
v_toApplicative_774_ = lean_ctor_get(v_inst_771_, 0);
v_toBind_775_ = lean_ctor_get(v_inst_771_, 1);
lean_inc_n(v_toBind_775_, 3);
v_getRing_776_ = lean_ctor_get(v_inst_773_, 0);
lean_inc(v_getRing_776_);
v_modifyRing_777_ = lean_ctor_get(v_inst_773_, 1);
lean_inc(v_modifyRing_777_);
lean_dec_ref(v_inst_773_);
v_toPure_778_ = lean_ctor_get(v_toApplicative_774_, 1);
lean_inc_n(v_toPure_778_, 2);
v___f_779_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_779_, 0, v_toPure_778_);
lean_closure_set(v___f_779_, 1, v_modifyRing_777_);
lean_closure_set(v___f_779_, 2, v_toBind_775_);
v___f_780_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_780_, 0, v_toPure_778_);
lean_closure_set(v___f_780_, 1, v_inst_769_);
lean_closure_set(v___f_780_, 2, v_inst_770_);
lean_closure_set(v___f_780_, 3, v_inst_771_);
lean_closure_set(v___f_780_, 4, v_inst_772_);
lean_closure_set(v___f_780_, 5, v_toBind_775_);
lean_closure_set(v___f_780_, 6, v___f_779_);
v___x_781_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v_getRing_776_, v___f_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_inst_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_783_, v_inst_784_, v_inst_785_, v_inst_786_, v_inst_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_789_, lean_object* v_s_790_){
_start:
{
lean_object* v_id_791_; lean_object* v_type_792_; lean_object* v_u_793_; lean_object* v_ringInst_794_; lean_object* v_semiringInst_795_; lean_object* v_charInst_x3f_796_; lean_object* v_addFn_x3f_797_; lean_object* v_mulFn_x3f_798_; lean_object* v_subFn_x3f_799_; lean_object* v_negFn_x3f_800_; lean_object* v_intCastFn_x3f_801_; lean_object* v_natCastFn_x3f_802_; lean_object* v_one_x3f_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
v_id_791_ = lean_ctor_get(v_s_790_, 0);
v_type_792_ = lean_ctor_get(v_s_790_, 1);
v_u_793_ = lean_ctor_get(v_s_790_, 2);
v_ringInst_794_ = lean_ctor_get(v_s_790_, 3);
v_semiringInst_795_ = lean_ctor_get(v_s_790_, 4);
v_charInst_x3f_796_ = lean_ctor_get(v_s_790_, 5);
v_addFn_x3f_797_ = lean_ctor_get(v_s_790_, 6);
v_mulFn_x3f_798_ = lean_ctor_get(v_s_790_, 7);
v_subFn_x3f_799_ = lean_ctor_get(v_s_790_, 8);
v_negFn_x3f_800_ = lean_ctor_get(v_s_790_, 9);
v_intCastFn_x3f_801_ = lean_ctor_get(v_s_790_, 11);
v_natCastFn_x3f_802_ = lean_ctor_get(v_s_790_, 12);
v_one_x3f_803_ = lean_ctor_get(v_s_790_, 13);
v_isSharedCheck_811_ = !lean_is_exclusive(v_s_790_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v_s_790_, 10);
lean_dec(v_unused_812_);
v___x_805_ = v_s_790_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_one_x3f_803_);
lean_inc(v_natCastFn_x3f_802_);
lean_inc(v_intCastFn_x3f_801_);
lean_inc(v_negFn_x3f_800_);
lean_inc(v_subFn_x3f_799_);
lean_inc(v_mulFn_x3f_798_);
lean_inc(v_addFn_x3f_797_);
lean_inc(v_charInst_x3f_796_);
lean_inc(v_semiringInst_795_);
lean_inc(v_ringInst_794_);
lean_inc(v_u_793_);
lean_inc(v_type_792_);
lean_inc(v_id_791_);
lean_dec(v_s_790_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v_powFn_789_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 10, v___x_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_id_791_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_type_792_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_u_793_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_ringInst_794_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_semiringInst_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 5, v_charInst_x3f_796_);
lean_ctor_set(v_reuseFailAlloc_810_, 6, v_addFn_x3f_797_);
lean_ctor_set(v_reuseFailAlloc_810_, 7, v_mulFn_x3f_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 8, v_subFn_x3f_799_);
lean_ctor_set(v_reuseFailAlloc_810_, 9, v_negFn_x3f_800_);
lean_ctor_set(v_reuseFailAlloc_810_, 10, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_810_, 11, v_intCastFn_x3f_801_);
lean_ctor_set(v_reuseFailAlloc_810_, 12, v_natCastFn_x3f_802_);
lean_ctor_set(v_reuseFailAlloc_810_, 13, v_one_x3f_803_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_813_, lean_object* v_powFn_814_, lean_object* v_____r_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = lean_apply_2(v_toPure_813_, lean_box(0), v_powFn_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_817_, lean_object* v_modifyRing_818_, lean_object* v_toBind_819_, lean_object* v_powFn_820_){
_start:
{
lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc_ref(v_powFn_820_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_821_, 0, v_powFn_820_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_822_, 0, v_toPure_817_);
lean_closure_set(v___f_822_, 1, v_powFn_820_);
v___x_823_ = lean_apply_1(v_modifyRing_818_, v___f_821_);
v___x_824_ = lean_apply_4(v_toBind_819_, lean_box(0), lean_box(0), v___x_823_, v___f_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_toBind_830_, lean_object* v___f_831_, lean_object* v_ring_832_){
_start:
{
lean_object* v_powFn_x3f_833_; 
v_powFn_x3f_833_ = lean_ctor_get(v_ring_832_, 10);
if (lean_obj_tag(v_powFn_x3f_833_) == 1)
{
lean_object* v_val_834_; lean_object* v___x_835_; 
lean_inc_ref(v_powFn_x3f_833_);
lean_dec_ref(v_ring_832_);
lean_dec(v___f_831_);
lean_dec(v_toBind_830_);
lean_dec_ref(v_inst_829_);
lean_dec_ref(v_inst_828_);
lean_dec_ref(v_inst_827_);
lean_dec(v_inst_826_);
v_val_834_ = lean_ctor_get(v_powFn_x3f_833_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v_powFn_x3f_833_, 1);
v___x_835_ = lean_apply_2(v_toPure_825_, lean_box(0), v_val_834_);
return v___x_835_;
}
else
{
lean_object* v_type_836_; lean_object* v_u_837_; lean_object* v_semiringInst_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v_toPure_825_);
v_type_836_ = lean_ctor_get(v_ring_832_, 1);
lean_inc_ref(v_type_836_);
v_u_837_ = lean_ctor_get(v_ring_832_, 2);
lean_inc(v_u_837_);
v_semiringInst_838_ = lean_ctor_get(v_ring_832_, 4);
lean_inc_ref(v_semiringInst_838_);
lean_dec_ref(v_ring_832_);
v___x_839_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_826_, v_inst_827_, v_inst_828_, v_inst_829_, v_u_837_, v_type_836_, v_semiringInst_838_);
v___x_840_ = lean_apply_4(v_toBind_830_, lean_box(0), lean_box(0), v___x_839_, v___f_831_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_){
_start:
{
lean_object* v_toApplicative_846_; lean_object* v_toBind_847_; lean_object* v_getRing_848_; lean_object* v_modifyRing_849_; lean_object* v_toPure_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___x_853_; 
v_toApplicative_846_ = lean_ctor_get(v_inst_843_, 0);
v_toBind_847_ = lean_ctor_get(v_inst_843_, 1);
lean_inc_n(v_toBind_847_, 3);
v_getRing_848_ = lean_ctor_get(v_inst_845_, 0);
lean_inc(v_getRing_848_);
v_modifyRing_849_ = lean_ctor_get(v_inst_845_, 1);
lean_inc(v_modifyRing_849_);
lean_dec_ref(v_inst_845_);
v_toPure_850_ = lean_ctor_get(v_toApplicative_846_, 1);
lean_inc_n(v_toPure_850_, 2);
v___f_851_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_851_, 0, v_toPure_850_);
lean_closure_set(v___f_851_, 1, v_modifyRing_849_);
lean_closure_set(v___f_851_, 2, v_toBind_847_);
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_852_, 0, v_toPure_850_);
lean_closure_set(v___f_852_, 1, v_inst_841_);
lean_closure_set(v___f_852_, 2, v_inst_842_);
lean_closure_set(v___f_852_, 3, v_inst_843_);
lean_closure_set(v___f_852_, 4, v_inst_844_);
lean_closure_set(v___f_852_, 5, v_toBind_847_);
lean_closure_set(v___f_852_, 6, v___f_851_);
v___x_853_ = lean_apply_4(v_toBind_847_, lean_box(0), lean_box(0), v_getRing_848_, v___f_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_inst_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_855_, v_inst_856_, v_inst_857_, v_inst_858_, v_inst_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_861_, lean_object* v_s_862_){
_start:
{
lean_object* v_id_863_; lean_object* v_type_864_; lean_object* v_u_865_; lean_object* v_ringInst_866_; lean_object* v_semiringInst_867_; lean_object* v_charInst_x3f_868_; lean_object* v_addFn_x3f_869_; lean_object* v_mulFn_x3f_870_; lean_object* v_subFn_x3f_871_; lean_object* v_negFn_x3f_872_; lean_object* v_powFn_x3f_873_; lean_object* v_natCastFn_x3f_874_; lean_object* v_one_x3f_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_id_863_ = lean_ctor_get(v_s_862_, 0);
v_type_864_ = lean_ctor_get(v_s_862_, 1);
v_u_865_ = lean_ctor_get(v_s_862_, 2);
v_ringInst_866_ = lean_ctor_get(v_s_862_, 3);
v_semiringInst_867_ = lean_ctor_get(v_s_862_, 4);
v_charInst_x3f_868_ = lean_ctor_get(v_s_862_, 5);
v_addFn_x3f_869_ = lean_ctor_get(v_s_862_, 6);
v_mulFn_x3f_870_ = lean_ctor_get(v_s_862_, 7);
v_subFn_x3f_871_ = lean_ctor_get(v_s_862_, 8);
v_negFn_x3f_872_ = lean_ctor_get(v_s_862_, 9);
v_powFn_x3f_873_ = lean_ctor_get(v_s_862_, 10);
v_natCastFn_x3f_874_ = lean_ctor_get(v_s_862_, 12);
v_one_x3f_875_ = lean_ctor_get(v_s_862_, 13);
v_isSharedCheck_883_ = !lean_is_exclusive(v_s_862_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v_s_862_, 11);
lean_dec(v_unused_884_);
v___x_877_ = v_s_862_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_one_x3f_875_);
lean_inc(v_natCastFn_x3f_874_);
lean_inc(v_powFn_x3f_873_);
lean_inc(v_negFn_x3f_872_);
lean_inc(v_subFn_x3f_871_);
lean_inc(v_mulFn_x3f_870_);
lean_inc(v_addFn_x3f_869_);
lean_inc(v_charInst_x3f_868_);
lean_inc(v_semiringInst_867_);
lean_inc(v_ringInst_866_);
lean_inc(v_u_865_);
lean_inc(v_type_864_);
lean_inc(v_id_863_);
lean_dec(v_s_862_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v_intCastFn_861_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 11, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_id_863_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_type_864_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_u_865_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_ringInst_866_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_semiringInst_867_);
lean_ctor_set(v_reuseFailAlloc_882_, 5, v_charInst_x3f_868_);
lean_ctor_set(v_reuseFailAlloc_882_, 6, v_addFn_x3f_869_);
lean_ctor_set(v_reuseFailAlloc_882_, 7, v_mulFn_x3f_870_);
lean_ctor_set(v_reuseFailAlloc_882_, 8, v_subFn_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_882_, 9, v_negFn_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_882_, 10, v_powFn_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_882_, 11, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_882_, 12, v_natCastFn_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_882_, 13, v_one_x3f_875_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_885_, lean_object* v_intCastFn_886_, lean_object* v_____r_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_apply_2(v_toPure_885_, lean_box(0), v_intCastFn_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_889_, lean_object* v_modifyRing_890_, lean_object* v_toBind_891_, lean_object* v_intCastFn_892_){
_start:
{
lean_object* v___f_893_; lean_object* v___f_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_inc_ref(v_intCastFn_892_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_893_, 0, v_intCastFn_892_);
v___f_894_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_894_, 0, v_toPure_889_);
lean_closure_set(v___f_894_, 1, v_intCastFn_892_);
v___x_895_ = lean_apply_1(v_modifyRing_890_, v___f_893_);
v___x_896_ = lean_apply_4(v_toBind_891_, lean_box(0), lean_box(0), v___x_895_, v___f_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v___x_899_, lean_object* v_type_900_, lean_object* v_canonExpr_901_, lean_object* v_toBind_902_, lean_object* v___f_903_, lean_object* v_inst_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_905_ = l_Lean_Name_mkStr2(v___x_897_, v___x_898_);
v___x_906_ = l_Lean_mkConst(v___x_905_, v___x_899_);
v___x_907_ = l_Lean_mkAppB(v___x_906_, v_type_900_, v_inst_904_);
v___x_908_ = lean_apply_1(v_canonExpr_901_, v___x_907_);
v___x_909_ = lean_apply_4(v_toBind_902_, lean_box(0), lean_box(0), v___x_908_, v___f_903_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_915_, lean_object* v_inst_x27_916_, lean_object* v_toBind_917_, lean_object* v___f_918_, lean_object* v___f_919_, lean_object* v_inst_920_, lean_object* v_____do__lift_921_){
_start:
{
if (lean_obj_tag(v_____do__lift_921_) == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec(v_inst_920_);
lean_dec(v___f_919_);
v___x_922_ = lean_apply_2(v_toPure_915_, lean_box(0), v_inst_x27_916_);
v___x_923_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v___x_922_, v___f_918_);
return v___x_923_;
}
else
{
lean_object* v_val_924_; lean_object* v___f_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec(v___f_918_);
v_val_924_ = lean_ctor_get(v_____do__lift_921_, 0);
lean_inc_n(v_val_924_, 2);
lean_dec_ref_known(v_____do__lift_921_, 1);
lean_inc(v_toBind_917_);
v___f_925_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_925_, 0, v_toPure_915_);
lean_closure_set(v___f_925_, 1, v_val_924_);
lean_closure_set(v___f_925_, 2, v_toBind_917_);
lean_closure_set(v___f_925_, 3, v___f_919_);
v___x_926_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_927_, 0, v___x_926_);
lean_closure_set(v___x_927_, 1, v_val_924_);
lean_closure_set(v___x_927_, 2, v_inst_x27_916_);
v___x_928_ = lean_apply_2(v_inst_920_, lean_box(0), v___x_927_);
v___x_929_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v___x_928_, v___f_925_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_939_, lean_object* v_inst_940_, lean_object* v_toBind_941_, lean_object* v___f_942_, lean_object* v_inst_943_, lean_object* v_ring_944_){
_start:
{
lean_object* v_intCastFn_x3f_945_; 
v_intCastFn_x3f_945_ = lean_ctor_get(v_ring_944_, 11);
if (lean_obj_tag(v_intCastFn_x3f_945_) == 1)
{
lean_object* v_val_946_; lean_object* v___x_947_; 
lean_inc_ref(v_intCastFn_x3f_945_);
lean_dec_ref(v_ring_944_);
lean_dec(v_inst_943_);
lean_dec(v___f_942_);
lean_dec(v_toBind_941_);
lean_dec_ref(v_inst_940_);
v_val_946_ = lean_ctor_get(v_intCastFn_x3f_945_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v_intCastFn_x3f_945_, 1);
v___x_947_ = lean_apply_2(v_toPure_939_, lean_box(0), v_val_946_);
return v___x_947_;
}
else
{
lean_object* v_type_948_; lean_object* v_u_949_; lean_object* v_ringInst_950_; lean_object* v_canonExpr_951_; lean_object* v_synthInstance_x3f_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_973_; 
v_type_948_ = lean_ctor_get(v_ring_944_, 1);
lean_inc_ref(v_type_948_);
v_u_949_ = lean_ctor_get(v_ring_944_, 2);
lean_inc(v_u_949_);
v_ringInst_950_ = lean_ctor_get(v_ring_944_, 3);
lean_inc_ref(v_ringInst_950_);
lean_dec_ref(v_ring_944_);
v_canonExpr_951_ = lean_ctor_get(v_inst_940_, 0);
v_synthInstance_x3f_952_ = lean_ctor_get(v_inst_940_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_inst_940_);
if (v_isSharedCheck_973_ == 0)
{
v___x_954_ = v_inst_940_;
v_isShared_955_ = v_isSharedCheck_973_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_synthInstance_x3f_952_);
lean_inc(v_canonExpr_951_);
lean_dec(v_inst_940_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_973_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_956_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_957_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_958_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 1);
lean_ctor_set(v___x_954_, 1, v___x_958_);
lean_ctor_set(v___x_954_, 0, v_u_949_);
v___x_960_ = v___x_954_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_u_949_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_972_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v_inst_x27_962_; lean_object* v___x_963_; lean_object* v___f_964_; lean_object* v___f_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_instType_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_inc_ref_n(v___x_960_, 2);
v___x_961_ = l_Lean_mkConst(v___x_957_, v___x_960_);
lean_inc_ref_n(v_type_948_, 2);
v_inst_x27_962_ = l_Lean_mkAppB(v___x_961_, v_type_948_, v_ringInst_950_);
v___x_963_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_941_, 2);
v___f_964_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_964_, 0, v___x_963_);
lean_closure_set(v___f_964_, 1, v___x_956_);
lean_closure_set(v___f_964_, 2, v___x_960_);
lean_closure_set(v___f_964_, 3, v_type_948_);
lean_closure_set(v___f_964_, 4, v_canonExpr_951_);
lean_closure_set(v___f_964_, 5, v_toBind_941_);
lean_closure_set(v___f_964_, 6, v___f_942_);
v___f_965_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_965_, 0, v___f_964_);
lean_inc_ref(v___f_965_);
v___f_966_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_966_, 0, v_toPure_939_);
lean_closure_set(v___f_966_, 1, v_inst_x27_962_);
lean_closure_set(v___f_966_, 2, v_toBind_941_);
lean_closure_set(v___f_966_, 3, v___f_965_);
lean_closure_set(v___f_966_, 4, v___f_965_);
lean_closure_set(v___f_966_, 5, v_inst_943_);
v___x_967_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_968_ = l_Lean_mkConst(v___x_967_, v___x_960_);
v_instType_969_ = l_Lean_Expr_app___override(v___x_968_, v_type_948_);
v___x_970_ = lean_apply_1(v_synthInstance_x3f_952_, v_instType_969_);
v___x_971_ = lean_apply_4(v_toBind_941_, lean_box(0), lean_box(0), v___x_970_, v___f_966_);
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_inst_977_){
_start:
{
lean_object* v_toApplicative_978_; lean_object* v_toBind_979_; lean_object* v_getRing_980_; lean_object* v_modifyRing_981_; lean_object* v_toPure_982_; lean_object* v___f_983_; lean_object* v___f_984_; lean_object* v___x_985_; 
v_toApplicative_978_ = lean_ctor_get(v_inst_975_, 0);
lean_inc_ref(v_toApplicative_978_);
v_toBind_979_ = lean_ctor_get(v_inst_975_, 1);
lean_inc_n(v_toBind_979_, 3);
lean_dec_ref(v_inst_975_);
v_getRing_980_ = lean_ctor_get(v_inst_977_, 0);
lean_inc(v_getRing_980_);
v_modifyRing_981_ = lean_ctor_get(v_inst_977_, 1);
lean_inc(v_modifyRing_981_);
lean_dec_ref(v_inst_977_);
v_toPure_982_ = lean_ctor_get(v_toApplicative_978_, 1);
lean_inc_n(v_toPure_982_, 2);
lean_dec_ref(v_toApplicative_978_);
v___f_983_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_983_, 0, v_toPure_982_);
lean_closure_set(v___f_983_, 1, v_modifyRing_981_);
lean_closure_set(v___f_983_, 2, v_toBind_979_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_984_, 0, v_toPure_982_);
lean_closure_set(v___f_984_, 1, v_inst_976_);
lean_closure_set(v___f_984_, 2, v_toBind_979_);
lean_closure_set(v___f_984_, 3, v___f_983_);
lean_closure_set(v___f_984_, 4, v_inst_974_);
v___x_985_ = lean_apply_4(v_toBind_979_, lean_box(0), lean_box(0), v_getRing_980_, v___f_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_986_, lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_inst_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_987_, v_inst_988_, v_inst_989_, v_inst_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_992_, lean_object* v_s_993_){
_start:
{
lean_object* v_id_994_; lean_object* v_type_995_; lean_object* v_u_996_; lean_object* v_ringInst_997_; lean_object* v_semiringInst_998_; lean_object* v_charInst_x3f_999_; lean_object* v_addFn_x3f_1000_; lean_object* v_mulFn_x3f_1001_; lean_object* v_subFn_x3f_1002_; lean_object* v_negFn_x3f_1003_; lean_object* v_powFn_x3f_1004_; lean_object* v_intCastFn_x3f_1005_; lean_object* v_one_x3f_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1014_; 
v_id_994_ = lean_ctor_get(v_s_993_, 0);
v_type_995_ = lean_ctor_get(v_s_993_, 1);
v_u_996_ = lean_ctor_get(v_s_993_, 2);
v_ringInst_997_ = lean_ctor_get(v_s_993_, 3);
v_semiringInst_998_ = lean_ctor_get(v_s_993_, 4);
v_charInst_x3f_999_ = lean_ctor_get(v_s_993_, 5);
v_addFn_x3f_1000_ = lean_ctor_get(v_s_993_, 6);
v_mulFn_x3f_1001_ = lean_ctor_get(v_s_993_, 7);
v_subFn_x3f_1002_ = lean_ctor_get(v_s_993_, 8);
v_negFn_x3f_1003_ = lean_ctor_get(v_s_993_, 9);
v_powFn_x3f_1004_ = lean_ctor_get(v_s_993_, 10);
v_intCastFn_x3f_1005_ = lean_ctor_get(v_s_993_, 11);
v_one_x3f_1006_ = lean_ctor_get(v_s_993_, 13);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_s_993_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v_s_993_, 12);
lean_dec(v_unused_1015_);
v___x_1008_ = v_s_993_;
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_one_x3f_1006_);
lean_inc(v_intCastFn_x3f_1005_);
lean_inc(v_powFn_x3f_1004_);
lean_inc(v_negFn_x3f_1003_);
lean_inc(v_subFn_x3f_1002_);
lean_inc(v_mulFn_x3f_1001_);
lean_inc(v_addFn_x3f_1000_);
lean_inc(v_charInst_x3f_999_);
lean_inc(v_semiringInst_998_);
lean_inc(v_ringInst_997_);
lean_inc(v_u_996_);
lean_inc(v_type_995_);
lean_inc(v_id_994_);
lean_dec(v_s_993_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_natCastFn_992_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 12, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_id_994_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_type_995_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_u_996_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_ringInst_997_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_semiringInst_998_);
lean_ctor_set(v_reuseFailAlloc_1013_, 5, v_charInst_x3f_999_);
lean_ctor_set(v_reuseFailAlloc_1013_, 6, v_addFn_x3f_1000_);
lean_ctor_set(v_reuseFailAlloc_1013_, 7, v_mulFn_x3f_1001_);
lean_ctor_set(v_reuseFailAlloc_1013_, 8, v_subFn_x3f_1002_);
lean_ctor_set(v_reuseFailAlloc_1013_, 9, v_negFn_x3f_1003_);
lean_ctor_set(v_reuseFailAlloc_1013_, 10, v_powFn_x3f_1004_);
lean_ctor_set(v_reuseFailAlloc_1013_, 11, v_intCastFn_x3f_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 12, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1013_, 13, v_one_x3f_1006_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1016_, lean_object* v_natCastFn_1017_, lean_object* v_____r_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_apply_2(v_toPure_1016_, lean_box(0), v_natCastFn_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1020_, lean_object* v_modifyRing_1021_, lean_object* v_toBind_1022_, lean_object* v_natCastFn_1023_){
_start:
{
lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_inc_ref(v_natCastFn_1023_);
v___f_1024_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1024_, 0, v_natCastFn_1023_);
v___f_1025_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1025_, 0, v_toPure_1020_);
lean_closure_set(v___f_1025_, 1, v_natCastFn_1023_);
v___x_1026_ = lean_apply_1(v_modifyRing_1021_, v___f_1024_);
v___x_1027_ = lean_apply_4(v_toBind_1022_, lean_box(0), lean_box(0), v___x_1026_, v___f_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_toBind_1032_, lean_object* v___f_1033_, lean_object* v_ring_1034_){
_start:
{
lean_object* v_natCastFn_x3f_1035_; 
v_natCastFn_x3f_1035_ = lean_ctor_get(v_ring_1034_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1035_) == 1)
{
lean_object* v_val_1036_; lean_object* v___x_1037_; 
lean_inc_ref(v_natCastFn_x3f_1035_);
lean_dec_ref(v_ring_1034_);
lean_dec(v___f_1033_);
lean_dec(v_toBind_1032_);
lean_dec_ref(v_inst_1031_);
lean_dec_ref(v_inst_1030_);
lean_dec(v_inst_1029_);
v_val_1036_ = lean_ctor_get(v_natCastFn_x3f_1035_, 0);
lean_inc(v_val_1036_);
lean_dec_ref_known(v_natCastFn_x3f_1035_, 1);
v___x_1037_ = lean_apply_2(v_toPure_1028_, lean_box(0), v_val_1036_);
return v___x_1037_;
}
else
{
lean_object* v_type_1038_; lean_object* v_u_1039_; lean_object* v_semiringInst_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v_toPure_1028_);
v_type_1038_ = lean_ctor_get(v_ring_1034_, 1);
lean_inc_ref(v_type_1038_);
v_u_1039_ = lean_ctor_get(v_ring_1034_, 2);
lean_inc(v_u_1039_);
v_semiringInst_1040_ = lean_ctor_get(v_ring_1034_, 4);
lean_inc_ref(v_semiringInst_1040_);
lean_dec_ref(v_ring_1034_);
v___x_1041_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1029_, v_inst_1030_, v_inst_1031_, v_u_1039_, v_type_1038_, v_semiringInst_1040_);
v___x_1042_ = lean_apply_4(v_toBind_1032_, lean_box(0), lean_box(0), v___x_1041_, v___f_1033_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_inst_1046_){
_start:
{
lean_object* v_toApplicative_1047_; lean_object* v_toBind_1048_; lean_object* v_getRing_1049_; lean_object* v_modifyRing_1050_; lean_object* v_toPure_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; 
v_toApplicative_1047_ = lean_ctor_get(v_inst_1044_, 0);
v_toBind_1048_ = lean_ctor_get(v_inst_1044_, 1);
lean_inc_n(v_toBind_1048_, 3);
v_getRing_1049_ = lean_ctor_get(v_inst_1046_, 0);
lean_inc(v_getRing_1049_);
v_modifyRing_1050_ = lean_ctor_get(v_inst_1046_, 1);
lean_inc(v_modifyRing_1050_);
lean_dec_ref(v_inst_1046_);
v_toPure_1051_ = lean_ctor_get(v_toApplicative_1047_, 1);
lean_inc_n(v_toPure_1051_, 2);
v___f_1052_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1052_, 0, v_toPure_1051_);
lean_closure_set(v___f_1052_, 1, v_modifyRing_1050_);
lean_closure_set(v___f_1052_, 2, v_toBind_1048_);
v___f_1053_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1053_, 0, v_toPure_1051_);
lean_closure_set(v___f_1053_, 1, v_inst_1043_);
lean_closure_set(v___f_1053_, 2, v_inst_1044_);
lean_closure_set(v___f_1053_, 3, v_inst_1045_);
lean_closure_set(v___f_1053_, 4, v_toBind_1048_);
lean_closure_set(v___f_1053_, 5, v___f_1052_);
v___x_1054_ = lean_apply_4(v_toBind_1048_, lean_box(0), lean_box(0), v_getRing_1049_, v___f_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1056_, v_inst_1057_, v_inst_1058_, v_inst_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1061_, lean_object* v_s_1062_){
_start:
{
lean_object* v_toRing_1063_; lean_object* v_semiringId_x3f_1064_; lean_object* v_commSemiringInst_1065_; lean_object* v_commRingInst_1066_; lean_object* v_noZeroDivInst_x3f_1067_; lean_object* v_fieldInst_x3f_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1076_; 
v_toRing_1063_ = lean_ctor_get(v_s_1062_, 0);
v_semiringId_x3f_1064_ = lean_ctor_get(v_s_1062_, 2);
v_commSemiringInst_1065_ = lean_ctor_get(v_s_1062_, 3);
v_commRingInst_1066_ = lean_ctor_get(v_s_1062_, 4);
v_noZeroDivInst_x3f_1067_ = lean_ctor_get(v_s_1062_, 5);
v_fieldInst_x3f_1068_ = lean_ctor_get(v_s_1062_, 6);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_s_1062_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_s_1062_, 1);
lean_dec(v_unused_1077_);
v___x_1070_ = v_s_1062_;
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_fieldInst_x3f_1068_);
lean_inc(v_noZeroDivInst_x3f_1067_);
lean_inc(v_commRingInst_1066_);
lean_inc(v_commSemiringInst_1065_);
lean_inc(v_semiringId_x3f_1064_);
lean_inc(v_toRing_1063_);
lean_dec(v_s_1062_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_invFn_1061_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_toRing_1063_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_semiringId_x3f_1064_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_commSemiringInst_1065_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_commRingInst_1066_);
lean_ctor_set(v_reuseFailAlloc_1075_, 5, v_noZeroDivInst_x3f_1067_);
lean_ctor_set(v_reuseFailAlloc_1075_, 6, v_fieldInst_x3f_1068_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1078_, lean_object* v_invFn_1079_, lean_object* v_____r_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_apply_2(v_toPure_1078_, lean_box(0), v_invFn_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1082_, lean_object* v_modifyCommRing_1083_, lean_object* v_toBind_1084_, lean_object* v_invFn_1085_){
_start:
{
lean_object* v___f_1086_; lean_object* v___f_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_inc_ref(v_invFn_1085_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1086_, 0, v_invFn_1085_);
v___f_1087_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1087_, 0, v_toPure_1082_);
lean_closure_set(v___f_1087_, 1, v_invFn_1085_);
v___x_1088_ = lean_apply_1(v_modifyCommRing_1083_, v___f_1086_);
v___x_1089_ = lean_apply_4(v_toBind_1084_, lean_box(0), lean_box(0), v___x_1088_, v___f_1087_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_toBind_1112_, lean_object* v___f_1113_, lean_object* v_ring_1114_){
_start:
{
lean_object* v_fieldInst_x3f_1115_; 
v_fieldInst_x3f_1115_ = lean_ctor_get(v_ring_1114_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1115_) == 1)
{
lean_object* v_invFn_x3f_1116_; 
lean_inc_ref(v_fieldInst_x3f_1115_);
v_invFn_x3f_1116_ = lean_ctor_get(v_ring_1114_, 1);
if (lean_obj_tag(v_invFn_x3f_1116_) == 1)
{
lean_object* v_val_1117_; lean_object* v___x_1118_; 
lean_inc_ref(v_invFn_x3f_1116_);
lean_dec_ref_known(v_fieldInst_x3f_1115_, 1);
lean_dec_ref(v_ring_1114_);
lean_dec(v___f_1113_);
lean_dec(v_toBind_1112_);
lean_dec_ref(v_inst_1111_);
lean_dec_ref(v_inst_1110_);
lean_dec_ref(v_inst_1109_);
lean_dec(v_inst_1108_);
v_val_1117_ = lean_ctor_get(v_invFn_x3f_1116_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v_invFn_x3f_1116_, 1);
v___x_1118_ = lean_apply_2(v_toPure_1107_, lean_box(0), v_val_1117_);
return v___x_1118_;
}
else
{
lean_object* v_toRing_1119_; lean_object* v_val_1120_; lean_object* v_type_1121_; lean_object* v_u_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_expectedInst_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_toPure_1107_);
v_toRing_1119_ = lean_ctor_get(v_ring_1114_, 0);
lean_inc_ref(v_toRing_1119_);
lean_dec_ref(v_ring_1114_);
v_val_1120_ = lean_ctor_get(v_fieldInst_x3f_1115_, 0);
lean_inc(v_val_1120_);
lean_dec_ref_known(v_fieldInst_x3f_1115_, 1);
v_type_1121_ = lean_ctor_get(v_toRing_1119_, 1);
lean_inc_ref_n(v_type_1121_, 2);
v_u_1122_ = lean_ctor_get(v_toRing_1119_, 2);
lean_inc_n(v_u_1122_, 2);
lean_dec_ref(v_toRing_1119_);
v___x_1123_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_u_1122_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_mkConst(v___x_1123_, v___x_1125_);
v_expectedInst_1127_ = l_Lean_mkAppB(v___x_1126_, v_type_1121_, v_val_1120_);
v___x_1128_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1129_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1130_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1108_, v_inst_1109_, v_inst_1110_, v_inst_1111_, v_type_1121_, v_u_1122_, v___x_1128_, v___x_1129_, v_expectedInst_1127_);
v___x_1131_ = lean_apply_4(v_toBind_1112_, lean_box(0), lean_box(0), v___x_1130_, v___f_1113_);
return v___x_1131_;
}
}
else
{
lean_object* v_toRing_1132_; lean_object* v_type_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v___f_1113_);
lean_dec(v_toBind_1112_);
lean_dec_ref(v_inst_1111_);
lean_dec(v_inst_1108_);
lean_dec(v_toPure_1107_);
v_toRing_1132_ = lean_ctor_get(v_ring_1114_, 0);
lean_inc_ref(v_toRing_1132_);
lean_dec_ref(v_ring_1114_);
v_type_1133_ = lean_ctor_get(v_toRing_1132_, 1);
lean_inc_ref(v_type_1133_);
lean_dec_ref(v_toRing_1132_);
v___x_1134_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1135_ = l_Lean_indentExpr(v_type_1133_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_throwError___redArg(v_inst_1110_, v_inst_1109_, v___x_1136_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_){
_start:
{
lean_object* v_toApplicative_1143_; lean_object* v_toBind_1144_; lean_object* v_getCommRing_1145_; lean_object* v_modifyCommRing_1146_; lean_object* v_toPure_1147_; lean_object* v___f_1148_; lean_object* v___f_1149_; lean_object* v___x_1150_; 
v_toApplicative_1143_ = lean_ctor_get(v_inst_1140_, 0);
v_toBind_1144_ = lean_ctor_get(v_inst_1140_, 1);
lean_inc_n(v_toBind_1144_, 3);
v_getCommRing_1145_ = lean_ctor_get(v_inst_1142_, 0);
lean_inc(v_getCommRing_1145_);
v_modifyCommRing_1146_ = lean_ctor_get(v_inst_1142_, 1);
lean_inc(v_modifyCommRing_1146_);
lean_dec_ref(v_inst_1142_);
v_toPure_1147_ = lean_ctor_get(v_toApplicative_1143_, 1);
lean_inc_n(v_toPure_1147_, 2);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1148_, 0, v_toPure_1147_);
lean_closure_set(v___f_1148_, 1, v_modifyCommRing_1146_);
lean_closure_set(v___f_1148_, 2, v_toBind_1144_);
v___f_1149_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1149_, 0, v_toPure_1147_);
lean_closure_set(v___f_1149_, 1, v_inst_1138_);
lean_closure_set(v___f_1149_, 2, v_inst_1139_);
lean_closure_set(v___f_1149_, 3, v_inst_1140_);
lean_closure_set(v___f_1149_, 4, v_inst_1141_);
lean_closure_set(v___f_1149_, 5, v_toBind_1144_);
lean_closure_set(v___f_1149_, 6, v___f_1148_);
v___x_1150_ = lean_apply_4(v_toBind_1144_, lean_box(0), lean_box(0), v_getCommRing_1145_, v___f_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1152_, v_inst_1153_, v_inst_1154_, v_inst_1155_, v_inst_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_1158_, lean_object* v_s_1159_){
_start:
{
lean_object* v_id_1160_; lean_object* v_type_1161_; lean_object* v_u_1162_; lean_object* v_semiringInst_1163_; lean_object* v_mulFn_x3f_1164_; lean_object* v_powFn_x3f_1165_; lean_object* v_natCastFn_x3f_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
v_id_1160_ = lean_ctor_get(v_s_1159_, 0);
v_type_1161_ = lean_ctor_get(v_s_1159_, 1);
v_u_1162_ = lean_ctor_get(v_s_1159_, 2);
v_semiringInst_1163_ = lean_ctor_get(v_s_1159_, 3);
v_mulFn_x3f_1164_ = lean_ctor_get(v_s_1159_, 5);
v_powFn_x3f_1165_ = lean_ctor_get(v_s_1159_, 6);
v_natCastFn_x3f_1166_ = lean_ctor_get(v_s_1159_, 7);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_s_1159_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_s_1159_, 4);
lean_dec(v_unused_1175_);
v___x_1168_ = v_s_1159_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_natCastFn_x3f_1166_);
lean_inc(v_powFn_x3f_1165_);
lean_inc(v_mulFn_x3f_1164_);
lean_inc(v_semiringInst_1163_);
lean_inc(v_u_1162_);
lean_inc(v_type_1161_);
lean_inc(v_id_1160_);
lean_dec(v_s_1159_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_addFn_1158_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 4, v___x_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_id_1160_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_type_1161_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_u_1162_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_semiringInst_1163_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1173_, 5, v_mulFn_x3f_1164_);
lean_ctor_set(v_reuseFailAlloc_1173_, 6, v_powFn_x3f_1165_);
lean_ctor_set(v_reuseFailAlloc_1173_, 7, v_natCastFn_x3f_1166_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_1176_, lean_object* v_modifySemiring_1177_, lean_object* v_toBind_1178_, lean_object* v_addFn_1179_){
_start:
{
lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_inc_ref(v_addFn_1179_);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1180_, 0, v_addFn_1179_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1181_, 0, v_toPure_1176_);
lean_closure_set(v___f_1181_, 1, v_addFn_1179_);
v___x_1182_ = lean_apply_1(v_modifySemiring_1177_, v___f_1180_);
v___x_1183_ = lean_apply_4(v_toBind_1178_, lean_box(0), lean_box(0), v___x_1182_, v___f_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_toBind_1189_, lean_object* v___f_1190_, lean_object* v_sr_1191_){
_start:
{
lean_object* v_addFn_x3f_1192_; 
v_addFn_x3f_1192_ = lean_ctor_get(v_sr_1191_, 4);
if (lean_obj_tag(v_addFn_x3f_1192_) == 1)
{
lean_object* v_val_1193_; lean_object* v___x_1194_; 
lean_inc_ref(v_addFn_x3f_1192_);
lean_dec_ref(v_sr_1191_);
lean_dec(v___f_1190_);
lean_dec(v_toBind_1189_);
lean_dec_ref(v_inst_1188_);
lean_dec_ref(v_inst_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec(v_inst_1185_);
v_val_1193_ = lean_ctor_get(v_addFn_x3f_1192_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v_addFn_x3f_1192_, 1);
v___x_1194_ = lean_apply_2(v_toPure_1184_, lean_box(0), v_val_1193_);
return v___x_1194_;
}
else
{
lean_object* v_type_1195_; lean_object* v_u_1196_; lean_object* v_semiringInst_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_expectedInst_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_toPure_1184_);
v_type_1195_ = lean_ctor_get(v_sr_1191_, 1);
lean_inc_ref_n(v_type_1195_, 3);
v_u_1196_ = lean_ctor_get(v_sr_1191_, 2);
lean_inc_n(v_u_1196_, 2);
v_semiringInst_1197_ = lean_ctor_get(v_sr_1191_, 3);
lean_inc_ref(v_semiringInst_1197_);
lean_dec_ref(v_sr_1191_);
v___x_1198_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1200_, 0, v_u_1196_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
lean_inc_ref(v___x_1200_);
v___x_1201_ = l_Lean_mkConst(v___x_1198_, v___x_1200_);
v___x_1202_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1203_ = l_Lean_mkConst(v___x_1202_, v___x_1200_);
v___x_1204_ = l_Lean_mkAppB(v___x_1203_, v_type_1195_, v_semiringInst_1197_);
v_expectedInst_1205_ = l_Lean_mkAppB(v___x_1201_, v_type_1195_, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1207_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1208_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1185_, v_inst_1186_, v_inst_1187_, v_inst_1188_, v_type_1195_, v_u_1196_, v___x_1206_, v___x_1207_, v_expectedInst_1205_);
v___x_1209_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1208_, v___f_1190_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_){
_start:
{
lean_object* v_toApplicative_1215_; lean_object* v_toBind_1216_; lean_object* v_getSemiring_1217_; lean_object* v_modifySemiring_1218_; lean_object* v_toPure_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___x_1222_; 
v_toApplicative_1215_ = lean_ctor_get(v_inst_1212_, 0);
v_toBind_1216_ = lean_ctor_get(v_inst_1212_, 1);
lean_inc_n(v_toBind_1216_, 3);
v_getSemiring_1217_ = lean_ctor_get(v_inst_1214_, 0);
lean_inc(v_getSemiring_1217_);
v_modifySemiring_1218_ = lean_ctor_get(v_inst_1214_, 1);
lean_inc(v_modifySemiring_1218_);
lean_dec_ref(v_inst_1214_);
v_toPure_1219_ = lean_ctor_get(v_toApplicative_1215_, 1);
lean_inc_n(v_toPure_1219_, 2);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1220_, 0, v_toPure_1219_);
lean_closure_set(v___f_1220_, 1, v_modifySemiring_1218_);
lean_closure_set(v___f_1220_, 2, v_toBind_1216_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1221_, 0, v_toPure_1219_);
lean_closure_set(v___f_1221_, 1, v_inst_1210_);
lean_closure_set(v___f_1221_, 2, v_inst_1211_);
lean_closure_set(v___f_1221_, 3, v_inst_1212_);
lean_closure_set(v___f_1221_, 4, v_inst_1213_);
lean_closure_set(v___f_1221_, 5, v_toBind_1216_);
lean_closure_set(v___f_1221_, 6, v___f_1220_);
v___x_1222_ = lean_apply_4(v_toBind_1216_, lean_box(0), lean_box(0), v_getSemiring_1217_, v___f_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1224_, v_inst_1225_, v_inst_1226_, v_inst_1227_, v_inst_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_1230_, lean_object* v_s_1231_){
_start:
{
lean_object* v_id_1232_; lean_object* v_type_1233_; lean_object* v_u_1234_; lean_object* v_semiringInst_1235_; lean_object* v_addFn_x3f_1236_; lean_object* v_powFn_x3f_1237_; lean_object* v_natCastFn_x3f_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1246_; 
v_id_1232_ = lean_ctor_get(v_s_1231_, 0);
v_type_1233_ = lean_ctor_get(v_s_1231_, 1);
v_u_1234_ = lean_ctor_get(v_s_1231_, 2);
v_semiringInst_1235_ = lean_ctor_get(v_s_1231_, 3);
v_addFn_x3f_1236_ = lean_ctor_get(v_s_1231_, 4);
v_powFn_x3f_1237_ = lean_ctor_get(v_s_1231_, 6);
v_natCastFn_x3f_1238_ = lean_ctor_get(v_s_1231_, 7);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_s_1231_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_s_1231_, 5);
lean_dec(v_unused_1247_);
v___x_1240_ = v_s_1231_;
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_natCastFn_x3f_1238_);
lean_inc(v_powFn_x3f_1237_);
lean_inc(v_addFn_x3f_1236_);
lean_inc(v_semiringInst_1235_);
lean_inc(v_u_1234_);
lean_inc(v_type_1233_);
lean_inc(v_id_1232_);
lean_dec(v_s_1231_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_mulFn_1230_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 5, v___x_1242_);
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_id_1232_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_type_1233_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_u_1234_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_semiringInst_1235_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_addFn_x3f_1236_);
lean_ctor_set(v_reuseFailAlloc_1245_, 5, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1245_, 6, v_powFn_x3f_1237_);
lean_ctor_set(v_reuseFailAlloc_1245_, 7, v_natCastFn_x3f_1238_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1248_, lean_object* v_modifySemiring_1249_, lean_object* v_toBind_1250_, lean_object* v_mulFn_1251_){
_start:
{
lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_inc_ref(v_mulFn_1251_);
v___f_1252_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1252_, 0, v_mulFn_1251_);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1253_, 0, v_toPure_1248_);
lean_closure_set(v___f_1253_, 1, v_mulFn_1251_);
v___x_1254_ = lean_apply_1(v_modifySemiring_1249_, v___f_1252_);
v___x_1255_ = lean_apply_4(v_toBind_1250_, lean_box(0), lean_box(0), v___x_1254_, v___f_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_toBind_1261_, lean_object* v___f_1262_, lean_object* v_sr_1263_){
_start:
{
lean_object* v_mulFn_x3f_1264_; 
v_mulFn_x3f_1264_ = lean_ctor_get(v_sr_1263_, 5);
if (lean_obj_tag(v_mulFn_x3f_1264_) == 1)
{
lean_object* v_val_1265_; lean_object* v___x_1266_; 
lean_inc_ref(v_mulFn_x3f_1264_);
lean_dec_ref(v_sr_1263_);
lean_dec(v___f_1262_);
lean_dec(v_toBind_1261_);
lean_dec_ref(v_inst_1260_);
lean_dec_ref(v_inst_1259_);
lean_dec_ref(v_inst_1258_);
lean_dec(v_inst_1257_);
v_val_1265_ = lean_ctor_get(v_mulFn_x3f_1264_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v_mulFn_x3f_1264_, 1);
v___x_1266_ = lean_apply_2(v_toPure_1256_, lean_box(0), v_val_1265_);
return v___x_1266_;
}
else
{
lean_object* v_type_1267_; lean_object* v_u_1268_; lean_object* v_semiringInst_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_expectedInst_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v_toPure_1256_);
v_type_1267_ = lean_ctor_get(v_sr_1263_, 1);
lean_inc_ref_n(v_type_1267_, 3);
v_u_1268_ = lean_ctor_get(v_sr_1263_, 2);
lean_inc_n(v_u_1268_, 2);
v_semiringInst_1269_ = lean_ctor_get(v_sr_1263_, 3);
lean_inc_ref(v_semiringInst_1269_);
lean_dec_ref(v_sr_1263_);
v___x_1270_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_u_1268_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
lean_inc_ref(v___x_1272_);
v___x_1273_ = l_Lean_mkConst(v___x_1270_, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1275_ = l_Lean_mkConst(v___x_1274_, v___x_1272_);
v___x_1276_ = l_Lean_mkAppB(v___x_1275_, v_type_1267_, v_semiringInst_1269_);
v_expectedInst_1277_ = l_Lean_mkAppB(v___x_1273_, v_type_1267_, v___x_1276_);
v___x_1278_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1279_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1280_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1257_, v_inst_1258_, v_inst_1259_, v_inst_1260_, v_type_1267_, v_u_1268_, v___x_1278_, v___x_1279_, v_expectedInst_1277_);
v___x_1281_ = lean_apply_4(v_toBind_1261_, lean_box(0), lean_box(0), v___x_1280_, v___f_1262_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_){
_start:
{
lean_object* v_toApplicative_1287_; lean_object* v_toBind_1288_; lean_object* v_getSemiring_1289_; lean_object* v_modifySemiring_1290_; lean_object* v_toPure_1291_; lean_object* v___f_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; 
v_toApplicative_1287_ = lean_ctor_get(v_inst_1284_, 0);
v_toBind_1288_ = lean_ctor_get(v_inst_1284_, 1);
lean_inc_n(v_toBind_1288_, 3);
v_getSemiring_1289_ = lean_ctor_get(v_inst_1286_, 0);
lean_inc(v_getSemiring_1289_);
v_modifySemiring_1290_ = lean_ctor_get(v_inst_1286_, 1);
lean_inc(v_modifySemiring_1290_);
lean_dec_ref(v_inst_1286_);
v_toPure_1291_ = lean_ctor_get(v_toApplicative_1287_, 1);
lean_inc_n(v_toPure_1291_, 2);
v___f_1292_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1292_, 0, v_toPure_1291_);
lean_closure_set(v___f_1292_, 1, v_modifySemiring_1290_);
lean_closure_set(v___f_1292_, 2, v_toBind_1288_);
v___f_1293_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1293_, 0, v_toPure_1291_);
lean_closure_set(v___f_1293_, 1, v_inst_1282_);
lean_closure_set(v___f_1293_, 2, v_inst_1283_);
lean_closure_set(v___f_1293_, 3, v_inst_1284_);
lean_closure_set(v___f_1293_, 4, v_inst_1285_);
lean_closure_set(v___f_1293_, 5, v_toBind_1288_);
lean_closure_set(v___f_1293_, 6, v___f_1292_);
v___x_1294_ = lean_apply_4(v_toBind_1288_, lean_box(0), lean_box(0), v_getSemiring_1289_, v___f_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1296_, v_inst_1297_, v_inst_1298_, v_inst_1299_, v_inst_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1302_, lean_object* v_s_1303_){
_start:
{
lean_object* v_id_1304_; lean_object* v_type_1305_; lean_object* v_u_1306_; lean_object* v_semiringInst_1307_; lean_object* v_addFn_x3f_1308_; lean_object* v_mulFn_x3f_1309_; lean_object* v_natCastFn_x3f_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
v_id_1304_ = lean_ctor_get(v_s_1303_, 0);
v_type_1305_ = lean_ctor_get(v_s_1303_, 1);
v_u_1306_ = lean_ctor_get(v_s_1303_, 2);
v_semiringInst_1307_ = lean_ctor_get(v_s_1303_, 3);
v_addFn_x3f_1308_ = lean_ctor_get(v_s_1303_, 4);
v_mulFn_x3f_1309_ = lean_ctor_get(v_s_1303_, 5);
v_natCastFn_x3f_1310_ = lean_ctor_get(v_s_1303_, 7);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_s_1303_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v_s_1303_, 6);
lean_dec(v_unused_1319_);
v___x_1312_ = v_s_1303_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_natCastFn_x3f_1310_);
lean_inc(v_mulFn_x3f_1309_);
lean_inc(v_addFn_x3f_1308_);
lean_inc(v_semiringInst_1307_);
lean_inc(v_u_1306_);
lean_inc(v_type_1305_);
lean_inc(v_id_1304_);
lean_dec(v_s_1303_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_powFn_1302_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 6, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_id_1304_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_type_1305_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_u_1306_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_semiringInst_1307_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v_addFn_x3f_1308_);
lean_ctor_set(v_reuseFailAlloc_1317_, 5, v_mulFn_x3f_1309_);
lean_ctor_set(v_reuseFailAlloc_1317_, 6, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1317_, 7, v_natCastFn_x3f_1310_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1320_, lean_object* v_modifySemiring_1321_, lean_object* v_toBind_1322_, lean_object* v_powFn_1323_){
_start:
{
lean_object* v___f_1324_; lean_object* v___f_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_inc_ref(v_powFn_1323_);
v___f_1324_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1324_, 0, v_powFn_1323_);
v___f_1325_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1325_, 0, v_toPure_1320_);
lean_closure_set(v___f_1325_, 1, v_powFn_1323_);
v___x_1326_ = lean_apply_1(v_modifySemiring_1321_, v___f_1324_);
v___x_1327_ = lean_apply_4(v_toBind_1322_, lean_box(0), lean_box(0), v___x_1326_, v___f_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_toBind_1333_, lean_object* v___f_1334_, lean_object* v_sr_1335_){
_start:
{
lean_object* v_powFn_x3f_1336_; 
v_powFn_x3f_1336_ = lean_ctor_get(v_sr_1335_, 6);
if (lean_obj_tag(v_powFn_x3f_1336_) == 1)
{
lean_object* v_val_1337_; lean_object* v___x_1338_; 
lean_inc_ref(v_powFn_x3f_1336_);
lean_dec_ref(v_sr_1335_);
lean_dec(v___f_1334_);
lean_dec(v_toBind_1333_);
lean_dec_ref(v_inst_1332_);
lean_dec_ref(v_inst_1331_);
lean_dec_ref(v_inst_1330_);
lean_dec(v_inst_1329_);
v_val_1337_ = lean_ctor_get(v_powFn_x3f_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v_powFn_x3f_1336_, 1);
v___x_1338_ = lean_apply_2(v_toPure_1328_, lean_box(0), v_val_1337_);
return v___x_1338_;
}
else
{
lean_object* v_type_1339_; lean_object* v_u_1340_; lean_object* v_semiringInst_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_toPure_1328_);
v_type_1339_ = lean_ctor_get(v_sr_1335_, 1);
lean_inc_ref(v_type_1339_);
v_u_1340_ = lean_ctor_get(v_sr_1335_, 2);
lean_inc(v_u_1340_);
v_semiringInst_1341_ = lean_ctor_get(v_sr_1335_, 3);
lean_inc_ref(v_semiringInst_1341_);
lean_dec_ref(v_sr_1335_);
v___x_1342_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1329_, v_inst_1330_, v_inst_1331_, v_inst_1332_, v_u_1340_, v_type_1339_, v_semiringInst_1341_);
v___x_1343_ = lean_apply_4(v_toBind_1333_, lean_box(0), lean_box(0), v___x_1342_, v___f_1334_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_){
_start:
{
lean_object* v_toApplicative_1349_; lean_object* v_toBind_1350_; lean_object* v_getSemiring_1351_; lean_object* v_modifySemiring_1352_; lean_object* v_toPure_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; 
v_toApplicative_1349_ = lean_ctor_get(v_inst_1346_, 0);
v_toBind_1350_ = lean_ctor_get(v_inst_1346_, 1);
lean_inc_n(v_toBind_1350_, 3);
v_getSemiring_1351_ = lean_ctor_get(v_inst_1348_, 0);
lean_inc(v_getSemiring_1351_);
v_modifySemiring_1352_ = lean_ctor_get(v_inst_1348_, 1);
lean_inc(v_modifySemiring_1352_);
lean_dec_ref(v_inst_1348_);
v_toPure_1353_ = lean_ctor_get(v_toApplicative_1349_, 1);
lean_inc_n(v_toPure_1353_, 2);
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1354_, 0, v_toPure_1353_);
lean_closure_set(v___f_1354_, 1, v_modifySemiring_1352_);
lean_closure_set(v___f_1354_, 2, v_toBind_1350_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1355_, 0, v_toPure_1353_);
lean_closure_set(v___f_1355_, 1, v_inst_1344_);
lean_closure_set(v___f_1355_, 2, v_inst_1345_);
lean_closure_set(v___f_1355_, 3, v_inst_1346_);
lean_closure_set(v___f_1355_, 4, v_inst_1347_);
lean_closure_set(v___f_1355_, 5, v_toBind_1350_);
lean_closure_set(v___f_1355_, 6, v___f_1354_);
v___x_1356_ = lean_apply_4(v_toBind_1350_, lean_box(0), lean_box(0), v_getSemiring_1351_, v___f_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1358_, v_inst_1359_, v_inst_1360_, v_inst_1361_, v_inst_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1364_, lean_object* v_s_1365_){
_start:
{
lean_object* v_id_1366_; lean_object* v_type_1367_; lean_object* v_u_1368_; lean_object* v_semiringInst_1369_; lean_object* v_addFn_x3f_1370_; lean_object* v_mulFn_x3f_1371_; lean_object* v_powFn_x3f_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1380_; 
v_id_1366_ = lean_ctor_get(v_s_1365_, 0);
v_type_1367_ = lean_ctor_get(v_s_1365_, 1);
v_u_1368_ = lean_ctor_get(v_s_1365_, 2);
v_semiringInst_1369_ = lean_ctor_get(v_s_1365_, 3);
v_addFn_x3f_1370_ = lean_ctor_get(v_s_1365_, 4);
v_mulFn_x3f_1371_ = lean_ctor_get(v_s_1365_, 5);
v_powFn_x3f_1372_ = lean_ctor_get(v_s_1365_, 6);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_s_1365_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v_s_1365_, 7);
lean_dec(v_unused_1381_);
v___x_1374_ = v_s_1365_;
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_powFn_x3f_1372_);
lean_inc(v_mulFn_x3f_1371_);
lean_inc(v_addFn_x3f_1370_);
lean_inc(v_semiringInst_1369_);
lean_inc(v_u_1368_);
lean_inc(v_type_1367_);
lean_inc(v_id_1366_);
lean_dec(v_s_1365_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_natCastFn_1364_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 7, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_id_1366_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_type_1367_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_u_1368_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_semiringInst_1369_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_addFn_x3f_1370_);
lean_ctor_set(v_reuseFailAlloc_1379_, 5, v_mulFn_x3f_1371_);
lean_ctor_set(v_reuseFailAlloc_1379_, 6, v_powFn_x3f_1372_);
lean_ctor_set(v_reuseFailAlloc_1379_, 7, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1382_, lean_object* v_modifySemiring_1383_, lean_object* v_toBind_1384_, lean_object* v_natCastFn_1385_){
_start:
{
lean_object* v___f_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_inc_ref(v_natCastFn_1385_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1386_, 0, v_natCastFn_1385_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1387_, 0, v_toPure_1382_);
lean_closure_set(v___f_1387_, 1, v_natCastFn_1385_);
v___x_1388_ = lean_apply_1(v_modifySemiring_1383_, v___f_1386_);
v___x_1389_ = lean_apply_4(v_toBind_1384_, lean_box(0), lean_box(0), v___x_1388_, v___f_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_toBind_1394_, lean_object* v___f_1395_, lean_object* v_sr_1396_){
_start:
{
lean_object* v_natCastFn_x3f_1397_; 
v_natCastFn_x3f_1397_ = lean_ctor_get(v_sr_1396_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1397_) == 1)
{
lean_object* v_val_1398_; lean_object* v___x_1399_; 
lean_inc_ref(v_natCastFn_x3f_1397_);
lean_dec_ref(v_sr_1396_);
lean_dec(v___f_1395_);
lean_dec(v_toBind_1394_);
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
lean_dec(v_inst_1391_);
v_val_1398_ = lean_ctor_get(v_natCastFn_x3f_1397_, 0);
lean_inc(v_val_1398_);
lean_dec_ref_known(v_natCastFn_x3f_1397_, 1);
v___x_1399_ = lean_apply_2(v_toPure_1390_, lean_box(0), v_val_1398_);
return v___x_1399_;
}
else
{
lean_object* v_type_1400_; lean_object* v_u_1401_; lean_object* v_semiringInst_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_toPure_1390_);
v_type_1400_ = lean_ctor_get(v_sr_1396_, 1);
lean_inc_ref(v_type_1400_);
v_u_1401_ = lean_ctor_get(v_sr_1396_, 2);
lean_inc(v_u_1401_);
v_semiringInst_1402_ = lean_ctor_get(v_sr_1396_, 3);
lean_inc_ref(v_semiringInst_1402_);
lean_dec_ref(v_sr_1396_);
v___x_1403_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1391_, v_inst_1392_, v_inst_1393_, v_u_1401_, v_type_1400_, v_semiringInst_1402_);
v___x_1404_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v___x_1403_, v___f_1395_);
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_){
_start:
{
lean_object* v_toApplicative_1409_; lean_object* v_toBind_1410_; lean_object* v_getSemiring_1411_; lean_object* v_modifySemiring_1412_; lean_object* v_toPure_1413_; lean_object* v___f_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; 
v_toApplicative_1409_ = lean_ctor_get(v_inst_1406_, 0);
v_toBind_1410_ = lean_ctor_get(v_inst_1406_, 1);
lean_inc_n(v_toBind_1410_, 3);
v_getSemiring_1411_ = lean_ctor_get(v_inst_1408_, 0);
lean_inc(v_getSemiring_1411_);
v_modifySemiring_1412_ = lean_ctor_get(v_inst_1408_, 1);
lean_inc(v_modifySemiring_1412_);
lean_dec_ref(v_inst_1408_);
v_toPure_1413_ = lean_ctor_get(v_toApplicative_1409_, 1);
lean_inc_n(v_toPure_1413_, 2);
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1414_, 0, v_toPure_1413_);
lean_closure_set(v___f_1414_, 1, v_modifySemiring_1412_);
lean_closure_set(v___f_1414_, 2, v_toBind_1410_);
v___f_1415_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1415_, 0, v_toPure_1413_);
lean_closure_set(v___f_1415_, 1, v_inst_1405_);
lean_closure_set(v___f_1415_, 2, v_inst_1406_);
lean_closure_set(v___f_1415_, 3, v_inst_1407_);
lean_closure_set(v___f_1415_, 4, v_toBind_1410_);
lean_closure_set(v___f_1415_, 5, v___f_1414_);
v___x_1416_ = lean_apply_4(v_toBind_1410_, lean_box(0), lean_box(0), v_getSemiring_1411_, v___f_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_inst_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1418_, v_inst_1419_, v_inst_1420_, v_inst_1421_);
return v___x_1422_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
